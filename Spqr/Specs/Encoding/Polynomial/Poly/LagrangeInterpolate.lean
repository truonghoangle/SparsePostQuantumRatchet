/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Polynomial.Poly.Clone
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolatePrepare
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateComplete
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateLoop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate`

Given a slice of evaluation points `pts : &[Pt]` with pairwise distinct x-coordinates, the Rust
function `Poly::lagrange_interpolate` (in `src/encoding/polynomial.rs`, lines 106:4-137:5) returns
the unique polynomial of degree `< pts.len()` over GF(2¹⁶) that interpolates the points: for every
index `i`, `result(pᵢ.x) = pᵢ.y`.

Concretely the Aeneas-extracted Lean function `encoding.polynomial.Poly.lagrange_interpolate`
proceeds as follows:

1. **Allocate**: `out = Poly::zero(pts.len())` — empty coefficient
   vector with the given capacity hint.
2. **Empty short-circuit**: if `pts.is_empty()`, return the zero
   polynomial immediately.
3. **Prepare template**: compute
     `template = ∏_{j=0}^{pts.len()−1} (X − pts[j].x)`
   via `Poly::lagrange_interpolate_prepare` (see
   `LagrangeInterpolatePrepare`).  The result has
   `coefficients.len() = pts.len() + 1` and a leading `GF16::ONE`.
4. **Clone template into `working`**: `working = template.clone()`.
5. **Unroll iteration `i = 0`**: call
   `working.lagrange_interpolate_complete(pts, 0)` to obtain
   `working₁` satisfying the algebraic identity
     `working₁ · (X − pts[0].x) =
        X · lagrangeScale(pts[0], pts) · template`
   in `GF216[X]` (see `LagrangeInterpolateComplete`).
6. **Initialise `out` from `working₁` shifted by one position**:
   `out.coefficients.extend_from_slice(&working₁.coefficients[1..])`,
   so after the extend `out.coefficients.len() = pts.len()`.  Reading
   from `working₁.coefficients[1..]` rather than from index `0` is the
   "divide by X" trick that strips the leading-zero coefficient
   artifact of `working₁` without a `memmove`.
7. **Outer loop** for `i = 1, …, pts.len() − 1`: each iteration
   re-loads `working` from `template`, calls
   `working.lagrange_interpolate_complete(pts, i)` to obtain
   `workingᵢ`, and XOR-adds `workingᵢ.coefficients[1..]` into
   `out.coefficients` via the inner loop
     `for j in 0..out.coefficients.len():
        out.coefficients[j] += workingᵢ.coefficients[j + 1]`
   (see `LagrangeInterpolateLoop0`).

After all `pts.len()` iterations the running interpolant `out` is
   `out = ∑_{i=0}^{pts.len()−1} workingᵢ / X`
where each `workingᵢ` is the polynomial produced by the `i`-th call to
`lagrange_interpolate_complete`, so each `workingᵢ` satisfies
   `workingᵢ · (X − pts[i].x) =
        X · lagrangeScale(pts[i], pts) · template`.
Dividing by `X` on both sides and summing over `i` recovers the
classical Lagrange interpolation formula
   `out(X) = ∑_i pᵢ.y · ∏_{j ≠ i} (X − pⱼ.x) / ∏_{j ≠ i} (pᵢ.x − pⱼ.x)`,
which is the unique polynomial of degree `< pts.len()` satisfying
`out(pᵢ.x) = pᵢ.y` for all `i`.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the 16-bit
encodings:
  `a + b = a − b = a ⊕ b`,
so the `+=` performed by the outer loop is the same as the in-place XOR-accumulation used by the
Rust `AddAssign` instance for `GF16`.

**Source**: spqr/src/encoding/polynomial.rs (lines 106:4-137:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly
open spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop
  (prodLinearFactors prodLinearFactors_eval_root
   prodLinearFactors_base prodLinearFactors_step prodLinearFactors_snoc)

namespace spqr.encoding.polynomial.Poly

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

instance : Inhabited spqr.encoding.polynomial.Pt where
  default := ⟨⟨0#u16⟩, ⟨0#u16⟩⟩

/--
`core.slice.Slice.is_empty pts` returns `true` iff the slice is empty.  This is a concrete (total)
operation extracted from the Aeneas standard library; it never panics.
-/
private lemma slice_is_empty_spec {T : Type} (s : Slice T) :
    core.slice.Slice.is_empty s ⦃ (b : Bool) =>
      b = (s.val.length = 0) ⦄ := by
  unfold core.slice.Slice.is_empty
  simp only [WP.spec_ok]
  rcases h : s.val.length with _ | n
  · simp [h]
  · simp [h]

/--
Stronger spec for `Poly.zero`: the resulting polynomial not only represents `0 ∈ GF216[X]` but also
has an empty coefficient vector (length `0`).  This is what is actually produced by the underlying
`Vec::with_capacity` call.
-/
private lemma zero_spec' (capacity : Std.Usize) :
    zero capacity ⦃ (result : Poly) =>
      result.coefficients.val.length = 0 ∧ result.toGF216Poly = 0 ⦄ := by
  unfold zero
  simp [alloc.vec.Vec.with_capacity, Poly.toGF216Poly,
    spqr.encoding.polynomial.listToGF216Poly]

/--
**Spec for `alloc.vec.Vec.extend_from_slice` specialised to `GF16`**:

The `core.clone.Clone` instance for `GF16` (`encoding.gf.GF16.Insts.CoreCloneClone`) has `clone x =
ok x` for every `x`, hence the elementwise `Slice.clone` on `s` returns `ok s` and the resulting
vector is exactly `v.val ++ s.val`.  The precondition `v.val.length + s.val.length ≤ Usize.max`
discharges the overflow guard in the body of `extend_from_slice`.
-/
private lemma extend_from_slice_GF16_spec
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (s : Slice spqr.encoding.gf.GF16)
    (h : v.val.length + s.val.length ≤ Std.Usize.max) :
    alloc.vec.Vec.extend_from_slice
        spqr.encoding.gf.GF16.Insts.CoreCloneClone v s
      ⦃ (r : alloc.vec.Vec spqr.encoding.gf.GF16) =>
        r.val = v.val ++ s.val ⦄ := by
  have h_clone_x :
      ∀ x ∈ s.val,
        spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone x = ok x := by
    intros _ _
    simp [spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone]
  have h_slclone :
      Slice.clone spqr.encoding.gf.GF16.Insts.CoreCloneClone.clone s = ok s := by
    obtain ⟨s', h_eq, hs⟩ := WP.spec_imp_exists (Slice.clone_spec h_clone_x)
    rw [h_eq, ← hs]
  unfold alloc.vec.Vec.extend_from_slice
  have hlen : v.length + s.length ≤ Std.Usize.max := h
  rw [dif_pos hlen]
  grind

/--
**Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate`**:

Given a slice of points `pts` with `pts.len() + 1 ≤ Usize.max`, the function returns a polynomial
`result : Poly` whose coefficient vector has exactly `pts.len()` entries and whose mathematical
content is the **Lagrange interpolant** of the points.

• The function always succeeds (no panic) under the precondition `pts.length + 1 ≤ Usize.max`,
  since `Poly::zero`, `is_empty`, `lagrange_interpolate_prepare`, the by-value `Clone` for `Poly`,
  `lagrange_interpolate_complete`, slice indexing with `RangeFrom`, `extend_from_slice`, and the
  outer loop driver `lagrange_interpolate_loop0` are all total under that assumption (the bound
  ensures the `pts.len() + 1` capacity hint passed to `Poly::zero` and the auxiliary index
  arithmetic do not overflow).

• **Length of the result**:
    `result.coefficients.val.length = pts.val.length`.
  In the empty case (`pts.length = 0`) this gives length `0`, and
  the function returns the zero polynomial directly.  In the
  non-empty case it follows from the initial
  `extend_from_slice(&working₁.coefficients[1..])` (which appends
  `pts.len()` coefficients to the empty `out`) together with the fact
  that the outer loop preserves the vector length (see
  `LagrangeInterpolateLoop0.loop_spec`).

• **Empty case**: when `pts` is empty,
    `result.toGF216Poly = 0`,
  i.e. the function returns the zero polynomial.  This is the unique
  interpolant of the empty point set.

• **Existence of per-iteration witness polynomials**: there exists a
  list `ws : List Poly` of length `pts.val.length`, collecting the
  scratch polynomials `workingᵢ` produced at each iteration
  `i ∈ {0, …, pts.len() − 1}`, such that:

    - **Polynomial identity** (one per iteration): for every
      `i < ws.length`,
        `ws[i].toGF216Poly · (X − C(pts[i].x.toGF216)) =
            X · C(lagrangeScaleGF216 pts[i] pts.val) ·
              prodLinearFactors pts.val 0 pts.val.length`
      in `GF216[X]`.  This is exactly the algebraic content produced by
      `lagrange_interpolate_complete` on the freshly-restored
      `working = template = ∏_j (X − pts[j].x)` at iteration `i`.

    - **Cumulative XOR-accumulation** of contributions: for every
      coefficient position `j < result.coefficients.val.length`,
        `result.coefficients[j].toGF216 =
            (ws.map (fun w =>
              w.coefficients[j + 1].toGF216)).sum`
      where the sum is over the witnesses `ws[0], …, ws[ws.length−1]`
      in `GF216 = GaloisField 2 16`.  In characteristic 2 this sum
      coincides with bitwise XOR of the 16-bit encodings, matching
      the Rust `+=` accumulation.  Reading at position `j + 1` is the
      "divide by `X`" trick that strips the leading-zero coefficient
      artifact of each `ws[i]` without an explicit shift.

**Interpolation property** (informal corollary).  Combining the two clauses above gives the
polynomial identity
   `X · result.toGF216Poly =
        ∑_i workingᵢ` (as polynomials over `GF216`),
and dividing through the per-iteration identity
   `workingᵢ · (X − pts[i].x) =
        X · lagrangeScale(pts[i], pts) · template`
by `(X − pts[i].x)` (which is valid since `template` is divisible by every `(X − pts[j].x)`) yields
   `result(X) = ∑_i pᵢ.y · ∏_{j ≠ i} (X − pⱼ.x) / ∏_{j ≠ i} (pᵢ.x − pⱼ.x)`,
the classical Lagrange interpolation formula.

**Source**: spqr/src/encoding/polynomial.rs (lines 106:4-137:5)
-/
theorem lagrange_interpolate_formula
    (pts : Slice Pt)
    (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.coefficients.val.length = pts.val.length ∧
      (pts.val.length = 0 → result.toGF216Poly = 0) ∧
      (0 < pts.val.length →
        ∃ ws : List Poly,
          ws.length = pts.val.length ∧
          (∀ (i : Nat) (hi : i < ws.length)
              (hpi : i < pts.val.length),
            (ws.get ⟨i, hi⟩).toGF216Poly *
              (X - C (GF16.toGF216
                (pts.val.get ⟨i, hpi⟩).x)) =
              X * C (lagrangeScaleGF216
                (pts.val.get ⟨i, hpi⟩) pts.val) *
                (prodLinearFactors pts.val 0 pts.val.length)) ∧
          (∀ (j : Nat)
              (hj : j < result.coefficients.val.length),
            (result.coefficients.val.get ⟨j, hj⟩).toGF216 =
              (ws.map (fun w =>
                (w.coefficients.val[j + 1]!).toGF216)).sum)) ⦄ := by
  unfold lagrange_interpolate
  step with zero_spec' pts.len as ⟨out, h_out_len, h_out_zero⟩
  step with slice_is_empty_spec pts as ⟨b, hb_eq⟩
  split
  · rename_i hb_true
    have h_empty : pts.val.length = 0 := by
      have := hb_eq
      simp_all
    simp only [WP.spec_ok]
    refine ⟨?_, ?_, ?_⟩
    · rw [h_out_len, h_empty]
    · intro _; exact h_out_zero
    · intro h_pos; omega
  · rename_i hb_false
    have h_nonempty : 0 < pts.val.length := by
      by_contra h_le
      push_neg at h_le
      interval_cases pts.val.length
      · simp_all
    step with lagrange_interpolate_prepare_spec pts h_len as
      ⟨template, h_template_len, _, _, _, h_template_eq⟩
    step with clone_spec template as ⟨working, h_working_eq⟩
    rw [h_working_eq]
    have h0_lt_pts : (0 : Nat) < pts.val.length := h_nonempty
    have h_template_pos : 0 < template.coefficients.val.length := by
      rw [h_template_len]
      omega
    have h_root_template :
        template.evalAt (pts.val.get ⟨0, h0_lt_pts⟩).x = 0 := by
      unfold Poly.evalAt
      rw [h_template_eq]
      exact prodLinearFactors_eval_root pts.val 0 pts.val.length 0
        (Nat.zero_le _) h_nonempty h0_lt_pts
    step with lagrange_interpolate_complete_spec template pts 0#usize
      h0_lt_pts h_template_pos h_root_template as
      ⟨working1, h_w1_len, h_w1_id⟩
    have h_w1_len_pts : working1.coefficients.val.length = pts.val.length + 1 := by
      rw [h_w1_len, h_template_len]
    have h_one_le_w1 : (1 : Nat) ≤ working1.coefficients.length := by
      change 1 ≤ working1.coefficients.val.length
      rw [h_w1_len_pts]
      omega
    step with alloc.vec.Vec.index_RangeFrom_spec
      working1.coefficients ⟨1#usize⟩ h_one_le_w1 as ⟨s, h_s_val, h_s_len⟩
    have h_s_len_pts : s.val.length = pts.val.length := by
      change s.length = pts.val.length
      rw [h_s_len]
      grind
    have h_v_overflow :
        out.coefficients.val.length + s.val.length ≤ Std.Usize.max := by
      rw [h_out_len, h_s_len_pts]
      omega
    step with extend_from_slice_GF16_spec out.coefficients s h_v_overflow as
      ⟨v, h_v_val⟩
    have h_out_val_nil : out.coefficients.val = [] :=
      List.length_eq_zero_iff.mp h_out_len
    have h_v_val' : v.val = s.val := by
      rw [h_v_val, h_out_val_nil, List.nil_append]
    have h_v_len : v.val.length = pts.val.length := by
      rw [h_v_val', h_s_len_pts]
    have h_v_coeff : ∀ (j : Nat), j < v.val.length →
        v.val[j]! = working1.coefficients.val[j + 1]! := by
      intro j hj
      have hj' : j < s.val.length := by rw [← h_v_val']; exact hj
      have hj'' : j + 1 < working1.coefficients.val.length := by
        rw [h_w1_len_pts]
        have : j < pts.val.length := by rw [← h_s_len_pts]; exact hj'
        omega
      have hgetv : v.val[j]! = s.val[j]! := by
        rw [h_v_val']
      rw [hgetv, h_s_val]
      rw [List.getElem!_drop 1 j]
      grind
    have h_end_le_pts : (Slice.len pts).val ≤ pts.val.length := by
      simp [Slice.len]
    have h_one_le_end : (1 : Nat) ≤ (Slice.len pts).val := by
      simp only [Slice.len, Usize.ofNatCore_val_eq]
      exact h_nonempty
    have h_v_lt_template : v.val.length < template.coefficients.val.length := by
      rw [h_v_len, h_template_len]; omega
    have h_wt_eq : template.coefficients.val.length = working1.coefficients.val.length :=
      h_w1_len.symm
    have h_eval_all_template :
        ∀ (i : Nat), 1 ≤ i → i < (Slice.len pts).val →
          ∀ (hi : i < pts.val.length),
            template.evalAt (pts.val.get ⟨i, hi⟩).x = 0 := by
      intro i _ _ hi
      unfold Poly.evalAt
      rw [h_template_eq]
      exact prodLinearFactors_eval_root pts.val 0 pts.val.length i
        (Nat.zero_le _) hi hi
    step with lagrange_interpolate_loop0.loop_spec
      pts template
      ({ start := 1#usize, «end» := Slice.len pts } : core.ops.range.Range Std.Usize)
      v working1
      h_end_le_pts h_template_pos h_v_lt_template h_wt_eq
      h_one_le_end h_eval_all_template as
      ⟨v1, h_v1_len, h_ws_ex⟩
    obtain ⟨ws', h_ws'_len, h_ws'_id, h_v1_coeff⟩ := h_ws_ex
    have h_v1_pts_len : v1.val.length = pts.val.length := by
      rw [h_v1_len, h_v_len]
    refine ⟨h_v1_pts_len, ?_, ?_⟩
    · intro h0; omega
    · intro _
      refine ⟨working1 :: ws', ?_, ?_, ?_⟩
      · simp [List.length_cons, h_ws'_len, Slice.len]
        omega
      · intro i hi hpi
        cases i with
        | zero =>
          simp only [List.get_eq_getElem, List.getElem_cons_zero]
          have := h_w1_id
          simp only [List.get_eq_getElem] at this
          grind
        | succ k =>
          simp only [List.get_eq_getElem, List.getElem_cons_succ]
          have hk : k < ws'.length := by
            simp [List.length_cons] at hi; omega
          have hki : 1 + k < pts.val.length := by
            simp only [Slice.len, Usize.ofNatCore_val_eq] at h_ws'_len
            have : k < ws'.length := hk
            rw [h_ws'_len] at this
            omega
          have := h_ws'_id k hk hki
          grind
      · intro j hj
        have hj' : j < v1.val.length := hj
        have hj_v : j < v.val.length := by rw [h_v_len]; rw [h_v1_pts_len] at hj'; exact hj'
        rw [h_v1_coeff j hj']
        rw [h_v_coeff j hj_v]
        simp [List.map_cons, List.sum_cons]

/-! ## Classical Lagrange interpolation formula

The corollary below makes the *classical* Lagrange formula
   `result(X) = ∑_i pᵢ.y · ∏_{j ≠ i} (X − pⱼ.x) / ∏_{j ≠ i} (pᵢ.x − pⱼ.x)`
visible as a Lean statement.  Recall that
`lagrangeScaleGF216 pᵢ pts = pᵢ.y * (∏_{j≠i}(pᵢ.x − pⱼ.x))^(2^16 − 2)`,
which is exactly `pᵢ.y / ∏_{j≠i}(pᵢ.x − pⱼ.x)` in `GF216` by Fermat's
little theorem (`x^(2^16 − 1) = 1` for `x ≠ 0`).  So the formula
takes the form
   `result.toGF216Poly =
       ∑_i C(lagrangeScaleGF216 pts[i] pts.val) ·
            ∏_{j ≠ i} (X − pts[j].x)`. -/

/--
**Lagrange basis polynomial**: the product `∏_{j ≠ i} (X − pts[j].x)`
of linear factors over all points except the `i`-th, as a polynomial
in `GF216[X]`.  Defined as
`prodLinearFactors pts 0 i.val * prodLinearFactors pts (i+1) pts.length`
when `i < pts.length`, and `1` otherwise.
-/
noncomputable def lagrangeBasisPoly
    (pts : List spqr.encoding.polynomial.Pt) (i : Nat) :
    Polynomial GF216 :=
  if i < pts.length then
    prodLinearFactors pts 0 i *
      prodLinearFactors pts (i + 1) pts.length
  else 1

/--
**Sum of `lagrangeScale · lagrangeBasis` over a prefix `[0, n)` of the
point list `pts`.**

This is the partial Lagrange interpolant
  `∑_{i=0}^{n−1} C(lagrangeScaleGF216 pts[i] pts) ·
       lagrangeBasisPoly pts i`,
i.e. the unique polynomial of degree `< pts.length` taking value
`pts[i].y` at `pts[i].x` for `i ∈ [0, n)` (modulo the assumption
of pairwise distinct x-coordinates).
-/
noncomputable def lagrangeInterpolantSum
    (pts : List spqr.encoding.polynomial.Pt) : Nat → Polynomial GF216
  | 0     => 0
  | n + 1 =>
      lagrangeInterpolantSum pts n +
        (if h : n < pts.length then
          C (lagrangeScaleGF216 (pts.get ⟨n, h⟩) pts) *
            lagrangeBasisPoly pts n
        else 0)

/-
**Classical Lagrange interpolation formula** (corollary of
`lagrange_interpolate_spec`).

Under the same precondition `pts.length + 1 ≤ Usize.max`, the Rust
function `Poly::lagrange_interpolate` returns a polynomial whose
`GF216[X]`-representation `result.toGF216Poly` equals the classical
Lagrange interpolant
   `∑_{i = 0}^{pts.length − 1}
        C(lagrangeScaleGF216 pts[i] pts.val) ·
        ∏_{j ≠ i} (X − pts[j].x)`.

Unfolding the definition of `lagrangeScaleGF216`, this is the
familiar expression
   `result(X) = ∑_i pᵢ.y · ∏_{j ≠ i} (X − pⱼ.x) / ∏_{j ≠ i} (pᵢ.x − pⱼ.x)`,
the unique polynomial of degree `< pts.length` satisfying
`result(pᵢ.x) = pᵢ.y` for all `i`.

**Proof sketch.**  Applying `lagrange_interpolate_spec` gives a list
of witness polynomials `ws` such that for every `i`,
  `ws[i] · (X − pts[i].x) =
       X · C(lagrangeScaleGF216 pts[i] pts.val) ·
       prodLinearFactors pts.val 0 pts.val.length`,
and
  `(j+1)-st coefficient sums to the j-th coefficient of result`
in characteristic 2.  Since
`prodLinearFactors pts 0 pts.length =
   (X − pts[i].x) · lagrangeBasisPoly pts i`,
we can cancel `(X − pts[i].x)` in `GF216[X]` (an integral domain) to
obtain `ws[i] = X · C(lagrangeScaleGF216 pts[i] pts.val) ·
                  lagrangeBasisPoly pts i`.
Each `ws[i]` therefore has zero constant term, and the
"coefficient-sum at `j+1`" identity becomes the polynomial identity
  `X · result.toGF216Poly =
        ∑_i X · C(lagrangeScaleGF216 pts[i] pts.val) · lagrangeBasisPoly pts i`,
from which dividing by the nonzerodivisor `X` yields the claim.
(The mechanical proof in Lean requires bridging the coefficient-list
representation `listToGF216Poly` with the polynomial identity above
and discharging the integral-domain cancellation; this is left as
`sorry` for now.)

**Source**: spqr/src/encoding/polynomial.rs (lines 106:4-137:5)
-/

-- Helper lemmas for the classical formula proof

/-- Splitting `prodLinearFactors` at a midpoint. -/
private lemma prodLinearFactors_split_at
    (pts : List Pt) (mid n : Nat)
    (hmid : mid ≤ n) (hn : n ≤ pts.length) :
    prodLinearFactors pts 0 n =
      prodLinearFactors pts 0 mid * prodLinearFactors pts mid n := by
  induction n with
  | zero =>
    have : mid = 0 := by omega
    subst this; simp
  | succ k ih =>
    by_cases hmk : mid = k + 1
    · subst hmk; simp
    · rw [prodLinearFactors_snoc pts 0 k (by omega) (by omega : k < pts.length),
          ih (by omega) (by omega),
          prodLinearFactors_snoc pts mid k (by omega) (by omega : k < pts.length)]
      ring

/-- The full product factors as `(X − pts[i].x) · lagrangeBasisPoly pts i`. -/
private lemma prodLinearFactors_eq_factor_mul_basis
    (pts : List Pt) (i : Nat)
    (hi : i < pts.length) :
    prodLinearFactors pts 0 pts.length =
      (X - C ((pts.get ⟨i, hi⟩).x.toGF216)) *
        lagrangeBasisPoly pts i := by
  simp only [lagrangeBasisPoly, if_pos hi]
  rw [prodLinearFactors_split_at pts (i + 1) pts.length (by omega) (le_refl _),
      prodLinearFactors_snoc pts 0 i (by omega) hi]
  ring

/-- Bridge: `getElem!` with `toGF216` equals `listToGF216Poly` coefficient. -/
private lemma getElem_bang_toGF216_eq_coeff
    (cs : List GF16) (j : Nat) :
    (cs[j]!).toGF216 = (listToGF216Poly cs).coeff j := by
  rw [listToGF216Poly_coeff]
  by_cases hj : j < cs.length
  · rw [dif_pos hj, List.get_eq_getElem]
    grind
  · rw [dif_neg hj]
    have : (cs[j]! : spqr.encoding.gf.GF16) = default := by
      grind
    rw [this]; exact GF16.toGF216_zero_val _ (by rfl)

/-- Degree bound for `prodLinearFactors`. -/
private lemma natDegree_prodLinearFactors_le
    (pts : List Pt) (s t : Nat) (hs : s ≤ t) (ht : t ≤ pts.length) :
    (prodLinearFactors pts s t).natDegree ≤ t - s := by
  induction t with
  | zero => simp [show s = 0 from by omega]
  | succ k ih =>
    by_cases hsk : s = k + 1
    · subst hsk; simp
    · rw [prodLinearFactors_snoc pts s k (by omega) (by omega : k < pts.length)]
      calc (prodLinearFactors pts s k * (X - C _)).natDegree
          ≤ (prodLinearFactors pts s k).natDegree +
              (X - C ((pts.get ⟨k, by omega⟩).x.toGF216)).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ (k - s) + 1 := by
            have h1 := ih (by omega) (by omega)
            have h2 : (X - C ((pts.get ⟨k, by omega⟩).x.toGF216) : GF216Poly).natDegree = 1 :=
              Polynomial.natDegree_X_sub_C _
            omega
        _ = k + 1 - s := by omega

/-- Degree bound for `lagrangeBasisPoly`. -/
private lemma natDegree_lagrangeBasisPoly_le
    (pts : List Pt) (i : Nat) (hi : i < pts.length) (hn : 0 < pts.length) :
    (lagrangeBasisPoly pts i).natDegree ≤ pts.length - 1 := by
  simp only [lagrangeBasisPoly, if_pos hi]
  calc (prodLinearFactors pts 0 i * prodLinearFactors pts (i + 1) pts.length).natDegree
      ≤ (prodLinearFactors pts 0 i).natDegree +
          (prodLinearFactors pts (i + 1) pts.length).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (i - 0) + (pts.length - (i + 1)) := by
        have h1 := natDegree_prodLinearFactors_le pts 0 i (by omega) (by omega)
        have h2 := natDegree_prodLinearFactors_le pts (i + 1) pts.length (by omega) (by omega)
        omega
    _ = pts.length - 1 := by omega

/-- `lagrangeInterpolantSum` equals a `Finset.sum`. -/
private lemma lagrangeInterpolantSum_eq_finset_sum
    (pts : List Pt) (n : Nat) (hn : n ≤ pts.length) :
    lagrangeInterpolantSum pts n =
      Finset.sum (Finset.range n) (fun i =>
        if h : i < pts.length then
          C (lagrangeScaleGF216 (pts.get ⟨i, h⟩) pts) *
            lagrangeBasisPoly pts i
        else 0) := by
  induction n with
  | zero => simp [lagrangeInterpolantSum]
  | succ k ih =>
    rw [lagrangeInterpolantSum, ih (by omega), Finset.sum_range_succ]

/-- Coefficient of `lagrangeInterpolantSum` beyond degree is zero. -/
private lemma lagrangeInterpolantSum_coeff_high
    (pts : List Pt) (n j : Nat) (hn : n ≤ pts.length)
    (hj : pts.length ≤ j) :
    (lagrangeInterpolantSum pts n).coeff j = 0 := by
  rw [lagrangeInterpolantSum_eq_finset_sum pts n hn]
  simp only [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  have hi' : i < pts.length := by omega
  rw [dif_pos hi']
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
    calc (C _ * lagrangeBasisPoly pts i).natDegree
        ≤ (lagrangeBasisPoly pts i).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ pts.length - 1 := natDegree_lagrangeBasisPoly_le pts i hi' (by omega)
      _ < j := by omega)

/-- Converting `List.map/sum` to `Finset.sum` indexed by `Fin`. -/
private lemma list_map_sum_eq_finset_sum
    {α β : Type} [AddCommMonoid β]
    (l : List α) (f : α → β) :
    (l.map f).sum = Finset.sum Finset.univ (fun i : Fin l.length => f (l.get i)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.get_eq_getElem]
    rw [ih, Fin.sum_univ_succ]
    simp [Fin.val_succ, List.get_eq_getElem]
@[step]
theorem lagrange_interpolate_spec
    (pts : Slice Pt)
    (h_len : pts.val.length + 1 ≤ Std.Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.toGF216Poly =
        lagrangeInterpolantSum pts.val pts.val.length ⦄ := by
  apply WP.spec_mono (lagrange_interpolate_formula pts h_len)
  intro result ⟨h_rlen, h_empty, h_nonempty⟩
  set n := pts.val.length with hn_def
  by_cases h0 : n = 0
  · -- Empty case: both sides are 0
    rw [h0, lagrangeInterpolantSum]
    have : result.coefficients.val.length = 0 := by rw [h_rlen]; exact h0
    exact Poly.toGF216Poly_eq_zero result this
  · -- Non-empty case
    have hpos : 0 < n := Nat.pos_of_ne_zero h0
    obtain ⟨ws, hws_len, hws_id, hws_coeff⟩ := h_nonempty hpos
    -- Step 1: Cancel (X − pts[i].x) to get ws[i] = X · C(scale_i) · basis_i
    have hws_poly : ∀ (i : Nat) (hi : i < ws.length) (hpi : i < n),
        (ws.get ⟨i, hi⟩).toGF216Poly =
          X * C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            lagrangeBasisPoly pts.val i := by
      intro i hi hpi
      have h_id := hws_id i hi hpi
      rw [prodLinearFactors_eq_factor_mul_basis pts.val i hpi] at h_id
      have hne : (X : GF216Poly) - C (GF16.toGF216 (pts.val.get ⟨i, hpi⟩).x) ≠ 0 :=
        (Polynomial.monic_X_sub_C _).ne_zero
      have h_rhs_rw :
          X * C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            ((X - C (GF16.toGF216 (pts.val.get ⟨i, hpi⟩).x)) *
              lagrangeBasisPoly pts.val i) =
          (X * C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            lagrangeBasisPoly pts.val i) *
          (X - C (GF16.toGF216 (pts.val.get ⟨i, hpi⟩).x)) := by ring
      rw [h_rhs_rw] at h_id
      exact mul_right_cancel₀ hne h_id
    -- Step 2: Show each term agrees
    have h_term_eq : ∀ (m : ℕ) (i : Fin ws.length),
        ((ws.get i).coefficients.val[m + 1]!).toGF216 =
          (C (lagrangeScaleGF216 (pts.val.get ⟨i.val, by
            omega⟩) pts.val) *
            lagrangeBasisPoly pts.val i.val).coeff m := by
      intro m ⟨i, hi⟩
      have hpi : i < n := by grind
      rw [getElem_bang_toGF216_eq_coeff]
      change (ws.get ⟨i, hi⟩).toGF216Poly.coeff (m + 1) = _
      rw [hws_poly i hi hpi]
      rw [show X * C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            lagrangeBasisPoly pts.val i =
          X * (C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            lagrangeBasisPoly pts.val i) from by ring]
      exact Polynomial.coeff_X_mul _ _
    -- Step 3: Show coefficient equality using ext
    unfold Poly.toGF216Poly
    ext m
    rw [listToGF216Poly_coeff]
    by_cases hm : m < result.coefficients.val.length
    · -- m < n: use coefficient identity + term equality
      rw [dif_pos hm, hws_coeff m hm, list_map_sum_eq_finset_sum]
      rw [Finset.sum_congr rfl (fun i _ => h_term_eq m i)]
      -- Now both sides are Finset sums of the same terms
      rw [lagrangeInterpolantSum_eq_finset_sum pts.val n (le_refl _)]
      rw [Polynomial.finset_sum_coeff]
      apply Finset.sum_bij (fun (a : Fin ws.length) _ => a.val)
        (fun a _ => by rw [Finset.mem_range]; grind)
        (fun a₁ _ a₂ _ h => Fin.val_injective h)
        (fun b hb => by
          rw [Finset.mem_range] at hb
          exact ⟨⟨b, by omega⟩, Finset.mem_univ _, rfl⟩)
        (fun a _ => by
          simp only [dif_pos (show a.val < pts.val.length from by omega)])
    · -- m ≥ n: both sides are 0
      rw [dif_neg hm]
      exact (lagrangeInterpolantSum_coeff_high pts.val n m (le_refl _)
        (by rw [h_rlen] at hm; push_neg at hm; omega)).symm

end spqr.encoding.polynomial.Poly
