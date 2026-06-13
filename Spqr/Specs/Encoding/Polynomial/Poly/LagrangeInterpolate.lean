/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.Poly.Clone
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolatePrepare
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateComplete

/-!
# Spec theorem for `lagrange_interpolate`: loop body 1

The outer Rust function `Poly::lagrange_interpolate` computes the unique polynomial of degree
`< pts.len()` that interpolates a set of points `pts : &[Pt]` with distinct x-coordinates.
After preparing the "product" polynomial
  `template = ∏_j (x − pts[j].x)`
and unrolling the first iteration, the function maintains two parallel coefficient vectors:

  * `out : Poly` — the running interpolant of degree `< pts.len()`,
    whose coefficient vector has length `pts.len() − 1 + 1 = pts.len()`;
  * `working : Poly` — the per-iteration contribution
    `pi.y · ∏_{j ≠ i} (x − pts[j].x) / ∏_{j ≠ i} (pi.x − pts[j].x)`
    *shifted up by one position* (i.e. `working` represents
    `x · <the polynomial we need>`), so its coefficient vector has
    length `pts.len() + 1`.

To add the `i`-th contribution to `out` *and* divide by `x` simultaneously, the inner `for j in
0..out.coefficients.len()` loop (lines 131:12-134:13) executes

  `out.coefficients[j] += working.coefficients[j + 1]`

for each `j` in `0..out.coefficients.len()`.  Reading from index `j + 1` rather than `j` is exactly
the "divide by x" trick that the source-level comment describes: it shifts `working` down by one
position without performing a `memmove`.

Concretely, the extracted Lean body `encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0.body`
performs one step of this inner loop.  Given the (fixed) polynomial `working`, the range iterator
`iter : 0..out.coefficients.len()`, and the current coefficient vector `v` of `out`, it:

  1. Retrieves the next index `j` from the range iterator.
  2. If the iterator is exhausted (`none`), returns `done (v, working)`
     — the inner loop is complete and the unchanged pair
     `(v, working)` is propagated to the outer loop.
  3. Otherwise, calls `Vec::index_mut(v, j)` to obtain a mutable
     reference `g = v[j]` together with the write-back closure
     `index_mut_back`, computes `i = j + 1`, reads
     `g1 = working.coefficients[i]`, performs the GF(2¹⁶) sum
     `g2 = g + g1` via
     `encoding.gf.GF16.Insts.CoreOpsArithAddAssignGF16.add_assign`,
     writes back `v[j] := g2`, and returns `cont (iter1, v1)` with
     the iterator advanced and the updated vector.

**Source**: spqr/src/encoding/polynomial.rs (lines 131:12-134:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0.body`**:

One step of the inner Lagrange-interpolation accumulation `out.coefficients[j] +=
working.coefficients[j + 1]`.  Given a fixed polynomial `working` (the shifted per-iteration
contribution), a range iterator over `0..out.coefficients.len()`, and the current coefficient vector
`v` of `out`, the body processes the next index from the iterator:

• The function always succeeds (no panic) for any valid inputs satisfying the preconditions, since
  `Vec.index_mut`, `Usize` addition (within bounds), `Vec.index`, and the by-value
  `AddAssign<GF16>::add_assign` are all total on bounded integers within range.
• In the `done` case (iterator exhausted):
    both the coefficient vector `v` and the polynomial `working` are
    returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.
• In the `cont` case (index `j = iter.start.val` processed):
    - The iterator has advanced by exactly one position:
        `iter1.start = iter.start + 1`, `iter1.«end» = iter.«end»`.
    - The coefficient vector length is preserved:
        `v1.val.length = v.val.length`.
    - Position `j = iter.start.val` has been updated with the
      GF(2¹⁶) sum
        `v1[j].toGF216 =
            v[j].toGF216 +
            working.toGF216.coefficients[j + 1]`
      where the `+` on the right-hand side is addition in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with subtraction and is bitwise XOR of the 16-bit
      encodings).
    - All other positions are unchanged:
        `v1.val[k]? = v.val[k]?`  for `k ≠ j`.

The two preconditions `iter.«end».val ≤ v.val.length` and `iter.«end».val <
working.coefficients.val.length` are exactly the invariants maintained by the surrounding outer
loop:

  `out.coefficients.len() == _w_l - 1`  and
  `working.coefficients.len() == _w_l`,

which together guarantee that for every `j < iter.«end».val ≤ out.coefficients.len()` both `v[j]`
and `working.coefficients[j + 1]` are valid reads.

**Source**: spqr/src/encoding/polynomial.rs (lines 131:12-134:13)
-/
@[step]
theorem body_spec
    (working : Poly)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_lt_working : iter.«end».val < working.coefficients.val.length) :
    body working iter v ⦃ cf =>
      match cf with
      | ControlFlow.done (v', working') =>
          v' = v ∧ working' = working ∧ ¬ (iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v1) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          v1.val.length = v.val.length ∧
          (∀ (h_idx : iter.start.val < v1.val.length),
            (v1.val.get ⟨iter.start.val, h_idx⟩).toGF216 =
              (v.val[iter.start.val]!).toGF216 +
              (working.coefficients.val[iter.start.val + 1]!).toGF216) ∧
          (∀ (k : Nat),
            k ≠ iter.start.val →
            v1.val[k]? = v.val[k]?) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    simp only [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_slice_index,
      uncurry_apply_pair, not_lt, List.get_eq_getElem, List.getElem!_eq_getElem?_getD, ne_eq]
    have h_j_lt_v : iter.start.val < v.val.length := by omega
    have h_jp1_lt_w : iter.start.val + 1 < working.coefficients.val.length := by
      omega
    step*
    refine ⟨h_lt, h_start1, h_end1, by
              simp_all, ?_, ?_⟩
    · intro h_idx
      simp_all
    · intro k hk
      simp_all
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]
    simp [WP.spec_ok]
    grind
end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0

/-!
# Spec theorem for `lagrange_interpolate`: loop 1

The outer Rust function `Poly::lagrange_interpolate` (in `src/encoding/polynomial.rs`, lines
106:4-137:5) computes the unique polynomial of degree `< pts.len()` that interpolates a set of
points `pts : &[Pt]` with distinct x-coordinates.  After preparing the "product" polynomial
  `template = ∏_j (x − pts[j].x)`
and unrolling the first iteration, the function maintains two parallel coefficient vectors:

  * `out : Poly` — the running interpolant of degree `< pts.len()`,
    whose coefficient vector has length `pts.len() − 1 + 1 = pts.len()`;
  * `working : Poly` — the per-iteration contribution
    `pi.y · ∏_{j ≠ i} (x − pts[j].x) / ∏_{j ≠ i} (pi.x − pts[j].x)`
    *shifted up by one position* (i.e. `working` represents
    `x · <the polynomial we need>`), so its coefficient vector has
    length `pts.len() + 1`.

To add the `i`-th contribution to `out` *and* divide by `x` simultaneously, the inner `for j in
0..out.coefficients.len()` loop (lines 131:12-134:13) executes

  `out.coefficients[j] += working.coefficients[j + 1]`

for each `j` in `0..out.coefficients.len()`.  Reading from index `j + 1` rather than `j` is exactly
the "divide by x" trick that the source-level comment describes: it shifts `working` down by one
position without performing a `memmove`.

This file specifies the full loop (the `loop` fixed-point wrapper around the body), providing a
closed-form postcondition that characterises the entire output vector after all iterations.  The
per-iteration specification is in
`Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateLoopBoby1`.

**Source**: spqr/src/encoding/polynomial.rs (lines 131:12-134:13)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0

@[step]
theorem loop_spec
    (working : encoding.polynomial.Poly)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_lt_working : iter.«end».val < working.coefficients.val.length)
    (h_le : iter.start.val ≤ iter.«end».val) :
    Poly.lagrange_interpolate_loop0_loop0
      iter v working ⦃ (result : (alloc.vec.Vec GF16) ×
                                  encoding.polynomial.Poly) =>
      result.2 = working ∧
      result.1.val.length = v.val.length ∧
      (∀ (j : Nat),
        iter.start.val ≤ j →
        j < iter.«end».val →
        ∀ (hj : j < result.1.val.length),
          (result.1.val.get ⟨j, hj⟩).toGF216 =
            (v.val[j]!).toGF216 +
            (working.coefficients.val[j + 1]!).toGF216) ∧
      (∀ (j : Nat),
        ¬(iter.start.val ≤ j ∧ j < iter.«end».val) →
        result.1.val[j]? = v.val[j]?) ⦄ := by
  unfold Poly.lagrange_interpolate_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
                        alloc.vec.Vec GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize ×
                    alloc.vec.Vec GF16) =>
        p.1.«end» = iter.«end» ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ iter.«end».val ∧
        p.2.val.length = v.val.length ∧
        (∀ (j : Nat),
          iter.start.val ≤ j →
          j < p.1.start.val →
          ∀ (hj : j < p.2.val.length),
            (p.2.val.get ⟨j, hj⟩).toGF216 =
              (v.val[j]!).toGF216 +
              (working.coefficients.val[j + 1]!).toGF216) ∧
        (∀ (j : Nat),
          ¬(iter.start.val ≤ j ∧ j < p.1.start.val) →
          p.2.val[j]? = v.val[j]?))
  · rintro ⟨iter', v'⟩ ⟨h_end', h_ge', h_le', h_len', h_processed, h_unchanged⟩
    simp only [] at h_end' h_ge' h_le' h_len' h_processed h_unchanged ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_end_le_v' : iter'.«end».val ≤ v'.val.length := by omega
    have h_end_lt_working' : iter'.«end».val < working.coefficients.val.length := by
      omega
    step*
    split
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_v_eq, h_w_eq, h_nlt⟩ := r_post
      subst h_v_eq
      subst h_w_eq
      refine ⟨rfl, h_len', ?_, ?_⟩
      · intro j hj1 hj2 hj
        exact h_processed j hj1 (by omega) hj
      · intro j hj
        apply h_unchanged
        push Not at hj ⊢
        intro h1; have := hj h1; omega
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v1len, h_modified, h_frame⟩ := r_post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_end1]; exact h_end'
      · omega
      · omega
      · omega
      · intro j hj1 hj2 hj
        by_cases hjk : j < iter'.start.val
        · have hj_ne : j ≠ iter'.start.val := by omega
          have hj_v' : j < v'.val.length := by omega
          have h_fr := h_frame j hj_ne
          have h_old := h_processed j hj1 hjk hj_v'
          have h_get_eq := list_get_of_getElem?_eq h_fr hj hj_v'
          simp only [List.get_eq_getElem] at h_get_eq h_old ⊢
          rw [h_get_eq, h_old]
        · have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          have h_mod := h_modified (by omega)
          have h_unch_s : v'.val[iter'.start.val]? = v.val[iter'.start.val]? :=
            h_unchanged iter'.start.val (by push Not; intro _; omega)
          have h_bang_s := getElem_bang_eq h_unch_s (by omega) (by omega)
          simp only [List.get_eq_getElem] at h_mod ⊢
          rw [h_mod, h_bang_s]
      · intro j hj
        push Not at hj
        have hj_ne : j ≠ iter'.start.val := by
          intro heq; subst heq
          grind
        have h_fr := h_frame j hj_ne
        have h_old_unch : v'.val[j]? = v.val[j]? := by
          apply h_unchanged; push Not; intro h1
          have := hj h1; omega
        rw [h_fr, h_old_unch]
      · grind
  · refine ⟨rfl, le_refl _, h_le, rfl, ?_, ?_⟩
    · intro j hj1 hj2
      grind
    · intro _ _; rfl

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0

/-!
# Spec theorem for `lagrange_interpolate`: loop body 0

The outer Rust function `Poly::lagrange_interpolate` (in `src/encoding/polynomial.rs`, lines
106:4-137:5) computes the unique polynomial of degree `< pts.len()` that interpolates a set of
points `pts : &[Pt]` with distinct x-coordinates.  After preparing the "product" polynomial
  `template = ∏_j (X − pts[j].x)`
and unrolling the first iteration, the function maintains two parallel coefficient vectors:

  * `out : Poly` — the running interpolant of degree `< pts.len()`,
    whose coefficient vector `v` has length `pts.len() − 1`;
  * `working : Poly` — a scratch polynomial whose coefficient vector
    has length `pts.len()` and is *re-loaded from `template` at the
    start of every iteration* via `copy_from_slice`.

The body of the outer loop processes the `i`-th point (lines 122:8-135:9):

  1. **Reset `working` from `template`**:
     `working.coefficients.copy_from_slice(&template.coefficients)`
     — restores `working = template = ∏_j (X − pts[j].x)`.
  2. **Compute the `i`-th Lagrange contribution in place**:
     `working.lagrange_interpolate_complete(pts, i)`.  By the spec
     of `lagrange_interpolate_complete`, the new polynomial
     `working₁` satisfies the polynomial identity
     ```
       working₁ · (X − pts[i].x) =
         X · C(lagrangeScale(pts[i], pts)) · template
     ```
     i.e. `working₁ = X · pᵢ.y · ∏_{j ≠ i} (X − pts[j].x) /
     ∏_{j ≠ i} (pts[i].x − pts[j].x)` (the `X` factor is the
     "shifted-up by one position" artifact described in
     `LagrangeInterpolateComplete`).
  3. **Add the contribution to `out`, simultaneously dividing by `X`**:
     the inner `for j in 0..out.coefficients.len()` loop executes
       `out.coefficients[j] += working.coefficients[j + 1]`
     for every `j` in `0..out.coefficients.len()`.  Reading from
     `working.coefficients[j + 1]` rather than `j` is exactly the
     "divide by `X`" trick: it shifts `working₁` down by one position
     without performing a `memmove`.  This inner loop is specified by
     `lagrange_interpolate_loop0_loop0.loop_spec`.

Concretely, the extracted Lean body `encoding.polynomial.Poly.lagrange_interpolate_loop0.body`
performs one step of this outer loop.  Given the slice `pts`, the fixed `template`, the range
iterator `iter : 1..pts.len()`, the current coefficient vector `v` of `out`, and the scratch
polynomial `working`, it:

  1. Retrieves the next index `i` from the range iterator.
  2. If the iterator is exhausted (`none`), returns `done v` — the
     outer loop is complete and the unchanged vector `v` is propagated
     out.
  3. Otherwise, deref's `working.coefficients` to a mutable slice `s`,
     deref's `template.coefficients` to the (immutable) slice `s1`,
     copies `s1` into `s` via `core.slice.Slice.copy_from_slice`,
     writes the result back to produce a fresh `Vec` `v1`, calls
     `Poly.lagrange_interpolate_complete { coefficients := v1 } pts i`
     to obtain `working₁`, reads `i1 = v.len`, calls
     `Poly.lagrange_interpolate_loop0_loop0 (0..i1) v working₁` to
     obtain the updated coefficient vector `v₂` and the (unchanged)
     polynomial `working₂ = working₁`, and finally returns
     `cont (iter1, v₂, working₂)` with the iterator advanced.

**Source**: spqr/src/encoding/polynomial.rs (lines 122:8-135:9)
-/


namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_loop0.body`**:

One step of the outer Lagrange-interpolation loop.  Given the slice `pts`, a fixed `template`
polynomial (the product `∏_j (X − pts[j].x)` precomputed by `lagrange_interpolate_prepare`), a
range iterator over the unprocessed indices, the current coefficient vector `v` of the running
interpolant, and the scratch polynomial `working`, the body processes the next index from the
iterator:

• The function always succeeds (no panic) provided the preconditions hold, since
  `Vec.deref_mut`, `Vec.deref`, `Slice.copy_from_slice` (with matching lengths), the
  `lagrange_interpolate_complete` call (with the root precondition), and the inner
  `lagrange_interpolate_loop0_loop0` (with the length preconditions) are total under those
  assumptions.
• In the `done` case (iterator exhausted):
    the coefficient vector `v` is returned unchanged, and the iterator
    condition is negated: `¬ (iter.start.val < iter.«end».val)`.
• In the `cont` case (index `i = iter.start.val` processed):
    - The iterator has advanced by exactly one position:
        `iter1.start = iter.start + 1`,
        `iter1.«end» = iter.«end»`.
    - The coefficient-vector length is preserved:
        `v₂.val.length = v.val.length`.
    - The new scratch polynomial `working₂` has the same coefficient
      vector length as `template`:
        `working₂.coefficients.val.length =
            template.coefficients.val.length`.
    - **`working₂` is the `i`-th Lagrange contribution** of `template`,
      shifted up by one position; equivalently the polynomial identity
        `working₂.toGF216Poly · (X − C(pts[i].x.toGF216)) =
            X · C(lagrangeScaleGF216 pts[i] pts) ·
              template.toGF216Poly`
      holds in `GF216[X]`.
    - **Inner-loop update** on the running interpolant: for every
      coefficient position `j ∈ [0, v.length)`,
        `v₂.val[j].toGF216 =
            v.val[j].toGF216 +
            working₂.coefficients.val[j + 1].toGF216`
      where the `+` on the right-hand side is addition in
      `GF216 = GaloisField 2 16` (which, in characteristic 2,
      coincides with subtraction and is bitwise XOR of the 16-bit
      encodings).  Reading at position `j + 1` is the "divide by `X`"
      trick that strips the leading-zero coefficient artifact of
      `working₂` without an explicit shift.

The preconditions are exactly the loop invariants maintained by the surrounding outer Rust loop
(`out.coefficients.len() == _w_l - 1` and `working.coefficients.len() == _w_l`) together with the
algebraic root condition required by `lagrange_interpolate_complete`:

* `iter.«end».val ≤ pts.val.length` — every iterator index is a
  valid point index.
* `0 < template.coefficients.val.length` — the prepared product
  polynomial is non-empty (true for `pts.len() ≥ 1`).
* `v.val.length < template.coefficients.val.length` — the running
  interpolant has one fewer coefficient than the scratch polynomial,
  so the inner-loop read at position `j + 1` is always in range.
* `template.coefficients.val.length =
    working.coefficients.val.length` — the `copy_from_slice` call
  requires matching slice lengths.
* For the current index `i = iter.start.val`,
  `template.evalAt pts[i].x = 0` — this is the algebraic root
  precondition required by `lagrange_interpolate_complete`, and it
  holds because `template = ∏_j (X − pts[j].x)` vanishes at every
  `pts[j].x` (see `LagrangeInterpolatePrepare`).

**Source**: spqr/src/encoding/polynomial.rs (lines 122:8-135:9)
-/
@[step]
theorem body_spec
    (pts : Slice Pt)
    (template : Poly)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16)
    (working : Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_template_pos : 0 < template.coefficients.val.length)
    (h_v_lt : v.val.length < template.coefficients.val.length)
    (h_wt : template.coefficients.val.length = working.coefficients.val.length)
    (h_eval : iter.start.val < iter.«end».val →
        ∀ (hi : iter.start.val < pts.val.length),
          template.evalAt (pts.val.get ⟨iter.start.val, hi⟩).x = 0) :
    body pts template iter v working ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬ (iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, v₂, working₂) =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          v₂.val.length = v.val.length ∧
          working₂.coefficients.val.length =
            template.coefficients.val.length ∧
          (∀ (hi : iter.start.val < pts.val.length),
            working₂.toGF216Poly *
              (X - C (GF16.toGF216
                (pts.val.get ⟨iter.start.val, hi⟩).x)) =
              X * C (lagrangeScaleGF216
                (pts.val.get ⟨iter.start.val, hi⟩) pts.val) *
                template.toGF216Poly) ∧
          (∀ (j : Nat) (hj : j < v₂.val.length),
            (v₂.val.get ⟨j, hj⟩).toGF216 =
              (v.val[j]!).toGF216 +
              (working₂.coefficients.val[j + 1]!).toGF216) ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have hi_pts : iter.start.val < pts.val.length := by omega
    have h_eval_t : template.evalAt (pts.val.get ⟨iter.start.val, hi_pts⟩).x = 0 :=
      h_eval h_lt hi_pts
    have h_match_len :
        (alloc.vec.Vec.deref_mut working.coefficients).1.length =
        (alloc.vec.Vec.deref template.coefficients).length := by
      simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.deref, Slice.length]
      exact h_wt.symm
    have hv1_val :
        ((alloc.vec.Vec.deref_mut working.coefficients).2
          (alloc.vec.Vec.deref template.coefficients)).val = template.coefficients.val := by
      simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.deref]
    have h_toGF_eq :
      ({coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                          (alloc.vec.Vec.deref template.coefficients)}
        : encoding.polynomial.Poly).toGF216Poly = template.toGF216Poly := by
      unfold Poly.toGF216Poly
      rw [hv1_val]
    have h_poly_eval :
      ({coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                          (alloc.vec.Vec.deref template.coefficients)}
        : encoding.polynomial.Poly).evalAt
          (pts.val.get ⟨iter.start.val, hi_pts⟩).x = 0 := by
      unfold Poly.evalAt
      rw [h_toGF_eq]
      exact h_eval_t
    have h_v1_len :
        0 < ({coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                                (alloc.vec.Vec.deref template.coefficients)}
              : encoding.polynomial.Poly).coefficients.val.length := by
      change 0 < ((alloc.vec.Vec.deref_mut working.coefficients).2
                  (alloc.vec.Vec.deref template.coefficients)).val.length
      rw [hv1_val]
      exact h_template_pos
    simp only [lift, bind_tc_ok]
    have h_copy :=
      core.slice.Slice.copy_from_slice.step_spec
        GF16.Insts.CoreMarkerCopy
        (alloc.vec.Vec.deref_mut working.coefficients).1
        (alloc.vec.Vec.deref template.coefficients)
        h_match_len
    have h_complete :=
      lagrange_interpolate_complete_spec
        { coefficients := (alloc.vec.Vec.deref_mut working.coefficients).2
                            (alloc.vec.Vec.deref template.coefficients) }
        pts iter.start hi_pts h_v1_len h_poly_eval
    have h_v_len_val : (alloc.vec.Vec.len v).val = v.val.length := by
      simp [alloc.vec.Vec.len]
    -- Step through copy_from_slice
    apply WP.spec_bind h_copy
    intro s2 hs2
    rw [hs2]
    -- Step through lagrange_interpolate_complete
    apply WP.spec_bind h_complete
    intro working1 ⟨h_w1_len, h_w1_poly⟩
    -- Step through lagrange_interpolate_loop0_loop0
    apply WP.spec_bind (lagrange_interpolate_loop0_loop0.loop_spec
        working1
        { start := 0#usize, «end» := alloc.vec.Vec.len v }
        v
        (by rw [h_v_len_val])
        (by rw [h_v_len_val, h_w1_len, hv1_val]; exact h_v_lt)
        (by grind))
    rintro ⟨v2, working2⟩ ⟨h_w2_eq, h_v2_len, h_processed, h_unchanged⟩
    simp only [uncurry_apply_pair, not_lt, List.get_eq_getElem, X_mul_C,
      List.getElem!_eq_getElem?_getD, WP.spec_ok]
    simp only [← h_w2_eq, List.get_eq_getElem, X_mul_C, UScalar.ofNatCore_val_eq, zero_le,
      alloc.vec.Vec.len, Usize.ofNatCore_val_eq, List.getElem!_eq_getElem?_getD,
      forall_const] at h_w1_len h_w1_poly h_processed ⊢
    refine ⟨h_lt, h_start1, h_end1, h_v2_len, ?_, ?_, ?_⟩
    · rw [h_w1_len, hv1_val]
    · intro hi; rw [h_toGF_eq] at h_w1_poly; exact h_w1_poly
    · intro j hj
      grind
  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]
    grind

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

/-!
# Spec theorem for `lagrange_interpolate`: loop 0

The outer Rust function `Poly::lagrange_interpolate` (in `src/encoding/polynomial.rs`, lines
106:4-137:5) computes the unique polynomial of degree `< pts.len()` that interpolates a set of
points `pts : &[Pt]` with distinct x-coordinates.  After preparing the "product" polynomial
  `template = ∏_j (X − pts[j].x)`
and unrolling the first iteration, the function maintains two parallel coefficient vectors:

  * `out : Poly` — the running interpolant of degree `< pts.len()`,
    whose coefficient vector `v` has length `pts.len() − 1`;
  * `working : Poly` — a scratch polynomial whose coefficient vector
    has length `pts.len()` and is *re-loaded from `template` at the
    start of every iteration* via `copy_from_slice`.

The outer `for i in 1..pts.len()` loop (lines 122:8-135:9) repeatedly executes three steps for
each remaining point index `i`:

  1. **Reset `working` from `template`** via
     `working.coefficients.copy_from_slice(&template.coefficients)`.
  2. **Compute the `i`-th Lagrange contribution in place** via
     `working.lagrange_interpolate_complete(pts, i)`; the new
     polynomial `working_i` satisfies the polynomial identity
     `working_i · (X − pts[i].x) = X · lagrangeScale(pts[i], pts) ·
       template`.
  3. **Add the contribution to `out`, simultaneously dividing by `X`**:
     the inner `for j in 0..out.coefficients.len()` loop executes
       `out.coefficients[j] += working_i.coefficients[j + 1]`
     for every `j` in `0..out.coefficients.len()`.

This file specifies the full outer loop (the `loop` fixed-point wrapper around the body).  The
postcondition is the closed-form aggregation of the per-iteration body specification
(`LagrangeInterpolateLoopBody0.body_spec`):

**Closed-form postcondition**:

After the loop completes over the range `iter.start..iter.«end»` on the coefficient vector `v` and
the scratch polynomial `working`:

1. **Length preserved**: `result.val.length = v.val.length`.

2. **Existence of the per-iteration witness polynomials**: there
   exists a list `ws : List Poly` collecting the scratch polynomials
   `working_i` produced at each iteration, such that

   - `ws.length = iter.«end».val − iter.start.val` (one witness per
     processed index).

   - **Polynomial identity** at every iteration: for every
     `k < ws.length` (corresponding to point index
     `i = iter.start.val + k`),
       `ws[k].toGF216Poly · (X − C(pts[i].x.toGF216)) =
            X · C(lagrangeScaleGF216 pts[i] pts) ·
              template.toGF216Poly`
     in `GF216[X]`.  This is exactly the postcondition of
     `lagrange_interpolate_complete` applied to the freshly-restored
     `working` at iteration `i`.

   - **Cumulative XOR-accumulation** of contributions: for every
     position `j < result.val.length`,
       `result.val[j].toGF216 =
            v.val[j].toGF216 +
            ∑_{k=0}^{ws.length−1} ws[k].coefficients[j+1].toGF216`
     where the sum is in `GF216 = GaloisField 2 16` (which, in
     characteristic 2, coincides with subtraction and is bitwise
     XOR of the 16-bit encodings).  Reading at position `j + 1` is
     the "divide by `X`" trick that strips the leading-zero
     coefficient artifact of `ws[k]` without an explicit shift.

These three pieces capture exactly the algorithmic and algebraic content of the body specification
(`LagrangeInterpolateLoopBody0.body_spec`) aggregated across all iterations: the running
interpolant is the running sum of Lagrange basis contributions (shifted up by one position to
implement the implicit "divide by `X`" optimisation), and each contribution `ws[k]` is the
polynomial that `lagrange_interpolate_complete` produces at the corresponding `pts[i]`.

The preconditions are exactly the invariants maintained by the surrounding Rust loop together
with the algebraic root condition required by `lagrange_interpolate_complete` on every
iteration index:

* `iter.«end».val ≤ pts.val.length` — every iterator index is a
  valid point index.
* `0 < template.coefficients.val.length` — the prepared product
  polynomial is non-empty (true for `pts.len() ≥ 1`).
* `v.val.length < template.coefficients.val.length` — the running
  interpolant has one fewer coefficient than the scratch polynomial,
  so the inner-loop read at position `j + 1` is always in range.
* `template.coefficients.val.length =
    working.coefficients.val.length` — the `copy_from_slice` call
  requires matching slice lengths.
* `iter.start.val ≤ iter.«end».val` — the range is well-formed.
* For every `i` in the processed range,
  `template.evalAt pts[i].x = 0` — this is the algebraic root
  precondition required by `lagrange_interpolate_complete` at each
  step, and it holds because `template = ∏_j (X − pts[j].x)` vanishes
  at every `pts[j].x` (see `LagrangeInterpolatePrepare`).

**Source**: spqr/src/encoding/polynomial.rs (lines 122:8-135:9)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

/--
**Closed-form postcondition for `encoding.polynomial.Poly.lagrange_interpolate_loop0`**:

The full outer Lagrange-interpolation accumulation loop.  Starting from a range
`iter.start..iter.«end»`, the running coefficient vector `v` of `out`, a fixed `template`
polynomial, and a scratch polynomial `working`, the loop processes indices
`i = iter.start.val, iter.start.val + 1, …, iter.«end».val − 1` and returns the final
coefficient vector `result` satisfying:

• **Length preserved**: `result.val.length = v.val.length`.

• **Existence of per-iteration witnesses**: there exists a list
  `ws : List Poly` of length `iter.«end».val − iter.start.val`,
  collecting the scratch polynomials `working_i` produced at each
  iteration, such that

    - **Polynomial identity** (one per iteration): for every
      `k < ws.length` and the corresponding point index
      `i = iter.start.val + k`,
        `ws[k].toGF216Poly · (X − C(pts[i].x.toGF216)) =
            X · C(lagrangeScaleGF216 pts[i] pts) ·
              template.toGF216Poly`
      in `GF216[X]`.  This is the algebraic content produced by
      `lagrange_interpolate_complete` on the freshly-restored
      `working = template` at index `i`.

    - **Cumulative XOR-accumulation**: for every position
      `j < result.val.length`,
        `result.val[j].toGF216 =
            v.val[j].toGF216 +
            (ws.map (fun w => w.coefficients[j+1].toGF216)).sum`
      where the sum is over the witnesses `ws[0], …, ws[ws.length−1]`
      in `GF216 = GaloisField 2 16`.  In characteristic 2 this sum
      coincides with bitwise XOR of the 16-bit encodings, matching the
      Rust `+=` accumulation.

The loop invariant is the same property restricted to the prefix of indices already processed:
at the iteration boundary `p.1.start.val`, the partial witness list `ws` has length
`p.1.start.val − iter.start.val`, the polynomial identity holds for each element, and the
running vector `p.2.1` equals `v` plus the partial XOR-sum of contributions.

**Source**: spqr/src/encoding/polynomial.rs (lines 122:8-135:9)
-/
@[step]
theorem loop_spec
    (pts : Slice Pt)
    (template : Poly)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16)
    (working : Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_template_pos : 0 < template.coefficients.val.length)
    (h_v_lt : v.val.length < template.coefficients.val.length)
    (h_wt : template.coefficients.val.length = working.coefficients.val.length)
    (h_le : iter.start.val ≤ iter.«end».val)
    (h_eval_all : ∀ (i : Nat), iter.start.val ≤ i → i < iter.«end».val →
        ∀ (hi : i < pts.val.length),
          template.evalAt (pts.val.get ⟨i, hi⟩).x = 0) :
    Poly.lagrange_interpolate_loop0
      iter pts v template working
        ⦃ (result : alloc.vec.Vec GF16) =>
          result.val.length = v.val.length ∧
          ∃ ws : List Poly,
            ws.length = iter.«end».val - iter.start.val ∧
            (∀ (k : Nat) (hk : k < ws.length)
                (hi : iter.start.val + k < pts.val.length),
              (ws.get ⟨k, hk⟩).toGF216Poly *
                (X - C (GF16.toGF216
                  (pts.val.get ⟨iter.start.val + k, hi⟩).x)) =
                X * C (lagrangeScaleGF216
                  (pts.val.get ⟨iter.start.val + k, hi⟩) pts.val) *
                  template.toGF216Poly) ∧
            (∀ (j : Nat) (hj : j < result.val.length),
              (result.val.get ⟨j, hj⟩).toGF216 =
                (v.val[j]!).toGF216 +
                (ws.map (fun w =>
                  (w.coefficients.val[j + 1]!).toGF216)).sum) ⦄ := by
  unfold Poly.lagrange_interpolate_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
                        alloc.vec.Vec GF16 ×
                        encoding.polynomial.Poly) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize ×
                      alloc.vec.Vec GF16 ×
                      encoding.polynomial.Poly) =>
        p.1.«end» = iter.«end» ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ iter.«end».val ∧
        p.2.1.val.length = v.val.length ∧
        p.2.2.coefficients.val.length = template.coefficients.val.length ∧
        ∃ ws : List Poly,
          ws.length = p.1.start.val - iter.start.val ∧
          (∀ (k : Nat) (hk : k < ws.length)
              (hi : iter.start.val + k < pts.val.length),
            (ws.get ⟨k, hk⟩).toGF216Poly *
              (X - C (GF16.toGF216
                (pts.val.get ⟨iter.start.val + k, hi⟩).x)) =
              X * C (lagrangeScaleGF216
                (pts.val.get ⟨iter.start.val + k, hi⟩) pts.val) *
                template.toGF216Poly) ∧
          (∀ (j : Nat) (hj : j < p.2.1.val.length),
            (p.2.1.val.get ⟨j, hj⟩).toGF216 =
              (v.val[j]!).toGF216 +
              (ws.map (fun w =>
                (w.coefficients.val[j + 1]!).toGF216)).sum))
  · rintro ⟨iter', v', working'⟩
      ⟨h_end', h_ge', h_le', h_len', h_wt', ws, h_ws_len, h_ws_id, h_ws_sum⟩
    simp only [] at h_end' h_ge' h_le' h_len' h_wt' h_ws_len h_ws_id h_ws_sum ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_end_le_pts' : iter'.«end».val ≤ pts.val.length := by omega
    have h_v_lt' : v'.val.length < template.coefficients.val.length := by omega
    have h_wt'' : template.coefficients.val.length = working'.coefficients.val.length := by
      omega
    have h_eval' : iter'.start.val < iter'.«end».val →
        ∀ (hi : iter'.start.val < pts.val.length),
          template.evalAt (pts.val.get ⟨iter'.start.val, hi⟩).x = 0 := by
      intro _ hi
      exact h_eval_all iter'.start.val h_ge' (by omega) hi
    step*
    split
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_v_eq, h_nlt⟩ := r_post
      subst h_v_eq
      refine ⟨h_len', ws, ?_, ?_, ?_⟩
      · -- ws.length = iter'.start.val - iter.start.val and ¬ (iter'.start.val < iter'.«end».val),
        -- combined with h_le' and h_end_val gives iter'.start.val = iter.«end».val.
        omega
      · intro k hk hi
        exact h_ws_id k hk hi
      · exact h_ws_sum
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v2len, h_w2len, h_poly_id, h_coord⟩ := r_post
      have hend_eq : r_post.1.«end».val = iter'.«end».val := by rw [h_end1]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_end1]; exact h_end'
      · omega
      · omega
      · rw [h_v2len]; exact h_len'
      · exact h_w2len
      · -- Existential: extend the witness list by the freshly produced working₂.
        refine ⟨ws ++ [r_post.2.2], ?_, ?_, ?_⟩
        · -- length: (ws.length + 1) = (iter'.start.val + 1) - iter.start.val
          simp only [List.length_append, List.length_singleton]
          omega
        · -- polynomial identity for each k < ws.length + 1
          intro k hk hi
          simp only [List.length_append, List.length_singleton] at hk
          simp only [List.get_eq_getElem]
          by_cases hk_old : k < ws.length
          · -- k < ws.length: reuse the IH on the prefix `ws`.
            have h_get_eq :
                (ws ++ [r_post.2.2])[k]'(by
                  simp only [List.length_append, List.length_singleton]; omega) =
                  ws[k]'hk_old := by
              rw [List.getElem_append_left hk_old]
            rw [h_get_eq]
            have := h_ws_id k hk_old hi
            simp only [List.get_eq_getElem] at this
            exact this
          · -- k = ws.length: this is the new contribution at iter'.start.val.
            have hk_eq : k = ws.length := by omega
            have hk_idx : iter.start.val + k = iter'.start.val := by omega
            have h_get_eq :
                (ws ++ [r_post.2.2])[k]'(by
                  simp only [List.length_append, List.length_singleton]; omega) =
                  r_post.2.2 := by
              subst hk_eq
              simp [List.getElem_append_right]
            rw [h_get_eq]
            have hi' : iter'.start.val < pts.val.length := by
              rw [← hk_idx]; exact hi
            have h_pts_eq :
                pts.val[iter.start.val + k]'hi =
                  pts.val[iter'.start.val]'hi' := by
              congr 1
            rw [h_pts_eq]
            have := h_poly_id hi'
            simp only [List.get_eq_getElem] at this
            grind
        · -- cumulative XOR-accumulation at every position j < v₂.val.length
          intro j hj
          have hj' : j < v'.val.length := by
            rw [← h_v2len]; exact hj
          have hjv : j < v.val.length := by rw [← h_len']; exact hj'
          -- From the body: v₂[j] = v'[j]! + working₂.coefficients[j+1]!
          have h_v2j := h_coord j hj
          -- From the IH on v': v'[j] = v[j]! + ws.map(...).sum
          have h_v'j := h_ws_sum j hj'
          -- Bridge `[]!` and `.get` on v'.
          have h_v'_bang : (v'.val[j]!).toGF216 = (v'.val.get ⟨j, hj'⟩).toGF216 := by
            rw [getElem!_pos v'.val j hj']
            rfl
          rw [h_v2j, h_v'_bang, h_v'j]
          -- Goal: v[j]!.toGF216 + ws.map(..).sum + working₂.coefficients[j+1]!.toGF216
          --     = v[j]!.toGF216 + (ws ++ [working₂]).map(..).sum
          simp only [List.map_append, List.map_singleton, List.sum_append,
            List.sum_cons, List.sum_nil, add_zero]
          ring
      · grind
  · -- Initial invariant: empty witness list.
    refine ⟨rfl, le_refl _, h_le, rfl, h_wt.symm, [], ?_, ?_, ?_⟩
    · simp
    · intro k hk; simp at hk
    · intro j hj
      simp only [List.map_nil, List.sum_nil, add_zero]
      rw [getElem!_pos v.val j hj]
      rfl

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

/-! # Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate`

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

namespace spqr.encoding.polynomial.Poly

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
**Spec for `alloc.vec.Vec.extend_from_slice` specialised to `GF16`**:


The `core.clone.Clone` instance for `GF16` (`encoding.gf.GF16.Insts.CoreCloneClone`) has `clone x =
ok x` for every `x`, hence the elementwise `Slice.clone` on `s` returns `ok s` and the resulting
vector is exactly `v.val ++ s.val`.  The precondition `v.val.length + s.val.length ≤ Usize.max`
discharges the overflow guard in the body of `extend_from_slice`.
-/
private lemma extend_from_slice_GF16_spec
    (v : alloc.vec.Vec GF16)
    (s : Slice GF16)
    (h : v.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice
        GF16.Insts.CoreCloneClone v s
      ⦃ (r : alloc.vec.Vec GF16) =>
        r.val = v.val ++ s.val ⦄ := by
  have h_clone_x :
      ∀ x ∈ s.val,
        GF16.Insts.CoreCloneClone.clone x = ok x := by
    intros _ _
    simp [GF16.Insts.CoreCloneClone.clone]
  have h_slclone :
      Slice.clone GF16.Insts.CoreCloneClone.clone s = ok s := by
    obtain ⟨s', h_eq, hs⟩ := WP.spec_imp_exists (Slice.clone_spec h_clone_x)
    rw [h_eq, ← hs]
  unfold alloc.vec.Vec.extend_from_slice
  have hlen : v.length + s.length ≤ Usize.max := h
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
    (h_len : pts.val.length + 1 ≤ Usize.max) :
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
  step with zero_spec pts.len as ⟨out, h_out_len, h_out_zero⟩
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
      push Not at h_le
      interval_cases pts.val.length
      · simp_all
    step with lagrange_interpolate_prepare_spec pts h_len as
      ⟨template, h_template_len, _, _, _, h_template_eq⟩
    step with clone_spec template as ⟨working, h_working_eq⟩
    rw [h_working_eq]
    have h0_lt_pts : (0 : Nat) < pts.val.length := h_nonempty
    have h_template_pos : 0 < template.degree := by
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
      rw [h_w1_len]
      grind [degree]
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
        out.coefficients.val.length + s.val.length ≤ Usize.max := by
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
      rw [h_v_len]; omega
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
      ({ start := 1#usize, «end» := Slice.len pts } : core.ops.range.Range Usize)
      v working1
      h_end_le_pts h_template_pos h_v_lt_template h_wt_eq
      h_one_le_end h_eval_all_template as
      ⟨v1, h_v1_len, ws', h_ws'_len, h_ws'_id, h_v1_coeff⟩
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

**Source**: spqr/src/encoding/polynomial.rs (lines 106:4-137:5)
-/

@[step]
theorem lagrange_interpolate_spec
    (pts : Slice Pt)
    (h_len : pts.length + 1 ≤ Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.toGF216Poly = lagrangeInterpolantSum pts pts.length ⦄ := by
  apply WP.spec_mono (lagrange_interpolate_formula pts h_len)
  intro result ⟨h_rlen, h_empty, h_nonempty⟩
  set n := pts.length with hn_def
  by_cases h0 : n = 0
  · rw [h0, lagrangeInterpolantSum]
    have : result.coefficients.val.length = 0 := by rw [h_rlen]; exact h0
    exact Poly.toGF216Poly_eq_zero result this
  · have hpos : 0 < n := Nat.pos_of_ne_zero h0
    obtain ⟨ws, hws_len, hws_id, hws_coeff⟩ := h_nonempty hpos
    have hws_poly : ∀ (i : Nat) (hi : i < ws.length) (hpi : i < n),
        (ws.get ⟨i, hi⟩).toGF216Poly =
          X * C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            lagrangeBasisPoly pts.val i := by
      intro i hi hpi
      have h_id := hws_id i hi hpi
      rw [prodLinearFactors_eq_X_sub_C_mul pts.val i hpi,
          show prodLinearFactors pts.val 0 i *
              prodLinearFactors pts.val (i + 1) pts.val.length =
              lagrangeBasisPoly pts.val i from by
            unfold lagrangeBasisPoly; rw [if_pos hpi]] at h_id
      have hne : (X : GF216[X]) - C (GF16.toGF216 (pts.val.get ⟨i, hpi⟩).x) ≠ 0 :=
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
    have h_term_eq : ∀ (m : ℕ) (i : Fin ws.length),
        ((ws.get i).coefficients.val[m + 1]!).toGF216 =
          (C (lagrangeScaleGF216 (pts.val.get ⟨i.val, by
            omega⟩) pts.val) *
            lagrangeBasisPoly pts.val i.val).coeff m := by
      intro m ⟨i, hi⟩
      have hpi : i < n := by grind
      rw [show ((ws.get ⟨i, hi⟩).coefficients.val[m + 1]!).toGF216 =
              (listToGF216Poly (ws.get ⟨i, hi⟩).coefficients.val).coeff (m + 1) from
            getElem!_toGF216_eq_coeff _ _]
      change (ws.get ⟨i, hi⟩).toGF216Poly.coeff (m + 1) = _
      rw [hws_poly i hi hpi]
      rw [show X * C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            lagrangeBasisPoly pts.val i =
          X * (C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
            lagrangeBasisPoly pts.val i) from by ring]
      exact Polynomial.coeff_X_mul _ _
    unfold Poly.toGF216Poly
    ext m
    rw [listToGF216Poly_coeff]
    by_cases hm : m < result.coefficients.val.length
    · rw [dif_pos hm, hws_coeff m hm, List.map_sum_eq_Finset_sum]
      rw [Finset.sum_congr rfl (fun i _ => h_term_eq m i)]
      rw [lagrangeInterpolantSum_eq_finset_sum pts.val n (le_refl _)]
      rw [Polynomial.finset_sum_coeff]
      apply Finset.sum_bij (fun (a : Fin ws.length) _ => a.val)
        (fun a _ => by rw [Finset.mem_range]; grind)
        (fun a₁ _ a₂ _ h => Fin.val_injective h)
        (fun b hb => by
          rw [Finset.mem_range] at hb
          exact ⟨⟨b, by grind⟩, Finset.mem_univ _, rfl⟩)
        (fun a _ => by
          simp only [dif_pos (show a.val < pts.val.length from by omega)])
    · rw [dif_neg hm]
      exact (lagrangeInterpolantSum_coeff_high pts.val n m (le_refl _)
        (by rw [h_rlen] at hm; push Not at hm; omega)).symm

end spqr.encoding.polynomial.Poly
