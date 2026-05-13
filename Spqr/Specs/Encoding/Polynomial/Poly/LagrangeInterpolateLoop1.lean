/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateLoopBoby1

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

**Closed-form postcondition**:

After the loop completes over the range `iter.start..iter.«end»` on the coefficient vector `v` and
the fixed polynomial `working`:

1. The polynomial `working` is returned unchanged in the second
   component of the result pair (the inner loop never mutates
   `working`; it only reads it).
2. The vector length is preserved:
     `result.1.length = v.length`.
3. For each processed position `j` with
   `iter.start.val ≤ j` and `j < iter.«end».val`:
     `result.1[j].toGF216 =
         v[j].toGF216 +
         working.coefficients[j + 1].toGF216`
   where the addition on the right-hand side is in
   `GF216 = GaloisField 2 16` (which, in characteristic 2,
   coincides with subtraction and is bitwise XOR of the 16-bit
   encodings).
4. All other positions are unchanged:
     `result.1[j]? = v[j]?`  for `j` outside the processed range.

The correctness of each step relies on the fact that the modified position `j = iter'.start.val`
has not yet been touched when step `j` executes (only positions `iter.start.val, …, j − 1` have
been modified so far), so reading `v_current[j]` yields the original `v[j]`.  Likewise the read
position `j + 1` in `working` is never modified by the loop.

**Source**: spqr/src/encoding/polynomial.rs (lines 131:12-134:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

private lemma list_get_of_getElem?_eq {T : Type} {xs ys : List T}
    {k : Nat}
    (h : xs[k]? = ys[k]?) (hx : k < xs.length) (hy : k < ys.length) :
    xs.get ⟨k, hx⟩ = ys.get ⟨k, hy⟩ := by
  have h1 : xs[k]? = some (xs.get ⟨k, hx⟩) := List.getElem?_eq_getElem hx
  have h2 : ys[k]? = some (ys.get ⟨k, hy⟩) := List.getElem?_eq_getElem hy
  rw [h1, h2] at h
  exact Option.some_injective _ h

private lemma getElem_bang_eq {T : Type} [Inhabited T] {xs ys : List T} {k : Nat}
    (h : xs[k]? = ys[k]?)
    (hx : k < xs.length) (hy : k < ys.length) :
    xs[k]! = ys[k]! := by
  rw [getElem!_pos xs k hx, getElem!_pos ys k hy]
  exact list_get_of_getElem?_eq h hx hy

/--
**Closed-form postcondition for `encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0`**:

The full inner Lagrange-interpolation accumulation loop `out.coefficients[j] +=
working.coefficients[j + 1]`.  Starting from a range `iter.start..iter.«end»`, a coefficient vector
`v` of `out`, and a fixed polynomial `working`, the loop processes indices
`j = iter.start.val, iter.start.val + 1, …, iter.«end».val − 1` and returns a pair `(v', working')`
satisfying:

• **`working` preserved**: `result.2 = working` (the inner loop reads
  but never mutates `working`).
• **Length preserved**: `result.1.length = v.length`.
• **Processed positions** (`iter.start.val ≤ j ∧ j < iter.«end».val`):
    `result.1[j].toGF216 =
        v[j].toGF216 +
        working.coefficients[j + 1].toGF216`
  where the addition is in `GF216 = GaloisField 2 16`
  (equivalently, subtraction in characteristic 2; i.e. bitwise XOR).
• **Unchanged positions** (all other `j`):
    `result.1[j]? = v[j]?`.

The loop invariant tracks which positions have been processed: after iterating indices
`iter.start.val, …, k − 1`, positions in `[iter.start.val, k)` carry their final values and all
other positions still hold their original values.  The body spec
(`LagrangeInterpolateLoopBoby1.body_spec`) guarantees that each step modifies exactly one
position (`j = iter'.start.val`) and leaves all others unchanged, and the key correctness
observation is that the read position (`j + 1`) in `working` is never touched by the loop and
position `j` in `v` has not yet been modified when step `j` executes.

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
theorem loop_spec
    (working : encoding.polynomial.Poly)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_lt_working : iter.«end».val < working.coefficients.val.length)
    (h_le : iter.start.val ≤ iter.«end».val) :
    spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0
      iter v working ⦃ (result : (alloc.vec.Vec spqr.encoding.gf.GF16) ×
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
  unfold spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                        alloc.vec.Vec spqr.encoding.gf.GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                    alloc.vec.Vec spqr.encoding.gf.GF16) =>
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
        push_neg at hj ⊢
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
            h_unchanged iter'.start.val (by push_neg; intro _; omega)
          have h_bang_s := getElem_bang_eq h_unch_s (by omega) (by omega)
          simp only [List.get_eq_getElem] at h_mod ⊢
          rw [h_mod, h_bang_s]
      · intro j hj
        push_neg at hj
        have hj_ne : j ≠ iter'.start.val := by
          intro heq; subst heq
          grind
        have h_fr := h_frame j hj_ne
        have h_old_unch : v'.val[j]? = v.val[j]? := by
          apply h_unchanged; push_neg; intro h1
          have := hj h1; omega
        rw [h_fr, h_old_unch]
      · grind
  · refine ⟨rfl, le_refl _, h_le, rfl, ?_, ?_⟩
    · intro j hj1 hj2
      grind
    · intro _ _; rfl

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0
