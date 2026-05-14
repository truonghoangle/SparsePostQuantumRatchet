/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateLoopBody0

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

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

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
    (pts : Slice spqr.encoding.polynomial.Pt)
    (template : Poly)
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (working : Poly)
    (h_end_le_pts : iter.«end».val ≤ pts.val.length)
    (h_template_pos : 0 < template.coefficients.val.length)
    (h_v_lt : v.val.length < template.coefficients.val.length)
    (h_wt : template.coefficients.val.length = working.coefficients.val.length)
    (h_le : iter.start.val ≤ iter.«end».val)
    (h_eval_all : ∀ (i : Nat), iter.start.val ≤ i → i < iter.«end».val →
        ∀ (hi : i < pts.val.length),
          template.evalAt (pts.val.get ⟨i, hi⟩).x = 0) :
    spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0
      iter pts v template working
        ⦃ (result : alloc.vec.Vec spqr.encoding.gf.GF16) =>
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
  unfold spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                        alloc.vec.Vec spqr.encoding.gf.GF16 ×
                        encoding.polynomial.Poly) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                      alloc.vec.Vec spqr.encoding.gf.GF16 ×
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
