/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePointsLoopBody0
/-!
# Spec theorem for `spqr::encoding::polynomial::lagrange_polys_for_complete_points`: loop 0

The Rust function `lagrange_polys_for_complete_points` (in `src/encoding/polynomial.rs`, lines
469:0-496:1) precomputes the array of Lagrange basis polynomials for the "complete points" —
evaluation points `0, 1, …, N−1` in GF(2¹⁶) with `y`-coordinate `GF16::ONE`.  The function begins
by constructing an array `ones` of `N` copies of `Pt { x: GF16::ZERO, y: GF16::ONE }`, then runs a
`while i < N` loop (lines 477:8-482:9) that sets `ones[i].x.value = i as u16` for each index `i`.

This file specifies **loop 0** — the `loop` fixed-point wrapper around the body
(`LagrangePolysForCompletePointsLoopBody0.body_spec`), which iterates over indices `i = 0, 1, …,
N−1` and sets the `x`-coordinate of each point to the corresponding GF(2¹⁶) element.

The extracted Lean function `encoding.polynomial.lagrange_polys_for_complete_points_loop0` applies
`Std.loop` to the body function
`encoding.polynomial.lagrange_polys_for_complete_points_loop0.body`, iterating from a starting
index `i` up to `N`.

At each step, the body processes index `i`:
  1. **Done** (`i ≥ N`): the loop terminates and `ones` is returned unchanged.
  2. **Continue** (`i < N`):
     a. Updates `ones[i].x.value := i` (cast from `usize` to `u16`).
     b. The `y` field of `ones[i]` is set to `GF16::ONE`.
     c. All other entries `ones[j]` for `j ≠ i` are left unchanged.
     d. Advances the loop counter: `i1 = i + 1`.

**Closed-form postcondition** (after all iterations from `i` to `N−1`):

  - **Processed positions** (`i ≤ j < N`): the `x`-coordinate has been set:
      `result[j].x.value.val = j` and `result[j].y = GF16.ONE`
    Equivalently, lifting the `x`-coordinate into `GF216`:
      `result[j].x.toGF216 = Nat.toGF216 j`.

  - **Unprocessed positions** (`j < i`): the array is unchanged from the input:
      `result[j]? = ones[j]?`

At the call site in `lagrange_polys_for_complete_points`, the loop starts with `i = 0`, so all
positions are processed and every entry satisfies `ones[j].x.value.val = j` and
`ones[j].y = GF16.ONE`.

In GF(2¹⁶), the elements `0, 1, …, N−1` (for `N ≤ 2¹⁶`) are pairwise distinct because the
canonical map `Nat → GF(2¹⁶)` is injective on `{0, …, 2¹⁶ − 1}` (each natural number below `2¹⁶`
has a unique binary polynomial representative of degree < 16).

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0

/--
**Spec theorem for `encoding.polynomial.lagrange_polys_for_complete_points_loop0`**:

The full `while i < N` initialisation loop in `lagrange_polys_for_complete_points`, which sets the
`x`-coordinate of each point `ones[j]` to the GF(2¹⁶) element with raw value `j`.  Given the
point array `ones` of size `N`, and the starting index `i`, the loop processes all indices from
`i` to `N−1` and returns the completed array `result` satisfying:

• The function always succeeds (no panic) provided the preconditions hold, since all array
  accesses and updates are bounded by `N`, and the loop counter `i < N` is checked before any
  operation.

• **Initialisation postcondition** (every position `j ∈ [i, N)` has been set):
    `∀ j, i.val ≤ j → j < N.val →
      result[j].x.value.val = j ∧ result[j].y = GF16.ONE`
  Equivalently, lifting the `x`-coordinate into `GF216`:
    `result[j].x.toGF216 = Nat.toGF216 j`.

• **Unchanged positions** (positions `j < i` are untouched):
    `∀ j, j < i.val → result[j]? = ones[j]?`

The result satisfies the GF(2¹⁶)-level postcondition:

  `∀ j ∈ [i, N), result[j].x.value.val = j ∧ result[j].y = GF16.ONE`

where the `x`-coordinate is the loop index cast to `u16` and the `y`-coordinate is the
multiplicative identity `GF16::ONE`.

The proof unfolds `lagrange_polys_for_complete_points_loop0` to expose the underlying `loop` call
and applies `loop.spec_decr_nat` with the natural-number measure `N − i`, using `body_spec` from
`LagrangePolysForCompletePointsLoopBody0` at each step.

**Source**: spqr/src/encoding/polynomial.rs (lines 477:8-482:9)
-/
@[step]
theorem loop_spec
    {N : Usize}
    (ones : Array Pt N)
    (i : Usize)
    (h_N_bound : N.val ≤ 65536)
    (h_i_le_N : i ≤ N) :
    lagrange_polys_for_complete_points_loop0 ones i ⦃ result =>
      (∀ (j : Nat), i ≤ j → j < N →
            (result[j]!).x.value.val = j ∧
            (result[j]!).y = GF16.ONE) ∧
      (∀ (j : Nat), j < i → result[j]! = ones[j]!)⦄ := by
  unfold lagrange_polys_for_complete_points_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : (Array Pt N) × Usize) => N - p.2)
    (inv := fun (p : (Array Pt N) × Usize) =>
        i ≤ p.2 ∧
        p.2 ≤ N ∧
        (∀ (j : Nat), i ≤ j → j < p.2 →
            (∀ (hj : j < p.1.length),
            (p.1[j]!).x.value.val = j ∧
            (p.1[j]!).y = GF16.ONE)) ∧
        (∀ (j : Nat), ¬(i ≤ j ∧ j < p.2) → p.1[j]! = ones[j]!))
  · rintro ⟨ones', i'⟩
      ⟨h_i_le_i', h_i'_le_N, h_proc, h_rest⟩
    simp only [] at h_i_le_i' h_i'_le_N h_proc h_rest ⊢
    have h_body := body_spec ones' i' h_N_bound
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      grind
    | ControlFlow.cont (ones1, i1) =>
      obtain ⟨h_lt, h_i1, h_at_i, h_others⟩ := h_cf
      refine ⟨⟨by grind, by grind, fun j h_ij h_ji1 h_idx => ?_, fun j h_not => ?_⟩, by grind⟩
      · -- Processed positions: i ≤ j < i1
        by_cases h_eq : j = i'.val
        · -- j = i'.val: directly from body spec
          subst h_eq
          exact h_at_i h_idx
        · -- j ≠ i'.val, so j < i': from invariant + unchanged positions
          have h_unch := h_others j (by omega)
          rw [h_unch]
          grind
      · -- Unchanged positions: ¬(i ≤ j ∧ j < i1)
        have h_unch := h_others j (by grind)
        rw [h_unch]
        exact h_rest j (by grind)
  · grind

end spqr.encoding.polynomial.lagrange_polys_for_complete_points_loop0
