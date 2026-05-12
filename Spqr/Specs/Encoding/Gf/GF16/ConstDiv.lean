/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Encoding.Gf.GF16.ConstMul
/-! # Spec theorem for `spqr::encoding::gf::GF16::const_div`

In GF(2¹⁶) — the Galois field with 65 536 elements — every non-zero
element `b` satisfies `b^(2¹⁶ − 1) = 1`, so the multiplicative
inverse is `b⁻¹ = b^(2¹⁶ − 2)` and `a / b = a · b^(2¹⁶ − 2)`.  The
exponent `2¹⁶ − 2 = 2 + 4 + 8 + ⋯ + 2¹⁵` is computed by iterated
squaring: starting from `square = b` and `out = a`, one repeats

  `square = square²;  out = out · square`

for the 15 indices `i = 1, …, 15`, after which

  `out = a · b^(2¹⁶ − 2) = a / b`.

The function proceeds in three layers:
  1. `const_div_loop.body` — one iteration of the `while i < 16`
     loop, performing `square := square²`, `out := out · square`,
     `i := i + 1`.
  2. `const_div_loop` — the Aeneas-extracted `loop` fixed-point
     driving the body for 15 rounds.
  3. `const_div` — the entry point, which initialises
     `(square, out, i) := (other, self, 1)` and returns the loop's
     final accumulator `out = self · other^(2¹⁶ − 2) = self / other`.

**Source**: spqr/src/encoding/gf.rs (lines 572:4-589:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf

namespace spqr.encoding.gf.GF16

/-- **Per-iteration postcondition for `encoding.gf.GF16.const_div_loop.body`**:

One iteration of the iterated-squaring loop driving `GF16::const_div`.
Both branches are characterised at the GF(2¹⁶) level via
`Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly`:

* **`done`** — the loop guard `i < 16#usize` failed; the returned
  accumulator is the unchanged `out`:
    `result.value.val.toGF216 = out.value.val.toGF216`.

* **`cont`** — the loop guard held; the new state `(square', out', _)`
  satisfies the squaring recurrence
    `square'.value.val.toGF216 =
        square.value.val.toGF216 * square.value.val.toGF216`,
    `out'.value.val.toGF216 =
        out.value.val.toGF216 * square'.value.val.toGF216`.

**Source**: spqr/src/encoding/gf.rs (lines 580:12-586:13)
-/
@[step]
theorem const_div_loop_body_spec
    (square out : GF16) (i : Usize) :
    const_div_loop.body square out i ⦃ (cf : ControlFlow (GF16 × GF16 × Usize) GF16) =>
      match cf with
      | ControlFlow.done result =>
          (result.toGF216 : GF216) = out.toGF216
      | ControlFlow.cont (square', out', _) =>
          (square'.toGF216 : GF216) =
            square.toGF216 * square.toGF216 ∧
          (out'.toGF216 : GF216) =
            out.toGF216 * square'.toGF216 ⦄ := by
  unfold const_div_loop.body
  step*

/-- **Closed-form postcondition for `encoding.gf.GF16.const_div_loop`**:

The iterated-squaring loop driving `GF16::const_div`, specified at
the GF(2¹⁶) level by the closed-form iterated-squaring identity:

  `result.value.val.toGF216 =
       out.value.val.toGF216 *
       square.value.val.toGF216 ^ (2 ^ (17 − i.val) − 2)`.

Specialised to the entry point `(square, out, i) = (other, self, 1)`
this collapses to `self · other^(2¹⁶ − 2) = self / other`, i.e.
division in GF(2¹⁶).

The proof applies `loop.spec_decr_nat` with measure `16 − i.val`
and the inductive invariant that, at any intermediate state
`(square', out', i')` with `i.val ≤ i'.val ≤ 16`,

  `square'.value.val.toGF216 =
       square.value.val.toGF216 ^ (2 ^ (i'.val − i.val))`,
  `out'.value.val.toGF216 =
       out.value.val.toGF216 *
       square.value.val.toGF216 ^ (2 ^ (i'.val − i.val + 1) − 2)`.

The active step is discharged via `const_div_loop_body_spec`
(registered `@[step]` above); the routine commutative-ring exponent
identities

  `(square^(2^k))² = square^(2^(k+1))`,
  `square^(2^(k+1) − 2) · square^(2^(k+1)) = square^(2^(k+2) − 2)`,

are settled by `omega` on the exponents (after `pow_succ` rewriting).
The `done` branch forces `i'.val = 16`, at which point the invariant
already coincides with the postcondition (because
`16 − i.val + 1 = 17 − i.val`).

**Source**: spqr/src/encoding/gf.rs (lines 580:12-586:13)
-/
theorem const_div_loop_spec
    (square out : GF16) (i : Usize)
    (hi : i.val ≤ 16) :
    const_div_loop square out i ⦃ (result : GF16) =>
      result.toGF216 = out.toGF216 * square.toGF216 ^ (2 ^ (17 - i.val) - 2) ⦄ := by
  unfold const_div_loop
  apply loop.spec_decr_nat
    (measure := fun (p : GF16 × GF16 × Usize) => 16 - p.2.2.val)
    (inv := fun (p : GF16 × GF16 × Usize) =>
      p.2.2.val ≤ 16 ∧ i.val ≤ p.2.2.val ∧
      (p.1.toGF216 : GF216) =
        square.toGF216 ^ (2 ^ (p.2.2.val - i.val)) ∧
      (p.2.1.toGF216 : GF216) =
        out.toGF216 *
          square.toGF216 ^ (2 ^ (p.2.2.val - i.val + 1) - 2))
  · rintro ⟨s', o', i'⟩ ⟨hi'_le, hi'_ge, h_sq, h_out⟩
    simp only []
    unfold const_div_loop.body
    by_cases hLt : i' < 16#usize
    · simp only [hLt, ↓reduceIte]
      step*
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · -- new square as a power of the original
        rw [square1_post, h_sq, ← pow_add]
        have hk : i1.val - i.val = (i'.val - i.val) + 1 := by scalar_tac
        rw [show (2 ^ (i'.val - i.val) + 2 ^ (i'.val - i.val) : Nat)
              = 2 ^ ((i'.val - i.val) + 1) from by rw [pow_succ]; ring,
            ← hk]
      · -- new out as a power of the original
        rw [out1_post, square1_post, h_sq, h_out, mul_assoc, ← pow_add, ← pow_add]
        have hk1 : i1.val - i.val + 1 = (i'.val - i.val + 1) + 1 := by scalar_tac
        have h_2le : 2 ≤ 2 ^ (i'.val - i.val + 1) := by
          calc (2 : Nat) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (i'.val - i.val + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
        have h_eq :
            (2 ^ (i'.val - i.val + 1) - 2) +
              (2 ^ (i'.val - i.val) + 2 ^ (i'.val - i.val)) =
            2 ^ (i1.val - i.val + 1) - 2 := by
          have hdouble :
              2 ^ (i'.val - i.val) + 2 ^ (i'.val - i.val) =
              2 ^ (i'.val - i.val + 1) := by rw [pow_succ]; ring
          rw [hdouble, hk1, pow_succ]; omega
        rw [h_eq]
      · scalar_tac
    · simp only [hLt, ↓reduceIte]
      have hi'_eq : i'.val = 16 := by scalar_tac
      have h17 : 17 - i.val = i'.val - i.val + 1 := by omega
      rw [h17]
      exact h_out
  · refine ⟨hi, le_refl _, ?_, ?_⟩
    · simp only [Nat.sub_self, pow_zero, pow_one]
    · simp only [Nat.sub_self, zero_add, pow_one, pow_zero, mul_one]

/-- **Spec theorem for `spqr.encoding.gf.GF16.const_div`**:

`const_div` computes GF(2¹⁶) division `self / other` on the `GF16`
wrapper by Fermat-style iterated squaring, deferring to the
extracted loop driver
`encoding.gf.GF16.const_div_loop other self 1#usize`.

The result satisfies the GF(2¹⁶)-level postcondition:

  `(result.value.val.toGF216 : GF216) =
       self.value.val.toGF216 *
       other.value.val.toGF216 ^ (2 ^ 16 − 2)`,

i.e. the GF(2¹⁶) quotient `self · other^(2¹⁶ − 2)`.  When
`other ≠ 0`, Fermat's little theorem in GF(2¹⁶) gives
`other^(2¹⁶ − 1) = 1`, so `other^(2¹⁶ − 2) = other⁻¹` and the
right-hand side is genuinely `self / other`.

This follows from `const_div_loop_spec` at the entry-point loop state
`(square, out, i) = (other, self, 1)`, where `17 − 1 = 16` so the
closed-form exponent collapses to `2¹⁶ − 2`.

**Source**: spqr/src/encoding/gf.rs (lines 572:4-589:5)
-/
@[step]
theorem const_div_spec (self other : GF16) :
    const_div self other ⦃ (result : GF16) =>
      result.toGF216  = self.toGF216 * other.toGF216 ^ (2 ^ 16 - 2) ⦄ := by
  unfold const_div
  have h := const_div_loop_spec other self 1#usize (by scalar_tac)
  step*

end spqr.encoding.gf.GF16
