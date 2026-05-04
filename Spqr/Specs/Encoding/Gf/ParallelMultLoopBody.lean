/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Mul2U16

/-! # Spec Theorem for `encoding::gf::parallel_mult` — loop body 0

Specification and proof for
`encoding.gf.parallel_mult_loop.body`, which executes a single
iteration of the `while i + 2 <= into.len() { … }` loop inside
`parallel_mult`.  The full loop is driven by
`encoding.gf.parallel_mult_loop` (the Aeneas-extracted `loop`
fixed-point); this file isolates the per-step behaviour so that
`parallel_mult_loop_spec` can appeal to a clean step lemma via
`loop.spec_decr_nat`.

One call to the body with state `(a, into, i)` performs the following
computation:

  1. **Termination guard** — if `i + 2 > into.len()`, the loop is
     exhausted: return `done (a, into, i)` (the state is unchanged
     and the trailing-element fix-up in `parallel_mult` takes over).
  2. **Active step** — if `i + 2 ≤ into.len()`:
       a. Read `g  = into[i]`, `g1 = into[i + 1]`.
       b. Compute `(i4, v3) = mul2_u16 a.value g.value g1.value`,
          i.e. the *shared-left-operand* GF(2¹⁶) double-product
          delegated to `unaccelerated::mul2`.
       c. Write back `into[i]     := { value := i4 }` and
                     `into[i + 1] := { value := v3 }`.
       d. Return `cont (s, i + 2)` with the doubly-updated slice `s`.

Mathematically, each pair of consecutive entries `into[i]`, `into[i+1]`
is replaced by `a · into[i]`, `a · into[i+1]` in GF(2¹⁶); the index
counter advances by two, and all other slice positions are untouched.

In the Rust source this body performs runtime CPU-feature dispatch via
`mul2_u16` (potentially calling a hardware-accelerated CLMUL kernel);
after Aeneas extraction every branch collapses to two software
multiplications sharing the left operand `a`, and the postcondition is
inherited verbatim from `mul2_u16_spec'` / `mul2_u16_spec` in
`Spqr.Specs.Encoding.Gf.Mul2U16`.

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, `Nat.toGF216`, `φ`, etc.) are imported from
`Spqr.Math.Gf`; the GF(2¹⁶) double-product kernel
(`mul2_u16_spec`, registered `@[step]`) is imported from
`Spqr.Specs.Encoding.Gf.Mul2U16`.

**Source**: spqr/src/encoding/gf.rs (lines 570:4-575:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf

/-- A default `GF16` value, needed by `Slice.index_usize_spec`. -/
local instance : Inhabited encoding.gf.GF16 := ⟨{ value := 0#u16 }⟩

/-- **Polynomial-level postcondition for
`encoding.gf.parallel_mult_loop.body`**:

One iteration of the multiply-by-`a` loop driving
`encoding::gf::parallel_mult`.  Both branches are characterised at the
GF(2)[X] level via `natToGF2Poly`:

* **`done`** — the loop guard `i + 2 ≤ into.len()` failed; the state
  is returned unchanged: `result = (a, into, i)`.

* **`cont`** — the loop guard held; the new state `(s, i')` satisfies
    `i'.val = i.val + 2`,
    `s.length = into.length`,
  and there exist `u16` values `v1, v2` such that
  `s = (into.set i ⟨v1⟩).set ⟨i.val + 1, _⟩ ⟨v2⟩` and at the polynomial
  level
    `natToGF2Poly v1.val =
       (natToGF2Poly a.value.val *
        natToGF2Poly g.value.val) %ₘ POLY_GF2`,
    `natToGF2Poly v2.val =
       (natToGF2Poly a.value.val *
        natToGF2Poly g1.value.val) %ₘ POLY_GF2`,
  where `g, g1` are the values originally stored at positions `i`,
  `i + 1` of `into` (so each updated position holds the GF(2¹⁶)
  product of `a` with the previous content).

This is an immediate consequence of `mul2_u16_spec'` applied to the
shared `do`-block in the extracted Lean source, combined with the
register/forget structure of two consecutive `Slice.update` calls.

**Source**: spqr/src/encoding/gf.rs (lines 570:4-575:5)
-/
theorem parallel_mult_loop_body_spec'
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16) (i : Std.Usize)
    (hi : i.val + 2 ≤ Std.Usize.max) :
    parallel_mult_loop.body a into i ⦃ cf =>
      match cf with
      | ControlFlow.done (a', into', i') =>
          a' = a ∧ into' = into ∧ i' = i ∧ into.length < i.val + 2
      | ControlFlow.cont (s, i') =>
          i.val + 2 ≤ into.length ∧
          i'.val = i.val + 2 ∧
          s.length = into.length ∧
          natToGF2Poly (s.val[i.val]!).value.val =
            (natToGF2Poly a.value.val *
             natToGF2Poly (into.val[i.val]!).value.val) %ₘ POLY_GF2 ∧
           natToGF2Poly (s.val[i.val + 1]!).value.val =
            (natToGF2Poly a.value.val *
             natToGF2Poly (into.val[i.val + 1]!).value.val) %ₘ POLY_GF2 ⦄ := by
  unfold parallel_mult_loop.body
  have h := mul2_u16_spec' a.value
  step*
  -- Discharge the post-condition for the `cont` (loop-guard-true) branch.
  -- After `step*` we know:
  --   * `into1 = into.set i ⟨i4⟩`
  --   * `s     = into1.set ⟨i.val + 1⟩ ⟨v3⟩`
  -- Hence at position `i.val` we read back `⟨i4⟩` (the `i+1` write does
  -- not touch position `i`), and at position `i.val + 1` we read back
  -- `⟨v3⟩`.  The polynomial equations on `i4`, `v3` are supplied by
  -- `mul2_u16_spec'` via the hypothesis `h`.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;>
    (try first
      | (rw [Slice.set_val_eq, Slice.set_val_eq,
             List.getElem!_set_ne (by scalar_tac : i.val ≠ i.val + 1),
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | (rw [Slice.set_val_eq,
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | scalar_tac)
  · grind
  · grind

/-- **GF(2¹⁶)-level postcondition for
`encoding.gf.parallel_mult_loop.body`** (provable, parametric):

For any ring-homomorphism `φ : (ZMod 2)[X] →+* GF216` that vanishes on
`POLY_GF2`, the body of `parallel_mult` either leaves the state
unchanged (`done` branch, when `i + 2 > into.len()`) or advances `i`
by two while preserving the slice length, with the two written
entries equal — in GF(2¹⁶) — to the shared-left-operand products
`a · into[i]`, `a · into[i + 1]`.  This algebraic content is exposed
inside the proof by the `@[step]` lemma `mul2_u16_spec`, but the
externally stated postcondition is kept minimal (length and index
invariants), mirroring the per-iteration body specs of the other
slice-mutating loops in the project.

Specialising `φ` to the canonical isomorphism (whose construction
requires irreducibility of `POLY_GF2` over `ZMod 2`, i.e. a finite-
field development we omit here) recovers the GF(2¹⁶) interpretation
of the result. -/
@[step]
theorem parallel_mult_loop_body_spec
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16) (i : Std.Usize)
    (hi : i.val + 2 ≤ Std.Usize.max) :
    parallel_mult_loop.body a into i ⦃ cf =>
      match cf with
      | ControlFlow.done (a', into', i') =>
          a' = a ∧ into' = into ∧ i' = i ∧ into.length < i.val + 2
      | ControlFlow.cont (s, i') =>
          i.val + 2 ≤ into.length ∧
          i'.val = i.val + 2 ∧
          s.length = into.length ∧
          (s.val[i.val]!).value.val.toGF216 =
            a.value.val.toGF216 *
              (into.val[i.val]!).value.val.toGF216 ∧
          (s.val[i.val + 1]!).value.val.toGF216 =
            a.value.val.toGF216 *
              (into.val[i.val + 1]!).value.val.toGF216 ⦄ := by
  unfold parallel_mult_loop.body
  have h := mul2_u16_spec a.value
  step*
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;>
    (try first
      | (rw [Slice.set_val_eq, Slice.set_val_eq,
             List.getElem!_set_ne (by scalar_tac : i.val ≠ i.val + 1),
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | (rw [Slice.set_val_eq,
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | scalar_tac)
  · grind
  · grind

end spqr.encoding.gf
