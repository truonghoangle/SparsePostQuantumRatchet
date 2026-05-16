/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.Mul2U16
import Spqr.Specs.Encoding.Gf.GF16.MulAssign
/-!
# Spec Theorem for `encoding::gf::parallel_mult` — loop body 0

One call to the body with state `(a, into, i)` performs the following computation:

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

Mathematically, each pair of consecutive entries `into[i]`, `into[i+1]` is replaced by `a ·
into[i]`, `a · into[i+1]` in GF(2¹⁶); the index counter advances by two, and all other slice
positions are untouched.

**Source**: spqr/src/encoding/gf.rs (lines 570:4-575:5)
-/

open Aeneas Aeneas.Std Result Polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.gf

local instance : Inhabited encoding.gf.GF16 := ⟨{ value := 0#u16 }⟩

/--
**Polynomial-level postcondition for `encoding.gf.parallel_mult_loop.body`**:

One iteration of the multiply-by-`a` loop driving `encoding::gf::parallel_mult`.  Both branches are
characterised at the GF(2)[X] level via `natToBinaryPoly`:

* **`done`** — the loop guard `i + 2 ≤ into.len()` failed; the state is returned unchanged: `result
  = (a, into, i)`.

* **`cont`** — the loop guard held; the new state `(s, i')` satisfies
    `i'.val = i.val + 2`,
    `s.length = into.length`,
  and there exist `u16` values `v1, v2` such that
  `s = (into.set i ⟨v1⟩).set ⟨i.val + 1, _⟩ ⟨v2⟩` and at the polynomial
  level
    `natToBinaryPoly v1.val =
       (natToBinaryPoly a.value.val *
        natToBinaryPoly g.value.val) %ₘ polyGF2`,
    `natToBinaryPoly v2.val =
       (natToBinaryPoly a.value.val *
        natToBinaryPoly g1.value.val) %ₘ polyGF2`,
  where `g, g1` are the values originally stored at positions `i`,
  `i + 1` of `into` (so each updated position holds the GF(2¹⁶)
  product of `a` with the previous content).

This is an immediate consequence of `mul2_u16_spec'` applied to the shared `do`-block in the
extracted Lean source, combined with the register/forget structure of two consecutive `Slice.update`
calls.

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
          natToBinaryPoly (s.val[i.val]!).value.val =
            (natToBinaryPoly a.value.val *
             natToBinaryPoly (into.val[i.val]!).value.val) %ₘ polyGF2 ∧
           natToBinaryPoly (s.val[i.val + 1]!).value.val =
            (natToBinaryPoly a.value.val *
             natToBinaryPoly (into.val[i.val + 1]!).value.val) %ₘ polyGF2 ⦄ := by
  unfold parallel_mult_loop.body
  have h := mul2_u16_spec' a.value
  step*
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (try first
      | (rw [Slice.set_val_eq, Slice.set_val_eq,
             List.getElem!_set_ne (by scalar_tac : i.val ≠ i.val + 1),
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | (rw [Slice.set_val_eq,
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | scalar_tac)
  · grind
  · grind

/--
**GF(2¹⁶)-level postcondition for `encoding.gf.parallel_mult_loop.body`** (provable, parametric):

For any ring-homomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` that vanishes on `polyGF2`,
the body of `parallel_mult` either leaves the state unchanged (`done` branch, when `i + 2 >
into.len()`) or advances `i` by two while preserving the slice length, with the two written entries
equal — in GF(2¹⁶) — to the shared-left-operand products `a · into[i]`, `a · into[i + 1]`.

Additionally, the **frame condition** asserts that all slice elements outside `{i, i+1}` are left
unchanged by the body, which is critical for the value-level loop invariant in
`parallel_mult_loop_spec`.

Specialising `BinaryPoly.toGF216` to the canonical isomorphism (whose construction requires
irreducibility of `polyGF2` over `ZMod 2`, i.e. a finite- field development we omit here) recovers
the GF(2¹⁶) interpretation of the result.
-/
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
          (s.val[i.val]!).toGF216 =
            a.toGF216 *
              (into.val[i.val]!).toGF216 ∧
          (s.val[i.val + 1]!).toGF216 =
            a.toGF216 *
              (into.val[i.val + 1]!).toGF216 ∧
          (∀ j : Nat, j ≠ i.val → j ≠ i.val + 1 →
            s.val[j]! = into.val[j]!) ⦄ := by
  unfold parallel_mult_loop.body
  have h := mul2_u16_spec a.value
  step*
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;>
    (try first
      | (rw [Slice.set_val_eq, Slice.set_val_eq,
             List.getElem!_set_ne (by scalar_tac : i.val ≠ i.val + 1),
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | (rw [Slice.set_val_eq,
             List.getElem!_set_self (by simp [Slice.length] at *; scalar_tac)])
      | scalar_tac)
  · simp_all[GF16.toGF216]
    grind
  · simp_all[GF16.toGF216]
    grind


/-!
# Spec theorem for `spqr::encoding::gf::parallel_mult` — loop 0

The `while i + 2 <= into.len()` loop in the Rust source (lines 570–575) processes the slice in
strides of two, computing

  `(into[i], into[i+1]) :=
       mul2_u16(a.value, into[i].value, into[i+1].value)`

and advancing `i += 2`.  When the loop terminates (`i + 2 > into.len()`), any trailing odd element
is handled separately by `parallel_mult` itself (outside this loop).

The loop is proved terminating with the natural-number measure `into.length − i.val`, which strictly
decreases by (at least) 2 every active iteration while the guard `i + 2 ≤ into.length` holds.  The
proof proceeds by `loop.spec_decr_nat`, appealing to the per-iteration step lemma
`parallel_mult_loop_body_spec` (registered `@[step]` in
`Spqr.Specs.Encoding.Gf.ParallelMultLoopBody`).

The postcondition characterises the three components of the returned triple `(a', into', i')`:

  * `a' = a` — the multiplier is threaded through unchanged.
  * `into'.length = into.length` — the slice length is preserved.
  * `into.length < i'.val + 2` — the loop has terminated: no
    more consecutive pairs remain.
  * `i.val ≤ i'.val ≤ into'.length` — the index only grew and
    stayed in bounds.
  * For every index `j` in `[i.val, i'.val)`, the GF(2¹⁶) value
    at position `j` of the result slice equals `a · into[j]`, the
    product of `a` with the original element.
  * For every index `j` in `[i'.val, into'.length)`, the element
    is unchanged from the original slice.
  * For every index `j` in `[0, i.val)`, the element is unchanged
    from the original slice.

These structural and value invariants, together with the per-step mathematical content of
`parallel_mult_loop_body_spec`, are sufficient for the caller (`parallel_mult_spec`) to derive the
full GF(2¹⁶)-level postcondition: every element of the returned slice is the product `a · original`
in GF(2¹⁶).

**Source**: spqr/src/encoding/gf.rs (lines 570:4-575:5)
-/

/--
**Spec theorem for `encoding.gf.parallel_mult_loop`**:

• The function always succeeds (no panic / overflow) provided `into.length + 2 ≤ Std.Usize.max`
  (mirrors the Rust `#[requires(into.len() <= usize::MAX - 2)]`) and `i.val ≤ into.length`.
• The returned multiplier `a'` equals the original `a` (the multiplier is never mutated by the
  loop).
• The returned slice has the same length as the input slice.
• On exit, `into.length < i'.val + 2`, meaning no further pair of elements can be processed.
• The final index satisfies `i.val ≤ i'.val ≤ into'.length`.
• Every element at index `j ∈ [i.val, i'.val)` in the returned
  slice satisfies the GF(2¹⁶) product relation:
    `into'[j].value.val.toGF216 = a.value.val.toGF216 * into[j].value.val.toGF216`
• Every element at index `j ∈ [i'.val, into'.length)` is unchanged from the original:  `into'[j] =
  into[j]`.
• Every element at index `j < i.val` is unchanged from the original:  `into'[j] = into[j]`.

**Source**: spqr/src/encoding/gf.rs (lines 570:4-575:5)
-/
@[step]
theorem parallel_mult_loop_spec
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16) (i : Std.Usize)
    (hlen : into.length + 2 ≤ Std.Usize.max) (hi : i.val ≤ into.length) :
    parallel_mult_loop a into i ⦃ (a', into', i') =>
      a' = a ∧
      into'.length = into.length ∧
      into.length < i'.val + 2 ∧
      i.val ≤ i'.val ∧
      i'.val ≤ into'.length ∧
      (∀ j : Nat, i.val ≤ j → j < i'.val →
        (into'.val[j]!).toGF216 = a.toGF216 * (into.val[j]!).toGF216) ∧
      (∀ j : Nat, i'.val ≤ j → j < into'.length →
        (into'.val[j]!) = (into.val[j]!)) ∧
      (∀ j : Nat, j < i.val →
        (into'.val[j]!) = (into.val[j]!)) ⦄ := by
  unfold parallel_mult_loop
  apply loop.spec_decr_nat
    (measure := fun (p : (Slice encoding.gf.GF16) × Std.Usize) =>
      p.1.length - p.2.val)
    (inv := fun (p : (Slice encoding.gf.GF16) × Std.Usize) =>
      p.1.length = into.length ∧
      i.val ≤ p.2.val ∧
      p.2.val ≤ p.1.length ∧
      (∀ j : Nat, i.val ≤ j → j < p.2.val →
        (p.1.val[j]!).toGF216 = a.toGF216 * (into.val[j]!).toGF216) ∧
      (∀ j : Nat, p.2.val ≤ j → j < p.1.length →
        (p.1.val[j]!) = (into.val[j]!)) ∧
      (∀ j : Nat, j < i.val →
        (p.1.val[j]!) = (into.val[j]!)))
  · rintro ⟨into', i'⟩ ⟨hlen', hi_le, hi_bound, hval_proc, hval_unproc, hval_before⟩
    simp only [] at *
    have hi' : i'.val + 2 ≤ Std.Usize.max := by omega
    step*
    split
    · simp_all
      grind
    · refine ⟨?measure, ?len, ?lo, ?proc, ?unproc, ?before, ?decr⟩
      case measure => simp_all
      case len => simp_all; grind
      case lo => simp_all
      case proc =>
        intro j hj_lo hj_hi
        by_cases hji : j = i'.val
        · subst hji; simp_all
          have := hval_unproc i'.val (le_refl _) (by grind)
          grind
        · by_cases hjip1 : j = i'.val + 1
          · subst hjip1; simp_all
            have := hval_unproc (i'.val + 1) (by omega) (by omega)
            grind
          · have hj_lt : j < i'.val := by omega
            simp_all
      case unproc =>
        intro j hj_lo hj_hi
        have hne1 : j ≠ i'.val := by omega
        have hne2 : j ≠ i'.val + 1 := by omega
        have hunproc := hval_unproc j (by omega) (by omega)
        simp_all
        have hf := r_post.2.2.2.2.2 j hne1 hne2
        simp_all
      case before =>
        intro j hj
        have hne1 : j ≠ i'.val := by omega
        have hne2 : j ≠ i'.val + 1 := by omega
        have hf := r_post.2.2.2.2.2 j hne1 hne2
        have hb := hval_before j (by omega)
        simp_all
      case decr => simp_all; omega
  · exact ⟨rfl, le_refl _, hi,
           fun _ h1 h2 => absurd h2 (by grind),
           fun j h1 h2 => rfl,
           fun j hj => rfl⟩

/-!
# Spec theorem for `spqr::encoding::gf::parallel_mult`

The function processes the slice in two phases:

  1. **Pair loop** — iterates in strides of two, calling
     `mul2_u16(a.value, into[i].value, into[i+1].value)` on each
     consecutive pair to perform the shared-left-operand GF(2¹⁶)
     double-product.  This is driven by `parallel_mult_loop` (the
     Aeneas-extracted `loop` fixed-point, specified in
     `Spqr.Specs.Encoding.Gf.ParallelMultLoop0`).

  2. **Trailing element** — if the slice has odd length, the
     remaining element `into[i]` is multiplied by `a` via the
     by-value `MulAssign<GF16> for GF16`
     (`CoreOpsArithMulAssignGF16.mul_assign`), which delegates to
     the by-reference `MulAssign<&GF16> for GF16` and ultimately
     to `unaccelerated.mul`.

The postconditions are:

  1. **Length preservation**: the returned slice has the same length
     as the input slice, matching the Rust
     `#[ensures(|_| future(into).len() == into.len())]` annotation.

  2. **Pointwise GF(2¹⁶) multiplication**: every element of the
     returned slice equals the product of `a` with the corresponding
     original element in GF(2¹⁶):
       `∀ j < result.length,
         result[j].value.val.toGF216 =
           a.value.val.toGF216 * into[j].value.val.toGF216`

In the Rust source, `mul2_u16` may dispatch to hardware-accelerated carry-less multiplication
(CLMUL/PMULL) on supported architectures; the extracted Lean version contains only the software
fallback.

**Source**: spqr/src/encoding/gf.rs (lines 566:0-579:1)
-/

/--
**Spec theorem for `encoding.gf.parallel_mult`**:

• The function always succeeds (no panic / overflow) provided `into.length + 2 ≤ Std.Usize.max`
  (mirrors the Rust `#[requires(into.len() <= usize::MAX - 2)]`).
• The returned slice has the same length as the input:
    `result.length = into.length`
  matching the Rust `#[ensures]` annotation.
• Every element of the returned slice is the GF(2¹⁶) product of
  the multiplier `a` with the corresponding original element:
    `∀ j < result.length,
       result[j].value.val.toGF216 =
         a.value.val.toGF216 * into[j].value.val.toGF216`

**Source**: spqr/src/encoding/gf.rs (lines 566:0-579:1)
-/
@[step]
theorem parallel_mult_spec
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16)
    (hlen : into.length + 2 ≤ Std.Usize.max) :
    parallel_mult a into ⦃ (result : Slice encoding.gf.GF16) =>
      result.length = into.length ∧
      (∀ j : Nat, j < result.length →
        ((result.val[j]!).toGF216 : GF216) =
          a.toGF216 * ((into.val[j]!).toGF216 : GF216)) ⦄ := by
  unfold parallel_mult
  step*
  constructor
  · simp_all
  · intro j hj
    set i:=a.2.2
    have hj_loop : j < i ∨ j ≥ i := Nat.lt_or_ge j i
    rcases hj_loop with hj1 | hj2
    · have :=hterm.2.2.2.2.2.1 j (by simp)  hj1
      simp_all only [Slice.length, le_refl, List.getElem!_eq_getElem?_getD,
      Slice.set_val_eq, List.length_set, zero_le,
      forall_const, getElem!_pos, not_lt_zero, IsEmpty.forall_iff,
      and_true, true_and, UScalar.lt_equiv,
      Usize.ofNatCore_val_eq, getElem?_pos, Option.getD_some]
      rw[← this]
      congr 1
      have : (↑i : Nat) ≠ j:= by omega
      simp [this]
    · have : j< ha1.2.1.length := by
        simp_all
      have :=hterm.2.2.2.2.2.2.1 j (by simp[hj2])  this
      have hji : j = ↑i := by
        have := hterm.2.2.1
        have := hterm.2.1
        simp_all
        omega
      subst hji
      simp_all [mul_comm]


end spqr.encoding.gf
