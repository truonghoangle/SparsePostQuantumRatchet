/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.ParallelMultLoopBody

/-! # Spec Theorem for `spqr::encoding::gf::parallel_mult` — loop 0

Specification and proof for
`encoding.gf.parallel_mult_loop`, the Aeneas-extracted `loop`
fixed-point that drives the main loop of `parallel_mult`.  It
iterates `parallel_mult_loop.body` to multiply every pair of
consecutive GF(2¹⁶) elements in a mutable slice by a shared
factor `a`.

The `while i + 2 <= into.len()` loop in the Rust source
(lines 570–575) processes the slice in strides of two, computing

  `(into[i], into[i+1]) :=
       mul2_u16(a.value, into[i].value, into[i+1].value)`

and advancing `i += 2`.  When the loop terminates
(`i + 2 > into.len()`), any trailing odd element is handled
separately by `parallel_mult` itself (outside this loop).

The loop is proved terminating with the natural-number measure
`into.length − i.val`, which strictly decreases by (at least) 2
every active iteration while the guard `i + 2 ≤ into.length`
holds.  The proof proceeds by `loop.spec_decr_nat`, appealing
to the per-iteration step lemma `parallel_mult_loop_body_spec`
(registered `@[step]` in
`Spqr.Specs.Encoding.Gf.ParallelMultLoopBody`).

The postcondition characterises the three components of the
returned triple `(a', into', i')`:

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

These structural and value invariants, together with the per-step
mathematical content of `parallel_mult_loop_body_spec`, are
sufficient for the caller (`parallel_mult_spec`) to derive the
full GF(2¹⁶)-level postcondition: every element of the returned
slice is the product `a · original` in GF(2¹⁶).

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, `Nat.toGF216`, `φ`, etc.) are imported from
`Spqr.Math.Gf`; the per-iteration GF(2¹⁶) double-product kernel
(`parallel_mult_loop_body_spec`, registered `@[step]`) is
imported from `Spqr.Specs.Encoding.Gf.ParallelMultLoopBody`.

**Source**: spqr/src/encoding/gf.rs (lines 570:4-575:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf

/-- A default `GF16` value, needed by `Slice.index_usize_spec`. -/
local instance : Inhabited encoding.gf.GF16 := ⟨{ value := 0#u16 }⟩

/-
natural language description:

• Receives the loop state: multiplier `a : GF16`, mutable slice
  `into : Slice GF16`, and loop counter `i : usize`.
• Iterates `parallel_mult_loop.body a` until termination:
    - Each active step reads `into[i]`, `into[i+1]`, computes the
      double-product `mul2_u16(a.value, into[i].value, into[i+1].value)`,
      writes the two results back, and advances `i` by 2.
    - When `i + 2 > into.len()`, the body returns `done (a, into, i)`,
      ending the iteration.
• Returns the triple `(a, into', i')` where `into'` is the
  pairwise-multiplied slice and `i'` is the index at which the
  loop stopped.

natural language specs:

• The function always succeeds (no panic / overflow) provided
  `into.length + 2 ≤ Std.Usize.max` (mirrors the Rust
  `#[requires(into.len() <= usize::MAX - 2)]`) and
  `i.val ≤ into.length`.
• The returned multiplier `a'` equals the original `a` (the
  multiplier is never mutated by the loop).
• The returned slice has the same length as the input slice.
• On exit, `into.length < i'.val + 2`, meaning no further
  pair of elements can be processed.
• The final index satisfies `i.val ≤ i'.val ≤ into'.length`.
• Every element at index `j ∈ [i.val, i'.val)` in the returned
  slice satisfies the GF(2¹⁶) product relation:
    `into'[j].value.val.toGF216 = a.value.val.toGF216 * into[j].value.val.toGF216`
• Every element at index `j ∈ [i'.val, into'.length)` is
  unchanged from the original:  `into'[j] = into[j]`.
• Every element at index `j < i.val` is unchanged from the
  original:  `into'[j] = into[j]`.
-/

/-- **Spec and proof concerning `encoding.gf.parallel_mult_loop`**:

The `loop` fixed-point driving `parallel_mult`, proved via
`loop.spec_decr_nat` with measure `into.length − i.val` and the
structural invariant that the slice length is preserved and the
index stays within `[i₀ .. into.length]`.

The result satisfies:

  `a' = a`,
  `into'.length = into.length`,
  `into.length < i'.val + 2`   (termination),
  `i.val ≤ i'.val ≤ into'.length`,
  `∀ j ∈ [i.val, i'.val), into'[j].value.val.toGF216 =
  a.value.val.toGF216 * into[j].value.val.toGF216`,
  `∀ j ∈ [i'.val, into'.length), into'[j] = into[j]`,
  `∀ j < i.val, into'[j] = into[j]`.

The proof unfolds `parallel_mult_loop` to expose the `loop`
combinator, then applies `loop.spec_decr_nat` with a
length-preservation / index-bounds / value-level invariant.
Each step is discharged by `step*` (which invokes the registered
`parallel_mult_loop_body_spec`), followed by `simp_all` and
`omega` for the arithmetic obligations in each branch.

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
        (into'.val[j]!).value.val.toGF216 =
          a.value.val.toGF216 * (into.val[j]!).value.val.toGF216) ∧
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
        (p.1.val[j]!).value.val.toGF216 =
          a.value.val.toGF216 * (into.val[j]!).value.val.toGF216) ∧
      (∀ j : Nat, p.2.val ≤ j → j < p.1.length →
        (p.1.val[j]!) = (into.val[j]!)) ∧
      (∀ j : Nat, j < i.val →
        (p.1.val[j]!) = (into.val[j]!)))
  · -- Step: show that each body call either terminates with the
    -- postcondition (`done`) or continues with a strictly smaller
    -- measure and the invariant maintained (`cont`).
    rintro ⟨into', i'⟩ ⟨hlen', hi_le, hi_bound, hval_proc, hval_unproc, hval_before⟩
    simp only [] at *
    -- Provide the body spec's side condition i'.val + 2 ≤ Usize.max.
    have hi' : i'.val + 2 ≤ Std.Usize.max := by omega
    step*
    split
    · -- `done` branch: loop guard `i' + 2 ≤ into'.length` failed;
      -- state returned unchanged.  The value properties follow
      -- directly from the invariant via `simp_all`.
      simp_all
    · -- `cont` branch: loop guard held; index advanced by 2,
      -- slice length preserved, measure strictly decreased.
      -- The body spec gives us (via `step*`):
      --   * guard, index, length, GF216 values, frame condition
      -- Combined with the invariant, we maintain all properties.
      --
      -- After `step*`, the goal structure is:
      --   ⊢ measure_decrease ∧ ⟨length, bounds, processed, unprocessed, before⟩
      -- We use `refine` to split all conjuncts at once.
      refine ⟨?measure, ?len, ?lo, ?proc, ?unproc, ?before, ?decr⟩
      case measure => simp_all
      case len => simp_all; grind
      case lo => simp_all
      case proc =>
        intro j hj_lo hj_hi
        -- Body spec hypotheses are anonymous; access them via `‹_›`
        -- or let `simp_all` use them.
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
        -- Extract and specialize the frame condition from body spec
        -- (which is in getD form); the second simp_all converts to getElem form
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
  · -- Initial state satisfies the invariant.
    exact ⟨rfl, le_refl _, hi,
           fun _ h1 h2 => absurd h2 (by grind),
           fun j h1 h2 => rfl,
           fun j hj => rfl⟩

end spqr.encoding.gf
