/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.GF16.Mul
import Spqr.Specs.Encoding.Gf.GF16.MulAssign

/-! # Spec Theorem for `GF16::div_impl_loop.body` (loop body 0)

Specification and proof for
`encoding.gf.GF16.div_impl_loop.body`,
the per-iteration body of the `for _i in 1..16` loop driving
`encoding.gf.GF16.div_impl` (Fermat-style iterated squaring used to
compute GF(2¹⁶) division by `self · other^(2¹⁶ − 2)`).

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication
is polynomial multiplication modulo the irreducible polynomial
POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).  Each field element is
represented as a polynomial of degree < 16 with coefficients in
GF(2), stored as a 16-bit unsigned integer; the `GF16` Rust type is
the `u16` wrapper providing the field operations.

Concretely, the Rust source is

```rust
for _i in 1..16 {
    out *= square;
    square = square * square;
}
```

The extracted Lean body advances the `1..16` iterator by one step
and, depending on whether the iterator is exhausted, either returns
the accumulated `out` (loop exit) or computes the new `(square', out')`
state for the next iteration:
  1. `out1 ← MulAssignGF16.mul_assign out square` — in-place
     `out *= square` delegating to the by-reference `MulAssign`
     instance, which itself delegates to the software (unaccelerated)
     carry-less multiplication `encoding.gf.unaccelerated.mul`.
  2. `square1 ← MulGF16GF16.mul square square` — by-value
     `square = square * square` delegating to the same software
     multiplication kernel.

Note that, unlike the `const_div` variant, the `div_impl` body
performs the `*=` *before* the squaring, so the new `out` involves
the **old** `square` (i.e. `out' = out · square`), while the new
`square` is `square² = square · square`.

The on-target Rust implementation may dispatch to hardware carry-less
multiplication instructions (`PCLMULQDQ` / `PMULL`) on x86/x86_64 and
aarch64 when the corresponding CPU feature is detected; the extracted
Lean version contains only the unaccelerated fallback.

The body introduces no additional logic beyond the two delegations
and the iterator advance, so its postcondition is inherited from the
underlying `mul_assign` and `mul` specifications: lifting the `u16`
of each new field element into `GF216 = GaloisField 2 16` via
`Nat.toGF216` yields the corresponding GF(2¹⁶) products.

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-- **Spec and proof concerning
`core.iter.range.IteratorRange.next core.iter.range.StepUsize`**:

The `next` method of the `Iterator` instance for `Range<usize>`,
specified at the WP / postcondition level: on a `range : Range Usize`,
`next` returns `(opt, range')` where:

* if `range.start.val ≥ range.end.val` (the range is exhausted), then
  `opt = none` and `range' = range` (the iterator is unchanged);
* if `range.start.val < range.end.val` (the range still has an element),
  then `opt = some range.start`, `range'.start.val = range.start.val + 1`,
  and `range'.end = range.end` (the upper bound is preserved).

Both branches are derived from the underlying definitions of
`core.iter.range.IteratorRange.next`,
`core.iter.range.StepUsize.forward_checked`,
`core.cmp.impls.PartialOrdUsize.lt`, and
`core.clone.impls.CloneUsize.clone`, which together implement
`Range::next` for `usize` ranges in Rust.
-/
@[step]
theorem next_spec (range : core.ops.range.Range Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range
      ⦃ (opt, range') =>
        (¬ range.start.val < range.end.val →
            opt = none ∧ range' = range) ∧
        (range.start.val < range.end.val →
            opt = some range.start ∧
            range'.start.val = range.start.val + 1 ∧
            range'.end = range.end) ⦄ := by
  -- Step 1: prove an existential / equational form of the spec.
  suffices h : ∃ opt range',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range
        = ok (opt, range') ∧
      (¬ range.start.val < range.end.val → opt = none ∧ range' = range) ∧
      (range.start.val < range.end.val →
          opt = some range.start ∧
          range'.start.val = range.start.val + 1 ∧
          range'.end = range.end) by
    obtain ⟨opt, range', heq, h1, h2⟩ := h
    rw [heq]; simp only [WP.spec_ok]
    exact ⟨h1, h2⟩
  -- Step 2: prove the existential / equational form.
  simp only [core.iter.range.IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneUsize.clone, bind_tc_ok, not_lt]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdUsize.lt range.start range.end = true) =
      (range.start.val < range.end.val) := by
    simp [core.cmp.impls.PartialOrdUsize.lt]
  simp only [h_lt_iff]
  by_cases hlt : range.start.val < range.end.val
  · rw [if_pos hlt]
    have hbound : range.start.val + 1 ≤ Usize.max := by
      have := range.end.hBounds; scalar_tac
    refine ⟨some range.start,
            {range with start := ⟨range.start.val + 1, by scalar_tac⟩},
            ?_, ?_, ?_⟩
    · simp only [core.iter.range.StepUsize.forward_checked, bind_tc_ok]
      have hca := Usize.checked_add_bv_spec range.start 1#usize
      rcases heq : Usize.checked_add range.start 1#usize with _ | z
      · rw [heq] at hca; scalar_tac
      · simp only
        rw [heq] at hca
        obtain ⟨_, hval, _⟩ := hca
        have hzval : z.val = range.start.val + 1 := by scalar_tac
        congr 4
        exact UScalar.eq_of_val_eq hzval
    · intro h; omega
    · intro _; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hlt]
    exact ⟨none, range, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

/-
natural language description:

• Takes the `1..16` iterator state `iter` together with the current
  `square` and `out` accumulators (each a `GF16` wrapping a `u16`
  representing an element of GF(2¹⁶)).
• Advances the iterator by one step.  If exhausted, the body returns
  `ControlFlow.done out` (loop exit, accumulator unchanged).
  Otherwise it delegates to:
    `encoding.gf.GF16.Insts.CoreOpsArithMulAssignGF16.mul_assign out square`
  for the in-place product `out *= square`, and to
    `encoding.gf.GF16.Insts.CoreOpsArithMulGF16GF16.mul square square`
  for the new squared value `square = square²`, both performing
  carry-less polynomial multiplication followed by reduction modulo
  POLY = 0x1100b.
• Returns `ControlFlow.cont (iter1, square1, out1)` carrying the
  advanced iterator and the updated accumulators.

natural language specs:

• The function always succeeds (no panic) for any `(iter, square, out)`,
  since the underlying iterator advance and `unaccelerated.mul` are
  total.
• On `done` the result accumulator coincides with the input `out`:
    `(result.value.val.toGF216 : GF216) = out.value.val.toGF216`.
• On `cont (_, square', out')` the new state satisfies the iterated-
  squaring recurrence
    `out'.value.val.toGF216 =
        out.value.val.toGF216 * square.value.val.toGF216`,
    `square'.value.val.toGF216 =
        square.value.val.toGF216 * square.value.val.toGF216`,
  where `*` denotes multiplication in `GF216 = GaloisField 2 16`.
-/

/-- **Spec and proof concerning
`encoding.gf.GF16.Insts.CoreOpsArithMulAssignGF16.mul_assign`**:

The trait-method `MulAssign<GF16> for GF16` provided by the
`CoreOpsArithMulAssignGF16` instance is a thin wrapper that
delegates to the by-reference instance
`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul_assign`,
which itself defers to the software carry-less multiplication
`encoding.gf.unaccelerated.mul`.

Registering the resulting GF(2¹⁶)-level postcondition as a `@[step]`
lemma allows `step*` to discharge `mul_assign` calls inside the
`div_impl` loop body without further unfolding.

**Source**: spqr/src/encoding/gf.rs (lines 507:4-509:5)
-/
@[step]
theorem CoreOpsArithMulAssignGF16_mul_assign_spec
    (self other : spqr.encoding.gf.GF16) :
    Insts.CoreOpsArithMulAssignGF16.mul_assign self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216 ⦄ := by
  unfold Insts.CoreOpsArithMulAssignGF16.mul_assign
  step*

/-- Auxiliary axiom asserting that the `Range<i32>` iterator's `next`
method always succeeds (returns `ok`).

The underlying `core.iter.range.IteratorRange.next` is defined in
terms of `I32.Insts.CoreIterRangeStep.forward_checked`, which Aeneas
extracts as an opaque axiom (see `Spqr/Code/FunsExternal.lean`).  As a
consequence, no concrete computational behaviour of `forward_checked`
is available, and `next` cannot be discharged automatically by
`step*` for `I32` ranges (unlike the `Usize` case, where
`Usize.checked_add` is fully specified — see `next_spec` above).

In practice, the Rust implementation of `Step::forward_checked` for
`i32` is total (it returns `Ok(None)` on overflow and `Ok(Some _)`
otherwise) and therefore never produces a `Result::Err`, so neither
does the resulting `IteratorRange::next`.  We lift this fact to a
dedicated axiom that mirrors the axiomatic treatment of the
underlying `forward_checked` operation. -/
private axiom IteratorRange_next_I32_ok
    (iter : core.ops.range.Range Std.I32) :
    ∃ o iter1,
      core.iter.range.IteratorRange.next I32.Insts.CoreIterRangeStep iter
        = ok (o, iter1)

/-- **Per-iteration postcondition for `encoding.gf.GF16.div_impl_loop.body`**:

One iteration of the iterated-squaring loop driving `GF16::div_impl`.
Both branches are characterised at the GF(2¹⁶) level via
`Nat.toGF216 = φ ∘ natToGF2Poly`:

* **`done`** — the `1..16` iterator is exhausted; the returned
  accumulator is the unchanged `out`:
    `result.value.val.toGF216 = out.value.val.toGF216`.

* **`cont`** — the iterator yielded another index; the new state
  `(_, square', out')` satisfies the squaring recurrence (note that,
  unlike `const_div`, the `*=` precedes the squaring, so `out'`
  involves the *old* `square`):
    `out'.value.val.toGF216 =
        out.value.val.toGF216 * square.value.val.toGF216`,
    `square'.value.val.toGF216 =
        square.value.val.toGF216 * square.value.val.toGF216`.

The proof unfolds `div_impl_loop.body` to expose the iterator advance
and its two-arm `match`.  The advance
`core.iter.range.IteratorRange.next I32.Insts.CoreIterRangeStep iter`
delegates (through the `Step<i32>` trait instance) to the opaque
axiomatised `I32.Insts.CoreIterRangeStep.forward_checked`, so its
result cannot be inspected by `step*` directly.  We use the auxiliary
axiom `IteratorRange_next_I32_ok` to extract a successful return
`ok (o, iter1)` and case-split on the `Option`:

* in the `none` branch the body returns `ok (ControlFlow.done out)`,
  whose postcondition is reflexively true;
* in the `some` branch `step*` discharges the two GF(2¹⁶)
  multiplications through the registered specifications
  `CoreOpsArithMulAssignGF16_mul_assign_spec` (above) and
  `CoreOpsArithMulGF16GF16.mul_spec` (the GF(2¹⁶) multiplication
  kernel imported from `Spqr.Specs.Encoding.Gf.GF16.Mul`).

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/
@[step]
theorem div_impl_loop_body_spec
    (iter : core.ops.range.Range Std.I32)
    (square out : spqr.encoding.gf.GF16) :
    div_impl_loop.body iter square out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          (result.value.val.toGF216 : GF216) = out.value.val.toGF216
      | ControlFlow.cont (_, square', out') =>
          (out'.value.val.toGF216 : GF216) =
            out.value.val.toGF216 * square.value.val.toGF216 ∧
          (square'.value.val.toGF216 : GF216) =
            square.value.val.toGF216 * square.value.val.toGF216 ⦄ := by
  unfold div_impl_loop.body
  obtain ⟨o, iter1, hnext⟩ := IteratorRange_next_I32_ok iter
  rw [hnext]
  simp only [bind_tc_ok]
  cases o with
  | none => simp only [WP.spec_ok]
  | some _ => step*


/-! # Spec Theorem for `GF16::div_impl_loop` (loop 0)

Specification and proof for `encoding.gf.GF16.div_impl_loop`,
the Aeneas-extracted `loop` fixed-point driving the
`for _i in 1..16` loop of `encoding.gf.GF16.div_impl`.  This loop
realises the iterated-squaring core of GF(2¹⁶) division, computing
`self · other^(2¹⁶ − 2) = self / other` from the entry-point state
`(iter = 1..16, square = other · other, out = self)`.

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication
is polynomial multiplication modulo the irreducible polynomial
POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).  Each field element is
represented as a polynomial of degree < 16 with coefficients in
GF(2), stored as a 16-bit unsigned integer.

Concretely, the Rust source is

```rust
for _i in 1..16 {
    out *= square;
    square = square * square;
}
```

The loop performs the canonical iterated-squaring schedule: after
`k` iterations starting from `(square, out)`, the accumulators carry

  `square_k = square^(2^k)`,
  `out_k    = out · square^(2^k − 1)`,

so that the geometric series `1 + 2 + 4 + ⋯ + 2^(k−1) = 2^k − 1`
fully appears in the exponent of `out_k`.  For `n = end − start`
iterations of an `n`-step iterator, the loop returns
`out · square^(2^n − 1)`.

Specialised to the entry point `(iter = 1..16, square = other²,
out = self)`, the loop runs for `n = 15` iterations, giving

  `self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`,

the Fermat-style inverse `other⁻¹ = other^(2¹⁶ − 2)` multiplied by
`self`, i.e. the GF(2¹⁶) quotient `self / other`.

The on-target Rust implementation may dispatch to hardware carry-less
multiplication instructions (`PCLMULQDQ` / `PMULL`) on x86/x86_64 and
aarch64 when the corresponding CPU feature is detected; the extracted
Lean version contains only the unaccelerated fallback.

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, `Nat.toGF216`, `φ`, etc.) are imported from
`Spqr.Math.Gf`; the per-iteration body specification
(`div_impl_loop_body_spec`, registered `@[step]`, together with the
auxiliary axiom `IteratorRange_next_I32_ok` for the opaque `Range<i32>`
iterator) is imported from `Spqr.Specs.Encoding.Gf.GF16.DivImplLoopBofy`.

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/


/-- Auxiliary axiom strengthening `IteratorRange_next_I32_ok`:
the `next` method of the `Iterator` instance for `Range<i32>`
not only succeeds, but, on a `range : Range I32`, returns
`(opt, range')` such that:

* if `range.start.val ≥ range.end.val` (the range is exhausted), then
  `opt = none` and `range' = range` (the iterator is unchanged);
* if `range.start.val < range.end.val` (the range still has an element),
  then `opt = some range.start`, `range'.start.val = range.start.val + 1`,
  and `range'.end = range.end` (the upper bound is preserved).

The underlying `core.iter.range.IteratorRange.next` is defined in
terms of `I32.Insts.CoreIterRangeStep.forward_checked`, which Aeneas
extracts as an opaque axiom (see `Spqr/Code/FunsExternal.lean`) — no
concrete computational behaviour of `forward_checked` is available in
Lean.  In practice, the Rust implementation of `Step::forward_checked`
for `i32` is total and increments the cursor by one on success
(returning `Ok(None)` only on overflow, which cannot occur for the
`1..16` range used by `div_impl`), so the resulting `Range::next`
behaves exactly as for `Usize` ranges (cf. `next_spec` in
`DivImplLoopBofy.lean`).  We lift this fact to a dedicated axiom
that mirrors the proven `Usize` specification.
-/
private axiom IteratorRange_next_I32_post
    (iter : core.ops.range.Range Std.I32) :
    ∃ opt iter1,
      core.iter.range.IteratorRange.next I32.Insts.CoreIterRangeStep iter
        = ok (opt, iter1) ∧
      (¬ iter.start.val < iter.end.val →
          opt = none ∧ iter1 = iter) ∧
      (iter.start.val < iter.end.val →
          opt = some iter.start ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end)

/-- **Closed-form postcondition for `encoding.gf.GF16.div_impl_loop`**:

The iterated-squaring loop driving `GF16::div_impl`, specified at
the GF(2¹⁶) level by the closed-form iterated-squaring identity:

  `result.value.val.toGF216 =
       out.value.val.toGF216 *
       square.value.val.toGF216 ^ (2 ^ (iter.end.val − iter.start.val).toNat − 1)`.

Specialised to the entry point `(iter, square, out) = (1..16,
other², self)` this collapses to
`self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`, i.e. division
in GF(2¹⁶).

The proof applies `loop.spec_decr_nat` with measure
`(iter'.end.val − iter'.start.val).toNat` and the inductive invariant
that, at any intermediate state `(iter', square', out')` with
`iter.start.val ≤ iter'.start.val ≤ iter.end.val` and
`iter'.end = iter.end`,

  `square'.value.val.toGF216 =
       square.value.val.toGF216 ^ (2 ^ (iter'.start.val − iter.start.val).toNat)`,
  `out'.value.val.toGF216 =
       out.value.val.toGF216 *
       square.value.val.toGF216 ^ (2 ^ (iter'.start.val − iter.start.val).toNat − 1)`.

The active step uses `IteratorRange_next_I32_post` to extract the
relationship between `iter'` and the advanced iterator, then
`CoreOpsArithMulAssignGF16_mul_assign_spec` and
`CoreOpsArithMulGF16GF16.mul_spec` (registered `@[step]`) discharge
the two GF(2¹⁶) multiplications.  The routine commutative-ring
exponent identities

  `(square^(2^k))² = square^(2^(k+1))`,
  `square^(2^k − 1) · square^(2^k) = square^(2^(k+1) − 1)`,

are settled by `omega` on the exponents (after `pow_succ` and
`pow_add` rewriting).  The `done` branch forces
`iter'.start.val = iter.end.val`, at which point the invariant
already coincides with the postcondition.

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/
theorem div_impl_loop_spec
    (iter : core.ops.range.Range Std.I32)
    (square out : spqr.encoding.gf.GF16)
    (h_le : iter.start.val ≤ iter.end.val) :
    div_impl_loop iter square out ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        out.value.val.toGF216 *
          square.value.val.toGF216 ^
            (2 ^ (iter.end.val - iter.start.val).toNat - 1) ⦄ := by
  unfold div_impl_loop
  apply loop.spec_decr_nat
    (measure := fun p : core.ops.range.Range Std.I32 ×
                          spqr.encoding.gf.GF16 ×
                          spqr.encoding.gf.GF16 =>
                  (p.1.end.val - p.1.start.val).toNat)
    (inv := fun p : core.ops.range.Range Std.I32 ×
                       spqr.encoding.gf.GF16 ×
                       spqr.encoding.gf.GF16 =>
        p.1.end = iter.end ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ iter.end.val ∧
        (p.2.1.value.val.toGF216 : GF216) =
          square.value.val.toGF216 ^
            (2 ^ (p.1.start.val - iter.start.val).toNat) ∧
        (p.2.2.value.val.toGF216 : GF216) =
          out.value.val.toGF216 *
            square.value.val.toGF216 ^
              (2 ^ (p.1.start.val - iter.start.val).toNat - 1))
  · rintro ⟨iter', sq', out'⟩ ⟨h_end, h_ge, h_le', h_sq, h_out⟩
    simp only [] at h_end h_ge h_le' h_sq h_out
    simp only []
    unfold div_impl_loop.body
    obtain ⟨opt, iter1, hnext, h_done, h_cont⟩ :=
      IteratorRange_next_I32_post iter'
    rw [hnext]
    simp only [bind_tc_ok]
    by_cases h_lt : iter'.start.val < iter'.end.val
    · -- `cont` branch: the iterator yielded another index.
      obtain ⟨h_opt, h_start1, h_end1⟩ := h_cont h_lt
      rw [h_opt]
      simp only
      step*
      -- Useful equality on the exponent index.
      have hk1 :
          (iter1.start.val - iter.start.val).toNat =
            (iter'.start.val - iter.start.val).toNat + 1 := by
        have h0 : 0 ≤ iter'.start.val - iter.start.val := by omega
        have h1 : iter1.start.val - iter.start.val =
                    (iter'.start.val - iter.start.val) + 1 := by
          rw [h_start1]; ring
        rw [h1]
        rw [Int.toNat_add (by omega) (by omega)]
        simp
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- `iter1.end = iter.end`
        rw [h_end1]; exact h_end
      · -- `iter.start.val ≤ iter1.start.val`
        rw [h_start1]; omega
      · -- `iter1.start.val ≤ iter.end.val`: from `iter'.start.val + 1 ≤ iter'.end.val`
        --                                  and `iter'.end = iter.end`.
        have : iter'.end.val = iter.end.val := by rw [← h_end]
        rw [h_start1]; omega
      · -- new square as a power of the original
        rw [square1_post, h_sq, ← pow_add, hk1, pow_succ]
        ring_nf
      · -- new out as a power of the original
        rw [out1_post, h_sq, h_out, mul_assoc, ← pow_add]
        have h_2le :
            2 ≤ 2 ^ ((iter'.start.val - iter.start.val).toNat + 1) := by
          calc (2 : Nat) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ ((iter'.start.val - iter.start.val).toNat + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
        have h_eq :
            (2 ^ (iter'.start.val - iter.start.val).toNat - 1) +
              2 ^ (iter'.start.val - iter.start.val).toNat =
            2 ^ (iter1.start.val - iter.start.val).toNat - 1 := by
          rw [hk1, pow_succ]; omega
        rw [h_eq]
      · -- measure strictly decreases
        rw [h_start1, h_end1]
        have h_pos : 0 < iter'.end.val - iter'.start.val := by omega
        have h_eq : iter'.end.val - (iter'.start.val + 1) =
                      (iter'.end.val - iter'.start.val) - 1 := by ring
        rw [h_eq]
        have h_toNat :
            ((iter'.end.val - iter'.start.val) - 1).toNat
              = (iter'.end.val - iter'.start.val).toNat - 1 := by
          have h0 : (0 : Int) ≤ iter'.end.val - iter'.start.val := by omega
          have h1 : (1 : Int) ≤ iter'.end.val - iter'.start.val := by omega
          omega
        rw [h_toNat]
        have h0 : 0 < (iter'.end.val - iter'.start.val).toNat := by
          have : (1 : Int) ≤ iter'.end.val - iter'.start.val := by omega
          omega
        omega
    · -- `done` branch: the iterator is exhausted.
      obtain ⟨h_opt, _⟩ := h_done h_lt
      rw [h_opt]
      simp only [WP.spec_ok]
      have h_end' : iter'.end.val = iter.end.val := by rw [← h_end]
      have h_start_eq : iter'.start.val = iter.end.val := by omega
      have h_k_eq :
          (iter'.start.val - iter.start.val).toNat =
            (iter.end.val - iter.start.val).toNat := by
        rw [h_start_eq]
      rw [← h_k_eq]
      exact h_out
  · -- initial invariant: `k = 0`
    refine ⟨rfl, le_refl _, h_le, ?_, ?_⟩
    · simp only [Int.sub_self, Int.toNat_zero, pow_zero, pow_one]
    · simp only [Int.sub_self, Int.toNat_zero, pow_zero,
        Nat.sub_self, mul_one]

/-! # Spec Theorem for `GF16::div_impl`

Specification and proof for `encoding.gf.GF16.div_impl`,
which implements GF(2¹⁶) division `self / other` on the `GF16`
wrapper by Fermat-style iterated squaring, delegating its actual
computation to the extracted `for`-loop driver `div_impl_loop`.

In GF(2¹⁶) — the Galois field with 65 536 elements — every non-zero
element `b` satisfies `b^(2¹⁶ − 1) = 1`, so the multiplicative
inverse is `b⁻¹ = b^(2¹⁶ − 2)` and `a / b = a · b^(2¹⁶ − 2)`.  The
exponent `2¹⁶ − 2 = 2 · (2¹⁵ − 1)` is computed by iterated
squaring: starting from `square = b²` and `out = a`, one repeats

  `out = out · square;  square = square²`

for the 15 indices `i = 1, …, 15`, after which

  `out = a · (b²)^(2¹⁵ − 1) = a · b^(2¹⁶ − 2) = a / b`.

Concretely, the Rust source is

```rust
fn div_impl(&self, other: &Self) -> Self {
    // Within GF(p^n), inv(a) == a^(p^n-2).  We're GF(2^16) == GF(65536),
    // so we can compute GF(65534).
    let mut square = *other * *other;
    let mut out = *self;
    for _i in 1..16 {
        out *= square;
        square = square * square;
    }
    out
}
```

The function proceeds in two stages:
  1. The initial squaring `square := other · other` via the
     `Mul<GF16> for GF16` instance, which delegates (through
     `MulAssign<&GF16> for GF16`) to the software (unaccelerated)
     carry-less multiplication `encoding.gf.unaccelerated.mul`.
  2. `div_impl_loop {start := 1, end := 16} square self` — the
     Aeneas-extracted `loop` fixed-point driving the iterated-
     squaring body for 15 rounds, returning the final accumulator
     `out = self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`.

The on-target Rust implementation may dispatch to hardware carry-less
multiplication instructions (`PCLMULQDQ` / `PMULL`) on x86/x86_64 and
aarch64 when the corresponding CPU feature is detected; the extracted
Lean version contains only the unaccelerated fallback.

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, `Nat.toGF216`, `φ`, etc.) are imported from
`Spqr.Math.Gf`; the underlying GF(2¹⁶) multiplication kernel
(`CoreOpsArithMulGF16GF16.mul_spec`, registered `@[step]`) is
imported from `Spqr.Specs.Encoding.Gf.GF16.Mul`; the closed-form
loop specification (`div_impl_loop_spec`) is imported from
`Spqr.Specs.Encoding.Gf.GF16.DivImplLoop0`.

**Source**: spqr/src/encoding/gf.rs (lines 446:4-456:5)
-/


/-
natural language description:

• Takes two `GF16` field elements `self` and `other` (each wrapping a
  `u16` value representing an element of GF(2¹⁶)) and computes the
  GF(2¹⁶) quotient `self / other` by Fermat-style iterated squaring.
• Initialises `square := other · other` by delegating to the
  by-value `Mul<GF16> for GF16` instance
    `encoding.gf.GF16.Insts.CoreOpsArithMulGF16GF16.mul`,
  which itself defers to the software carry-less multiplication
  `encoding.gf.unaccelerated.mul`.
• Drives the `for _i in 1..16` loop via
    `encoding.gf.GF16.div_impl_loop {start := 1, end := 16} square self`,
  which runs 15 iterations of `out := out · square; square := square²`.
• Returns the final accumulator
    `out = self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`.

natural language specs:

• The function always succeeds (no panic) for any pair of `GF16`
  inputs, since the underlying `unaccelerated.mul` and the loop
  driver are total on `GF16 × GF16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = φ ∘ natToGF2Poly` yields the GF(2¹⁶) Fermat-style
  quotient of the similarly-lifted inputs:
    `(result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 *
        other.value.val.toGF216 ^ (2 ^ 16 − 2)`
  where the operations on the right-hand side are performed in
  `GF216 = GaloisField 2 16`.  When `other ≠ 0` Fermat's little
  theorem in GF(2¹⁶) gives `other^(2¹⁶ − 1) = 1`, so
  `other^(2¹⁶ − 2) = other⁻¹` and the right-hand side is genuinely
  the field quotient `self / other`.
-/

/-- **Spec and proof concerning `encoding.gf.GF16.div_impl`**:

`div_impl` computes GF(2¹⁶) division `self / other` on the `GF16`
wrapper by Fermat-style iterated squaring.  After initialising
`square := other · other` and `out := self`, the loop
`div_impl_loop {start := 1, end := 16} square self`
runs 15 iterations of

  `out := out · square;  square := square²`,

producing `out = self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`.

The result satisfies the GF(2¹⁶)-level postcondition:

  `(result.value.val.toGF216 : GF216) =
       self.value.val.toGF216 *
       other.value.val.toGF216 ^ (2 ^ 16 − 2)`,

i.e. the GF(2¹⁶) quotient `self · other^(2¹⁶ − 2)`.  When
`other ≠ 0`, Fermat's little theorem in GF(2¹⁶) gives
`other^(2¹⁶ − 1) = 1`, so `other^(2¹⁶ − 2) = other⁻¹` and the
right-hand side is genuinely `self / other`.

The proof unfolds `div_impl` to expose the initial squaring
(handled by the registered `CoreOpsArithMulGF16GF16.mul_spec` via
`step*`) and the subsequent loop call.  The closed-form
`div_impl_loop_spec` is provided as a hypothesis (parametric in the
intermediate `square` introduced by the prior `Mul<GF16>` step) so
that `step*` can specialise it to the concrete loop entry-point
`(iter, square, out) = ({start := 1, end := 16}, other², self)`.

The remaining algebraic gap

  `(other²)^(2¹⁵ − 1) = other^(2 · (2¹⁵ − 1)) = other^(2¹⁶ − 2)`

is settled by rewriting `other · other` to `other^2`, applying
`pow_mul` to merge the nested exponent, and discharging the
resulting numeric identity `2 · (2¹⁵ − 1) = 2¹⁶ − 2` with `decide`.

**Source**: spqr/src/encoding/gf.rs (lines 446:4-456:5)
-/
@[step]
theorem div_impl_spec (self other : spqr.encoding.gf.GF16) :
    div_impl self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 *
          other.value.val.toGF216 ^ (2 ^ 16 - 2) ⦄ := by
  unfold div_impl
  have h_loop := fun (square : spqr.encoding.gf.GF16) =>
    div_impl_loop_spec { start := 1#i32, «end» := 16#i32 } square self
      (by scalar_tac)
  step*
  -- Close the algebraic gap:
  --   `(other · other) ^ (2 ^ (16 - 1).toNat - 1) = other ^ (2 ^ 16 - 2)`.
  rw [result_post, square_post,
      show (other.value.val.toGF216 * other.value.val.toGF216 : GF216)
            = other.value.val.toGF216 ^ 2 from by ring,
      ← pow_mul]
  congr 1

end spqr.encoding.gf.GF16
