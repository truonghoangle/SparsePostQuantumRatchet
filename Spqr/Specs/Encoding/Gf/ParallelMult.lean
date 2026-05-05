/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.ParallelMultLoop0
import Spqr.Specs.Encoding.Gf.GF16.MulAssign
/-! # Spec Theorem for `spqr::encoding::gf::parallel_mult`

Specification and proof for `encoding.gf.parallel_mult`, the top-level
entry point that multiplies every element of a mutable `GF16` slice by
a shared factor `a` in GF(2¹⁶).

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

In the Rust source, `mul2_u16` may dispatch to hardware-accelerated
carry-less multiplication (CLMUL/PMULL) on supported architectures;
the extracted Lean version contains only the software fallback.

**Source**: spqr/src/encoding/gf.rs (lines 566:0-579:1)
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf

/-- A default `GF16` value, needed by `Slice.index_usize_spec`. -/
local instance : Inhabited encoding.gf.GF16 := ⟨{ value := 0#u16 }⟩

/-
natural language description:

• Takes a GF(2¹⁶) multiplier `a : GF16` and a mutable slice
  `into : Slice GF16`.
• Runs the pair loop (`parallel_mult_loop`) starting from index 0,
  which processes elements two at a time: for each pair
  `(into[i], into[i+1])`, it computes the GF(2¹⁶) products
  `a · into[i]` and `a · into[i+1]` via `mul2_u16` and writes
  them back, advancing `i` by 2.
• After the loop terminates (when `i + 2 > into.len()`), if there
  is a trailing odd element (`i < into.len()`), it is multiplied
  by `a` via `MulAssign<GF16>`.
• Returns the updated slice.

natural language specs:

• The function always succeeds (no panic / overflow) provided
  `into.length + 2 ≤ Std.Usize.max` (mirrors the Rust
  `#[requires(into.len() <= usize::MAX - 2)]`).
• The returned slice has the same length as the input:
    `result.length = into.length`
  matching the Rust `#[ensures]` annotation.
• Every element of the returned slice is the GF(2¹⁶) product of
  the multiplier `a` with the corresponding original element:
    `∀ j < result.length,
       result[j].value.val.toGF216 =
         a.value.val.toGF216 * into[j].value.val.toGF216`
-/

/-- **Spec and proof concerning `encoding.gf.parallel_mult`**:

The top-level `parallel_mult` multiplies every element of a `GF16`
slice by a shared factor `a`, processing consecutive pairs via
`mul2_u16` and handling the trailing odd element (if any) with
a single `MulAssign`.

The result satisfies:

  1. `result.length = into.length`
     (matching the Rust `#[ensures(|_| future(into).len() == into.len())]`).

  2. `∀ j < result.length,
       (result.val[j]!).value.val.toGF216 =
         a.value.val.toGF216 * (into.val[j]!).value.val.toGF216`
     (every element is multiplied by `a` in GF(2¹⁶)).

The proof unfolds `parallel_mult` to expose the loop call and the
trailing-element branch, then discharges the resulting goals with
`step*` (which applies the registered `parallel_mult_loop_spec` and
`mul_assign_spec`), followed by case analysis and the value-level
invariants from the loop specification.

**Source**: spqr/src/encoding/gf.rs (lines 566:0-579:1)
-/
@[step]
theorem parallel_mult_spec
    (a : encoding.gf.GF16) (into : Slice encoding.gf.GF16)
    (hlen : into.length + 2 ≤ Std.Usize.max) :
    parallel_mult a into ⦃ (result : Slice encoding.gf.GF16) =>
      result.length = into.length ∧
      (∀ j : Nat, j < result.length →
        (result.val[j]!).value.val.toGF216 =
          a.value.val.toGF216 * (into.val[j]!).value.val.toGF216) ⦄ := by
  unfold parallel_mult
  step*
  rename_i ha1 hlen1 hterm hi_hi hval_proc hval_unproc hval_before
  constructor
  · simp_all
  · intro j hj
    set i:=ha1.2.2
    have hj_loop : j < i ∨ j ≥ i := Nat.lt_or_ge j i
    rcases hj_loop with hj1 | hj2
    · -- Case 1: `j` is processed by the pair loop, so we can apply the loop spec invariants.
      have :=hterm.2.2.2.2.2.1 j (by simp)  hj1
      simp_all
      rw[← this]
      



end spqr.encoding.gf
