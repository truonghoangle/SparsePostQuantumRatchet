/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Gf.GF16.New

/-!
# Spec theorem for `PolyEncoder::point_at` closure#1 `call_mut`

The Rust method `PolyEncoder::point_at` (in `src/encoding/polynomial.rs`,
lines 633–660) converts an array of `Point`s (evaluation-data vectors) into
polynomials for later evaluation.  During this process, each `Point`'s inner
`Vec<GF16>` is enumerated and mapped through a closure (lines 641:25–644:21):

```
.map(|(x, y)| Pt {
    x: GF16::new(x as u16),
    y: *y,
})
```

This closure converts an enumerated `(usize, &GF16)` pair — an index and its
associated field element — into an evaluation point `Pt { x, y }` in
GF(2¹⁶) × GF(2¹⁶), where:
  1. The x-coordinate is the enumeration index `x`, cast from `usize` to `u16`
     and wrapped as a `GF16` via `GF16::new`.
  2. The y-coordinate is the referenced `GF16` value `*y`, passed through
     unchanged.

The closure is extracted by Aeneas as the `FnMut` trait implementation whose
`call_mut` method takes:
  - a closure state `c : PolyEncoder.point_at.closure_1` (which is `Unit`,
    since the closure captures no environment),
  - a `(Usize × GF16)` argument (the current enumerated pair),

and returns `(Pt, closure_1)` — the constructed evaluation point paired with
the unchanged closure state.

Concretely, the extracted `call_mut` performs:
  1. Destructures the input tuple into `(x, y)`.
  2. Casts `x : Usize` to `i : U16` via `UScalar.cast .U16 x`.
  3. Wraps `i` as `g : GF16` via `GF16.new i`.
  4. Returns `({ x := g, y }, c)` — the evaluation point paired with the
     unchanged closure.

**Source**: spqr/src/encoding/polynomial.rs (lines 641:25-644:21)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

-- Long namespace names are unavoidable for Aeneas-extracted closures.
set_option linter.style.longLine false

namespace spqr.encoding.polynomial.PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt

/-- **Spec theorem for `PolyEncoder.point_at.closure_1.call_mut`**:

The closure `|(x, y)| Pt { x: GF16::new(x as u16), y: *y }` inside
`point_at`, extracted as `call_mut`.  Takes a closure state `c` (which is
`Unit`, since the closure captures nothing) and a `(Usize × GF16)` argument,
and returns the pair `(result, c')` where:

• The function succeeds whenever `tupled_args.1.val < 2 ^ 16` (i.e. the
  enumeration index fits in a `u16`).

• **x-coordinate (GF216 lift)**: the x-coordinate of the resulting `Pt`
  lifts to the same GF(2¹⁶) element as the enumeration index:
    `result.1.x.toGF216 = tupled_args.1.val.toGF216`

• **y-coordinate preserved**: the y-coordinate is the input `GF16` value,
  unchanged:
    `result.1.y = tupled_args.2`

• **Closure unchanged**: the closure state is returned as-is:
    `result.2 = c`

**Source**: spqr/src/encoding/polynomial.rs (lines 641:25-644:21)
-/
@[step]
theorem call_mut_spec
    (c : PolyEncoder.point_at.closure_1)
    (tupled_args : Usize × GF16)
    (h : tupled_args.1.val < 2 ^ 16) :
    call_mut c tupled_args
      ⦃ (result : Pt × PolyEncoder.point_at.closure_1) =>
        result.1.x.toGF216 =
          tupled_args.1.val.toGF216 ∧
        result.1.y = tupled_args.2 ∧
        result.2 = c ⦄ := by
  unfold call_mut
  obtain ⟨x, y⟩ := tupled_args
  simp only [] at h ⊢
  step*
  rw [g_post]
  subst i_post
  have hval : (UScalar.cast UScalarTy.U16 x).val = x.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by omega)
  grind

end spqr.encoding.polynomial.PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt
