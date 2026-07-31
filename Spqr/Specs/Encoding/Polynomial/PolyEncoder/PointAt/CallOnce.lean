/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.CallMut

/-!
# Spec theorem for `PolyEncoder::point_at` closure#1 `call_once`

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

The closure is extracted by Aeneas as both a `FnMut` and a `FnOnce` trait
implementation.  The `FnOnce` variant
`encoding.polynomial.PolyEncoder.point_at.closure_1.Insts.
CoreOpsFunctionFnOnceTuplePairUsizeSharedGF16Pt`
whose `call_once` method takes:
  - a closure state `c : PolyEncoder.point_at.closure_1` (which is `Unit`,
    since the closure captures no environment),
  - a `(Usize × GF16)` argument (the current enumerated pair),

and returns `Pt` — the constructed evaluation point (without the closure state,
unlike `call_mut`).

Concretely, the extracted `call_once` delegates to `call_mut`:
  1. Calls `call_mut c p` to obtain `(p1, _)` — the constructed `Pt` paired
     with the (discarded) closure state.
  2. Returns `p1` — just the resulting evaluation point.

Since `call_once` introduces no additional logic beyond the delegation to
`call_mut`, its postcondition is inherited directly from `call_mut_spec`
(minus the closure state preservation):

  - **x-coordinate (GF216 lift)**: `result.x.toGF216 = p.1.val.toGF216`
  - **y-coordinate preserved**: `result.y = p.2`

This is the per-element mapping step used by `point_at` when the closure is
consumed (via `FnOnce`) rather than borrowed (via `FnMut`).

**Source**: spqr/src/encoding/polynomial.rs (lines 641:25-644:21)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

-- Long namespace names are unavoidable for Aeneas-extracted closures.
set_option linter.style.longLine false

namespace spqr.encoding.polynomial.PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairUsizeSharedGF16Pt

/-- **Spec theorem for `PolyEncoder.point_at.closure_1.call_once`**:

The closure `|(x, y)| Pt { x: GF16::new(x as u16), y: *y }` inside
`point_at`, extracted as `call_once`.  Takes a closure state `c` (which is
`Unit`, since the closure captures nothing) and a `(Usize × GF16)` argument,
and returns the resulting `Pt` where:

• The function succeeds whenever `p.1.val < 2 ^ 16` (i.e. the
  enumeration index fits in a `u16`).

• **x-coordinate (GF216 lift)**: the x-coordinate of the resulting `Pt`
  lifts to the same GF(2¹⁶) element as the enumeration index:
    `result.x.toGF216 = p.1.val.toGF216`

• **y-coordinate preserved**: the y-coordinate is the input `GF16` value,
  unchanged:
    `result.y = p.2`

**Source**: spqr/src/encoding/polynomial.rs (lines 641:25-644:21)
-/
@[step]
theorem call_once_spec
    (c : PolyEncoder.point_at.closure_1)
    (p : Usize × GF16)
    (h : p.1.val < 2 ^ 16) :
    call_once c p
      ⦃ (result : Pt) =>
        result.x.toGF216 = p.1.val.toGF216 ∧
        result.y = p.2 ⦄ := by
  unfold call_once
  step*

end spqr.encoding.polynomial.PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairUsizeSharedGF16Pt
