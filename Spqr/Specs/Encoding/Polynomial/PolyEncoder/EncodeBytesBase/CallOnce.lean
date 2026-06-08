/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytesBase.CallMut

/-!
# Spec theorem for `PolyEncoder::encode_bytes_base` closure#0 `call_once`

The Rust method `PolyEncoder::encode_bytes_base` (in `src/encoding/polynomial.rs`,
lines 670–691) constructs an array of `NUM_POLYS` empty `Point`s via
`core::array::from_fn`.  The closure passed to `from_fn` (lines 676:63–678:9):

```
|_| Point {
    value: Vec::<GF16>::with_capacity(msg.len() / 2),
}
```

ignores its `usize` index argument and returns a fresh `Point` whose `value`
field is an empty `Vec<GF16>` pre-allocated with capacity `msg.len() / 2`.

The closure captures `msg: &[u8]` (the input byte slice).  Aeneas extracts the
closure state type as `encode_bytes_base.closure := Slice U8`, so the captured
state *is* the message slice itself.

The closure is extracted by Aeneas as both a `FnMut` and a `FnOnce` trait
implementation.  The `FnOnce` variant
`encoding.polynomial.PolyEncoder.encode_bytes_base.closure.Insts.
CoreOpsFunctionFnOnceTupleUsizePoint`
whose `call_once` method takes:
  - a closure state `c : PolyEncoder.encode_bytes_base.closure` (i.e. `Slice U8`,
    the captured `msg`),
  - an `i : Usize` argument (the `from_fn` index, which is ignored),

and returns `Point` — the freshly constructed `Point` (without the closure state,
unlike `call_mut`).

Concretely, the extracted `call_once` delegates to `call_mut`:
  1. Calls `call_mut c i` to obtain `(p, _)` — the constructed `Point` paired
     with the (discarded) closure state.
  2. Returns `p` — just the resulting `Point`.

Since `call_once` introduces no additional logic beyond the delegation to
`call_mut`, its postcondition is inherited directly from `call_mut_spec`
(minus the closure state preservation):

  - **Empty value vector**: `result.value.val = []`

This is the per-element construction step used by `encode_bytes_base` when the
closure is consumed (via `FnOnce`) rather than borrowed (via `FnMut`).

**Source**: spqr/src/encoding/polynomial.rs (lines 676:63-678:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

-- Long namespace names are unavoidable for Aeneas-extracted closures.
set_option linter.style.longLine false

namespace spqr.encoding.polynomial.PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePoint

/-- **Spec theorem for `PolyEncoder.encode_bytes_base.closure.call_once`**:

The closure `|_| Point { value: Vec::<GF16>::with_capacity(msg.len() / 2) }`
inside `encode_bytes_base`, extracted as `call_once`.  Takes a closure state `c`
(which is `Slice U8`, the captured message) and a `Usize` argument (the
`from_fn` index, which is ignored), and returns the resulting `Point` where:

• The function always succeeds (division of a `Usize` by the non-zero constant
  `2` cannot overflow or fail).

• **Empty value vector**: the returned `Point` has an empty `value` field:
    `result.value.val = []`

**Source**: spqr/src/encoding/polynomial.rs (lines 676:63-678:9)
-/
@[step]
theorem call_once_spec
    (c : PolyEncoder.encode_bytes_base.closure)
    (i : Usize) :
    call_once c i
      ⦃ (result : Point) =>
        result.value.val = [] ⦄ := by
  unfold call_once
  step*

end spqr.encoding.polynomial.PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnOnceTupleUsizePoint
