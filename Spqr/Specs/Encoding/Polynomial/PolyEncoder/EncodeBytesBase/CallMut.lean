/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `PolyEncoder::encode_bytes_base` closure#0 `call_mut`

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

The extracted `call_mut` method takes:
  - a closure state `c : encode_bytes_base.closure` (i.e. `Slice U8`, the
    captured `msg`),
  - a `tupled_args : Usize` argument (the `from_fn` index, which is ignored),

and returns `(Point × encode_bytes_base.closure)` — the freshly constructed
`Point` paired with the unchanged closure state.

Concretely, the extracted `call_mut` performs:
  1. Computes `i := Slice.len c` (length of the captured message).
  2. Computes `i1 := i / 2` (half the message length).
  3. Creates `v := Vec.with_capacity GF16 i1` (an empty vector).
  4. Returns `({ value := v }, c)` — a `Point` with empty value vector, paired
     with the unchanged closure.

**Source**: spqr/src/encoding/polynomial.rs (lines 676:63-678:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

-- Long namespace names are unavoidable for Aeneas-extracted closures.
set_option linter.style.longLine false

namespace spqr.encoding.polynomial.PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoint

/-- **Spec theorem for `PolyEncoder.encode_bytes_base.closure.call_mut`**:

The closure `|_| Point { value: Vec::<GF16>::with_capacity(msg.len() / 2) }`
inside `encode_bytes_base`, extracted as `call_mut`.  Takes a closure state `c`
(which is `Slice U8`, the captured message) and a `Usize` argument (the
`from_fn` index, which is ignored), and returns the pair `(result.1, result.2)`
where:

• The function always succeeds (division of a `Usize` by the non-zero constant
  `2` cannot overflow or fail).

• **Empty value vector**: the returned `Point` has an empty `value` field:
    `result.1.value.val = []`

• **Closure unchanged**: the closure state is returned as-is:
    `result.2 = c`

**Source**: spqr/src/encoding/polynomial.rs (lines 676:63-678:9)
-/
@[step]
theorem call_mut_spec
    (c : PolyEncoder.encode_bytes_base.closure)
    (tupled_args : Usize) :
    call_mut c tupled_args
      ⦃ (result : Point × PolyEncoder.encode_bytes_base.closure) =>
        result.1.value.val = [] ∧
        result.2 = c ⦄ := by
  unfold call_mut
  step*
  simp [alloc.vec.Vec.with_capacity]

end spqr.encoding.polynomial.PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoint
