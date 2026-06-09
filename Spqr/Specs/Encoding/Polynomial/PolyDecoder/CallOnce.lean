/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.CallMut

/-!
# Spec theorem for `PolyDecoder::new_with_poly_count` closure `call_once`

The Rust method `PolyDecoder::new_with_poly_count` (in `src/encoding/polynomial.rs`,
lines 782–791) constructs a `PolyDecoder` by initialising an array of 16 empty
`SortedSet<Pt>` values via `core::array::from_fn`.  The closure passed to `from_fn`
(line 788):

```
|_| SortedSet::new()
```

ignores its `usize` index argument and returns a fresh, empty `SortedSet<Pt>`.

The closure captures no environment — Aeneas extracts the closure state type as
`new_with_poly_count.closure := Unit` — so the closure state is always `()`.

The closure is extracted by Aeneas as both a `FnMut` and a `FnOnce` trait
implementation.  The `FnOnce` variant
`encoding.polynomial.PolyDecoder.new_with_poly_count.closure.Insts.
CoreOpsFunctionFnOnceTupleUsizeSortedSetPt`
whose `call_once` method takes:
  - a closure state `c : new_with_poly_count.closure` (i.e. `Unit`,
    since the closure captures nothing),
  - an `i : Usize` argument (the `from_fn` index, which is ignored),

and returns `SortedSet Pt` — the freshly created sorted set (without the closure
state, unlike `call_mut`).

Concretely, the extracted `call_once` delegates to `call_mut`:
  1. Calls `call_mut c i` to obtain `(ss, _)` — the constructed `SortedSet Pt` paired
     with the (discarded) closure state.
  2. Returns `ss` — just the resulting sorted set.

Since `call_once` introduces no additional logic beyond the delegation to
`call_mut`, its postcondition is inherited directly from `call_mut_spec`
(minus the closure state preservation):

  - The function succeeds whenever `SortedSet.new` succeeds (which is assumed
    since `SortedSet.new` is an external axiom modelling the infallible Rust
    constructor `SortedSet::new()`).

This is the per-element construction step used by `new_with_poly_count` when the
closure is consumed (via `FnOnce`) rather than borrowed (via `FnMut`).

**Source**: spqr/src/encoding/polynomial.rs (lines 788:38-788:58)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

-- Long namespace names are unavoidable for Aeneas-extracted closures.
set_option linter.style.longLine false

namespace spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeSortedSetPt

/-- **Spec theorem for `PolyDecoder.new_with_poly_count.closure.call_once`**:

The closure `|_| SortedSet::new()` inside `new_with_poly_count`, extracted as
`call_once`.  Takes a closure state `c` (which is `Unit`, since the closure
captures nothing) and a `Usize` argument (the `from_fn` index, which is
ignored), and returns the resulting `SortedSet Pt` where:

• The function always succeeds (it delegates to `call_mut`, which succeeds
  whenever the infallible `SortedSet::new()` succeeds).

**Source**: spqr/src/encoding/polynomial.rs (lines 788:38-788:58)
-/
@[step]
theorem call_once_spec
    (c : PolyDecoder.new_with_poly_count.closure)
    (i : Usize) :
    call_once c i
      ⦃ (result : sorted_vec.SortedSet Pt) =>
        True ⦄ := by
  unfold call_once
  step*

end spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeSortedSetPt
