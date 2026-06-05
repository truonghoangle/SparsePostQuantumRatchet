/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `PolyDecoder::new_with_poly_count` closure `call_mut`

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

The extracted `call_mut` method takes:
  - a closure state `c : new_with_poly_count.closure` (i.e. `Unit`),
  - a `tupled_args : Usize` argument (the `from_fn` index, which is ignored),

and returns `(SortedSet Pt × new_with_poly_count.closure)` — the freshly created
sorted set paired with the unchanged closure state.

Concretely, the extracted `call_mut` performs:
  1. Creates `ss ← SortedSet.new` (a new empty sorted set of `Pt`).
  2. Returns `(ss, c)` — the sorted set paired with the unchanged closure.

**Source**: spqr/src/encoding/polynomial.rs (lines 788:38-788:58)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

-- Long namespace names are unavoidable for Aeneas-extracted closures.
set_option linter.style.longLine false

namespace spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure.Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt

/-- **Spec theorem for `PolyDecoder.new_with_poly_count.closure.call_mut`**:

The closure `|_| SortedSet::new()` inside `new_with_poly_count`, extracted as
`call_mut`.  Takes a closure state `c` (which is `Unit`, since the closure
captures nothing) and a `Usize` argument (the `from_fn` index, which is
ignored), and returns the pair `(result.1, result.2)` where:

• The function succeeds whenever `SortedSet.new` succeeds (which is assumed
  since `SortedSet.new` is an external axiom modelling the infallible Rust
  constructor `SortedSet::new()`).

• **Closure unchanged**: the closure state is returned as-is:
    `result.2 = c`

**Source**: spqr/src/encoding/polynomial.rs (lines 788:38-788:58)
-/
@[step]
theorem call_mut_spec
    (c : PolyDecoder.new_with_poly_count.closure)
    (tupled_args : Usize) :
    call_mut c tupled_args
      ⦃ (result : (sorted_vec.SortedSet Pt) × PolyDecoder.new_with_poly_count.closure) =>
        result.2 = c ⦄ := by
  unfold call_mut
  step*

end spqr.encoding.polynomial.PolyDecoder.new_with_poly_count.closure.Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt
