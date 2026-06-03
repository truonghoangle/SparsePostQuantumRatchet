/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `core::slice::iter::{Iterator for Iter<'a, T>}::map`

The Rust method `core::slice::iter::{Iterator for Iter<'a, T>}::map` (in the
standard library, `core/src/slice/iter/macros.rs`, lines 153:8-153:45) wraps a
slice iterator together with a mapping function into a lazy `Map` adapter
struct.  No elements are consumed at this point; actual iteration is deferred
to subsequent calls such as `Map.collect` or `Map.next`.

The Aeneas-extracted Lean function
`core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map`
constructs a `core.iter.adapters.map.Map (core.slice.iter.Iter T) F` value by
pairing the input iterator with the mapping function:

```
@[rust_fun
  "core::slice::iter::{…}::map"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map
  {T : Type} {B : Type} {F : Type}
  (_opsfunctionFnMutFTupleSharedATBInst : core.ops.function.FnMut F T B) :
  core.slice.iter.Iter T → F → Result
    (core.iter.adapters.map.Map (core.slice.iter.Iter T) F) :=
  fun iter f => ok ⟨iter, f⟩
```

The function is total (never panics) for any valid `Iter T` and mapping
function `F`.  The resulting `Map` adapter preserves both the underlying
iterator and the mapping function verbatim, deferring all element-wise
computation to the downstream consumer (typically `Map.collect`).

This is a key building block in `const_polys_to_polys` (in
`src/encoding/polynomial.rs`, lines 465:0-467:1) where the slice iterator
produced by `Slice.iter` is wrapped with the `|x| x.to_poly()` closure via
this `map` combinator, and subsequently driven to completion by `Map.collect`.

**Postcondition**:
  - **Iterator preservation**: `result.iter = iter`
  - **Function preservation**: `result.f = f`

**Source**: core/src/slice/iter/macros.rs (lines 153:8-153:45)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT

/--
**Spec theorem for `core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map`**:

• Takes a `core.ops.function.FnMut F T B` instance (witnessing that `F` is a
  callable mapping `T → B`), a `core.slice.iter.Iter T` (a slice iterator over
  elements of type `T`), and a mapping function `f : F`.
• Returns a `core.iter.adapters.map.Map (core.slice.iter.Iter T) F` whose
  `iter` field is the original iterator and whose `f` field is the original
  mapping function.

• The function always succeeds (no panic) for any `Iter T` and `F` input,
  since it merely constructs the pair `⟨iter, f⟩` without any fallible
  operations.
• No elements of the underlying slice are consumed; the `Map` adapter is a
  lazy wrapper that defers element-wise application of `f` to downstream
  consumers such as `Map.collect` or `Map.next`.

The postcondition captures both structural invariants:

  `result.iter = iter`  — the adapter wraps the same iterator.
  `result.f = f`        — the adapter stores the same mapping function.

The proof unfolds `map` to expose the underlying `ok ⟨iter, f⟩` constructor
and discharges the resulting goal with `step*`.

**Source**: core/src/slice/iter/macros.rs (lines 153:8-153:45)
-/
@[step]
theorem map_spec
    {T : Type} {B : Type} {F : Type}
    (fnMutInst : core.ops.function.FnMut F T B)
    (iter : core.slice.iter.Iter T)
    (f : F) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map
      fnMutInst iter f
    ⦃ (result : core.iter.adapters.map.Map (core.slice.iter.Iter T) F) =>
      result.iter = iter ∧ result.f = f ⦄ := by
  unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map
  step*

end Aeneas.Std.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT
