/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs

/-!
# Spec theorem for `core::iter::adapters::map::{Iterator for Map<I, F>}::collect`

In Rust's standard library, `Map<I, F>` is an iterator adapter that lazily applies a mapping
function `F` to each element yielded by an underlying iterator `I`.  The `collect` method drives
this composed iterator to completion, materialising the mapped elements into a target collection
`B1` via the `FromIterator` trait.

The function proceeds in two stages:
  1. **Map-iterator construction** — a local `Iterator (Map I F) B` instance is built whose `next`
     field first calls the underlying `I`'s `next`, and on `some item` applies `FnMut.call_mut`
     to produce a `B` and an updated closure state `F`.
  2. **Collection** — the map iterator is passed to `FromIterator.from_iter` through the blanket
     `IntoIterator` instance, which drives iteration to completion and assembles the final `B1`
     value.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

/-- The `Iterator (Map I F) B` instance constructed internally by `collect`.

`mapIterator` factors out the locally-defined iterator that `collect` builds.  Its `next`
field composes the underlying iterator's `next` with `FnMut.call_mut`:

  * If the underlying iterator yields `none`, the map iterator yields `none` with an
    updated `Map` state that preserves the current closure value.
  * If the underlying iterator yields `some item`, the closure is applied via
    `FnMut.call_mut` to produce a `(b, f')` pair, and the map iterator yields `some b`
    with the updated iterator and closure state.

The remaining methods (`step_by`, `enumerate`, `take`) are structural stubs matching the
`Iterator` trait's default implementations. -/
noncomputable def mapIterator
    {B I F Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (fnMutInst : core.ops.function.FnMut F Clause0_Item B)
    : core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B := {
  next := fun m => do
    let (opt, iter') ← iterInst.next m.iter
    match opt with
    | none => .ok (none, ⟨iter', m.f⟩)
    | some item => do
      let (b, f') ← fnMutInst.call_mut m.f item
      .ok (some b, ⟨iter', f'⟩)
  step_by := fun m s => if s.val = 0 then .fail .panic else .ok ⟨m, s⟩
  enumerate := fun m => .ok ⟨m, 0#usize⟩
  take := fun m n => .ok ⟨m, n⟩
}

/-- **Spec theorem for `mapIterator.next`** (definitional unfolding):

The `next` of the map iterator first invokes the underlying iterator's `next`.
  * On `none` — the underlying iterator is exhausted — it returns `(none, ⟨iter', m.f⟩)`,
    preserving the closure state unchanged.
  * On `some item` — the underlying iterator yields an element — it applies `FnMut.call_mut`
    to the item, producing `(b, f')`, and returns `(some b, ⟨iter', f'⟩)` with the updated
    closure state.

This follows from the definition of `mapIterator` and is used by downstream inductive proofs
over `iterToList` to reason about each step of the mapped iteration.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/
@[simp, step_simps]
theorem mapIterator_next_eq
    {B I F Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (fnMutInst : core.ops.function.FnMut F Clause0_Item B)
    (m : core.iter.adapters.map.Map I F) :
    (mapIterator iterInst fnMutInst).next m = (do
      let (opt, iter') ← iterInst.next m.iter
      match opt with
      | none => .ok (none, ⟨iter', m.f⟩)
      | some item => do
        let (b, f') ← fnMutInst.call_mut m.f item
        .ok (some b, ⟨iter', f'⟩)) := by
  unfold mapIterator
  rfl

/-- **Spec theorem for `collect`** (definitional unfolding):

`collect` reduces to `FromIterator.from_iter` applied via the blanket `IntoIterator` instance
to the internally-constructed `mapIterator`.

Concretely, for any `Map I F` value `m`:

    `collect iterInst fnMutInst fromIterInst m
       = fromIterInst.from_iter (IntoIterator.Blanket (mapIterator iterInst fnMutInst)) m`

This establishes that `collect` on `Map<I, F>` is equivalent to running the underlying iterator `I`,
mapping each yielded element through `FnMut.call_mut`, and collecting the results via
`FromIterator.from_iter`.

This is the fundamental equation that downstream, specialised `collect_spec` theorems (e.g. for
`const_polys_to_polys`) build upon: they instantiate the generic types, unfold `from_iter` to its
concrete implementation (typically `FromIteratorVec.iterToList`), and then reason about the
resulting loop.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/
@[simp, step_simps]
theorem collect_eq
    {B I F B1 Clause0_Item : Type}
    (iterInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (fnMutInst : core.ops.function.FnMut F Clause0_Item B)
    (fromIterInst : core.iter.traits.collect.FromIterator B1 B)
    (m : core.iter.adapters.map.Map I F) :
    core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
      iterInst fnMutInst fromIterInst m =
      fromIterInst.from_iter
        (core.iter.traits.collect.IntoIterator.Blanket
          (mapIterator iterInst fnMutInst)) m := by
  unfold core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
    mapIterator
  rfl

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
