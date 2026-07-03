/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `core::iter::adapters::map::{Iterator for Map<I, F>}::collect`

In Rust's standard library, `Map<I, F>` is an iterator adapter that lazily applies a mapping
function `F` to each element yielded by an underlying iterator `I`.  The `collect` method drives
this composed iterator to completion, materialising the mapped elements into a target collection
`B1` via the `FromIterator` trait.

The function proceeds in two stages:
  1. **Map-iterator construction** — a `mapIteratorTransformer` builds an `Iterator I B` instance
     whose `next` field first calls the underlying `I`'s `next`, and on `some item` applies
     `FnMut.call_mut` to the item using the closure `map.f` to produce a `B`.
  2. **Collection** — the map-transformed iterator is passed to `FromIterator.from_iter` through
     the blanket `IntoIterator` instance, which drives iteration to completion and assembles the
     final `B1` value.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

/--
**Spec theorem for `mapIteratorTransformer.next`** (definitional unfolding):

• Takes an iterator state `iter : I` and the `mapIteratorTransformer`-constructed iterator
  instance built from a `Map I F` value `m`, an underlying `Iterator I Clause0_Item` instance,
  and a `FnMut F Clause0_Item B` instance.
• Composes the underlying iterator's `next` with `FnMut.call_mut`:
    - If the underlying iterator yields `none`, the map-transformed iterator yields
      `(none, iter')` — the underlying iterator is exhausted.
    - If the underlying iterator yields `some val`, the closure is applied via
      `FnMut.call_mut m.f val` to produce `(b, _)`, and the map-transformed iterator
      yields `(some b, iter')` with the updated underlying iterator state.

• The function always produces the same result as inlining the `mapNext` closure from
  `mapIteratorTransformer`, since `fromNext` stores that closure as the `next` field.

The proof unfolds `mapIteratorTransformer` and `fromNext` to expose the underlying composition
and discharges with `rfl`.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/
@[simp, step_simps]
theorem mapIteratorTransformer_next_eq
    {B I F Clause0_Item : Type}
    (m : core.iter.adapters.map.Map I F)
    (iterInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (fnMutInst : core.ops.function.FnMut F Clause0_Item B)
    (iter : I) :
    (core.iter.adapters.map.mapIteratorTransformer m iterInst fnMutInst).next iter = (do
      let (opt, iter') ← iterInst.next iter
      match opt with
      | none => .ok (none, iter')
      | some val => do
        let (postFnVal, _) ← fnMutInst.call_mut m.f val
        .ok (some postFnVal, iter')) := by
  unfold core.iter.adapters.map.mapIteratorTransformer
    core.iter.traits.iterator.Iterator.fromNext
  rfl

/--
**Spec theorem for `collect`** (definitional unfolding):

• Takes a `Map I F` value `m`, an `Iterator I Clause0_Item` instance for the underlying
  iterator, a `FnMut F Clause0_Item B` instance for the mapping closure, and a
  `FromIterator B1 B` instance for the target collection.
• Delegates to `Iterator.collect.default`, which in turn calls `FromIterator.from_iter`
  with the blanket `IntoIterator` instance wrapping the `mapIteratorTransformer`-constructed
  iterator, starting iteration from the underlying iterator state `m.iter`:

      `collect iterInst fnMutInst fromIterInst m
         = fromIterInst.from_iter
             (IntoIterator.Blanket (mapIteratorTransformer m iterInst fnMutInst))
             m.iter`

• This establishes that `collect` on `Map<I, F>` is equivalent to running the underlying
  iterator `I`, mapping each yielded element through `FnMut.call_mut`, and collecting the
  results via `FromIterator.from_iter`.

This is the fundamental equation that downstream, specialised `collect_spec` theorems (e.g. for
`const_polys_to_polys`) build upon: they instantiate the generic types, unfold `from_iter` to
its concrete implementation (typically `FromIteratorVec.iterToList`), and then reason about the
resulting loop.

The proof unfolds `collect` and `Iterator.collect.default` to expose the underlying
`from_iter` call and discharges with `rfl`.

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
          (core.iter.adapters.map.mapIteratorTransformer m iterInst fnMutInst))
        m.iter := by
  unfold core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
    core.iter.traits.iterator.Iterator.collect.default
  rfl

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
