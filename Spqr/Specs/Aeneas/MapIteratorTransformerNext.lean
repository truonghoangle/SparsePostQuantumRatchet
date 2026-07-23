/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `mapIteratorTransformer.next`

In Rust's standard library, `Map<I, F>` is an iterator adapter that lazily applies a mapping
function `F` to each element yielded by an underlying iterator `I`.  The `mapIteratorTransformer`
builds an `Iterator I B` instance whose `next` field first calls the underlying `I`'s `next`,
and on `some item` applies `FnMut.call_mut` to the item using the closure `map.f` to produce a `B`.

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
theorem mapIteratorTransformer_next_spec
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

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
