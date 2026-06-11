/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `collect` on the enumerate–map pipeline in `PolyEncoder::point_at`

The Rust method `PolyEncoder::point_at` (in `src/encoding/polynomial.rs`, lines
641:25-644:21) transforms each `Point`'s inner `Vec<GF16>` into a `Vec<Pt>` via
an enumerate–map–collect pipeline:

```rust
let pt_vec: Vec<Pt> = pts[i].value.iter().enumerate()
    .map(|(x, y)| Pt { x: GF16::new(x as u16), y: *y })
    .collect();
```

The Aeneas-extracted Lean expression for this pipeline is:

```
core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
  (core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
    (core.iter.traits.iterator.IteratorSliceIter encoding.gf.GF16))
  encoding.polynomial.PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt
  (core.iter.traits.collect.FromIteratorVec encoding.polynomial.Pt) m
```

The `collect` call drives the composed `Map (Enumerate (Iter GF16))` iterator to
completion, materialising a `Vec<Pt>`.  The function is total (never panics) for
any valid map iterator state `m`.

The resulting `Map` adapter preserves both the underlying enumerate iterator and
the closure state, deferring all element-wise computation to the `collect`
consumer which builds the vector.

**Postcondition**:
  - **Iterator preservation**: `result.iter = m.iter`
  - **Closure preservation**: `result.f = m.f`

**Source**: src/encoding/polynomial.rs (lines 641:25-644:21)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

/--
**Spec theorem for
`core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.map`**:

• Takes the enumerate iterator instance for `Iter GF16`, the `FnMut` instance
  for `closure_1` (which maps `(Usize, &GF16) → Pt`), an enumerate iterator
  `e`, and a closure state `f`.
• Returns a `Map (Enumerate (Iter GF16)) closure_1` whose `iter` field is the
  enumerate iterator `e` and whose `f` field is the closure state `f`.

• The function always succeeds for any `Enumerate (Iter GF16)` and closure state
  input, since it merely constructs the pair `⟨e, f⟩` without any fallible
  operations.

The postcondition captures both structural invariants:

  `result.iter = e`  — the adapter wraps the same enumerate iterator.
  `result.f = f`     — the adapter stores the same closure state.

The proof unfolds `map` to expose the underlying `ok ⟨e, f⟩` constructor and
discharges the resulting goal with `step*`.

**Source**: core/src/iter/adapters/enumerate.rs (lines 62:0-64:16)
-/
@[step]
theorem enumerate_map_spec
    (e : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
      spqr.encoding.gf.GF16))
    (f : spqr.encoding.polynomial.PolyEncoder.point_at.closure_1) :
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.map
      (core.iter.traits.iterator.IteratorSliceIter spqr.encoding.gf.GF16)
      spqr.encoding.polynomial.PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt
      e f
    ⦃ (result : core.iter.adapters.map.Map
        (core.iter.adapters.enumerate.Enumerate
          (core.slice.iter.Iter spqr.encoding.gf.GF16))
        spqr.encoding.polynomial.PolyEncoder.point_at.closure_1) =>
      result.iter = e ∧ result.f = f ⦄ := by
  unfold core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.map
  step*

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
