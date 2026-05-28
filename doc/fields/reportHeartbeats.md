# Report: `set_option maxHeartbeats 6400000` in `FromCompletePointsLoopBody0.lean`

## 1. Context

The file `Spqr/Specs/Encoding/Polynomial/Poly/FromCompletePointsLoopBody0.lean` contains
specification theorems for the **loop body** of `Poly::from_complete_points`. The main
theorem `body_spec` dispatches to per-branch helpers depending on:

- whether the iterator is **in bounds** (`body_spec_some_case`), or
- whether the iterator is **out of bounds** and the slice length is one of the
  allowed concrete sizes (`body_spec_none_0`, `body_spec_none_1`, …, `body_spec_none_36`).

Every `body_spec_none_*` helper carries the annotation:

```lean
set_option maxHeartbeats 6400000 in
```

This is **32×** the default budget of 200 000 heartbeats.

## 2. The theorem `body_spec_none_0`

```lean
set_option maxHeartbeats 6400000 in

private theorem body_spec_none_0
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h0 : pts.val.length = 0) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    have h_len_0 : Slice.len pts = 0#usize := by
      ext
      simp [Slice.len]
      simp [h0]
      simp [Usize.ofNatCore]
    step*
    exact ⟨h_not_lt,
      alloc.vec.Vec.deref (alloc.vec.Vec.new Poly),
      by simp [alloc.vec.Vec.deref, alloc.vec.Vec.new],
      by simp [h0, Finset.sum_range_zero],
      fun _ => ⟨by simp [alloc.vec.Vec.deref, alloc.vec.Vec.new],
                 by simp [h0, Finset.sum_range_zero]⟩,
      fun h => absurd h0 h⟩
```

### Proof outline

| Step | What happens |
|------|-------------|
| `unfold body` | Exposes the full definition of the Rust loop body translated via Aeneas. |
| Enumerate iterator dispatch | Destructs the result of `Enumerate::next` into `some` / `none`. |
| `some` branch | Immediately contradicted by `h_out_of_bounds`. |
| `none` branch | The iterator is exhausted; we must construct the return value. |
| `h_len_0` | Shows `Slice.len pts = 0#usize` from `h0 : pts.val.length = 0`. |
| **`step*`** | **The expensive call.** Repeatedly applies `@[step]`-tagged lemmas to discharge every intermediate monadic bind (`>>=`), `if`/`match`, and arithmetic obligation that remains in the unfolded `body`. |
| Final `exact` | Packages the postcondition witnesses (empty polys slice, zero polynomial sum, etc.). |

## 3. Why `set_option maxHeartbeats 6400000` is needed

The `step*` tactic is the primary consumer of heartbeats. After `unfold body`, the goal
contains the **full monadic translation** of the Rust function body — a deeply nested tree of
`bind`, `if`, scalar casts, vector operations, and slice operations. `step*` works by:

1. Pattern-matching the head of the current goal against the `@[step]` lemma database.
2. Applying the matching lemma, which may itself invoke the kernel for unification and
   type-checking of large terms.
3. Repeating until no more `@[step]` lemma applies.

Each individual step is cheap, but the **number of steps** is proportional to the number of
intermediate Rust operations in the function body. For `body_spec_none_0` the unfolded term
includes:

- `Slice.len` evaluation and comparison against `0`, `1`, `3`, `5`, `30`, `34`, `36`
- Branching on the slice length (a 7-way `if`/`else` chain)
- For the matching branch: `alloc::vec::Vec::new`, `alloc::vec::Vec::deref`,
  `lagrange_polys_for_complete_points`, `const_polys_to_polys`, a fold/sum, etc.
- For every non-matching branch: the kernel must still **reduce** the comparison to
  discover it is `false` and move on.

Even though `pts.val.length = 0` is known, Lean's kernel evaluates the full `if`/`else`
cascade, and each branch may itself be a large term that the kernel must partially normalise
before `step*` can dismiss it. The cumulative cost easily exceeds 200 000 heartbeats.

For the larger sizes (`body_spec_none_30`, `body_spec_none_34`, `body_spec_none_36`) the
situation is even worse because the constant-folded polynomials and Lagrange tables are
bigger.

## 4. Suggested ways to avoid `set_option maxHeartbeats 6400000`

### Strategy A — Replace `step*` with explicit, targeted steps

Instead of letting `step*` blindly iterate through the entire monadic spine, manually
sequence the key reduction steps:

```lean
  | none =>
    -- 1. Establish slice-length facts (already done)
    ...
    -- 2. Reduce the length comparison explicitly
    simp only [h_len_0]
    -- 3. Apply one step lemma at a time for the matching branch
    step  -- handles the first bind
    step  -- handles the Vec::new call
    step  -- handles the deref call
    -- 4. Close the goal with the postcondition witnesses
    exact ⟨ ... ⟩
```

By using **`step`** (single step) rather than **`step*`** (iterated), we control exactly which
obligations are discharged at each point. The kernel never has to hold the entire unfolded
term in memory at once.

### Strategy B — Factor the monadic spine into a `@[simp]`/`@[step]` lemma

Prove once that when the iterator returns `none` and the length matches a given `N`, the
body reduces to a specific value:

```lean
@[step]
private lemma body_none_reduces (pts : Slice Pt) (iter : Enumerate (Iter Pt))
    (iter1 : Enumerate (Iter Pt))
    (h_none : Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter = ok (none, iter1))
    (hN : pts.val.length = N) :
    ∃ p, body pts iter = ok (ControlFlow.done (core.result.Result.Ok p)) ∧ ... := by
  ...
```

Each `body_spec_none_*` theorem then becomes a one-line application of this lemma, and the
heavy `step*` work is done only once (in the proof of `body_none_reduces`), cached, and
reused.

### Strategy C — Pre-reduce with `native_decide` or `Decidable` instances

For purely computational obligations (e.g., `Slice.len pts = 0#usize` or numeric
comparisons), use `native_decide` or `decide` instead of `simp`:

```lean
    have h_len_0 : Slice.len pts = 0#usize := by
      ext; simp [Slice.len, h0, Usize.ofNatCore]
```

can become:

```lean
    have h_len_0 : Slice.len pts = 0#usize := by
      ext; omega
```

or, where the goal is a closed Boolean expression after substitution:

```lean
    have h_len_0 : Slice.len pts = 0#usize := by native_decide
```

`native_decide` compiles the check to native code and runs it outside the kernel, avoiding
heartbeat consumption entirely for decidable propositions.

### Strategy D — Use `withReducible` or `TransparencyMode` control

Wrap the expensive `step*` call to prevent the kernel from unfolding definitions it does
not need:

```lean
    withReducible step*
```

or mark certain definitions as `@[irreducible]` after their key properties are proved, so
that `step*` does not try to unfold them.

### Recommended approach

**Strategy A** (explicit stepping) combined with **Strategy B** (a shared reduction lemma
for the `none` case) is the most robust solution. It:

- Eliminates all `set_option maxHeartbeats` annotations.
- Makes the proof structure clearer and easier to maintain.
- Keeps each individual proof obligation small, improving IDE responsiveness.
- Avoids reliance on `native_decide` (which is not available in all Lean build
  configurations).
