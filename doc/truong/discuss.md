# VecDeque Model Consistency Analysis — `SrcTranslated/FunsExternal.lean`

## 1. Background: The Original Issue

The original bug report described a potential inconsistency in the Lean model of Rust's `VecDeque`:

> **`push_back`** appends `buf ++ [value]`, growing the physical buffer on every call.
> **`pop_front`** and **`index_mut`** formerly used `(head + i) % cap` ring-buffer indexing.
>
> This mismatch means that after a sequence of pops followed by a push, readers (`index_mut`,
> `pop_front`) would compute physical positions via modular arithmetic and land on stale
> elements rather than the freshly pushed value.

Two remedies were proposed:

| Option | Description | Tradeoff |
|--------|-------------|----------|
| **1 — Ring buffer** | Make `push_back` write at `(head + length) % cap`, grow only when `length == cap` | Faithful to Rust's physical layout; more proof overhead |
| **2 — Growing list** | Drop `% cap` from `pop_front` and `index_mut`; keep `push_back` as append | Simpler; matches the capacity-free `Vec` model already used in this codebase |

The reporter recommended **Option 2** since `Vec` is already modeled without capacity.

---

## 2. Current State of `FunsExternal.lean` (as of this analysis)

All three core `VecDeque` operations now consistently implement the **growing-list model** (Option 2). Each definition's docstring explicitly labels it "Growing-list model."

### 2.1 Type Definition (`TypesExternal.lean`, lines 30–33)

```lean
structure alloc.collections.vec_deque.VecDeque (T : Type) (A : Type) where
  buf    : alloc.vec.Vec T    -- backing list (grows, never shrinks)
  head   : Std.Usize          -- index of the first logical element
  length : Std.Usize          -- number of logical elements
```

The logical contents of the deque are `buf[head .. head + length)`.

### 2.2 `push_back` (lines 1068–1080)

```lean
def alloc.collections.vec_deque.VecDeque.push_back ... :=
  fun self value =>
    if h : self.buf.val.length + 1 ≤ Usize.max then
      do
        let len' ← self.length + 1#usize
        ok { self with
          buf := ⟨self.buf.val ++ [value], ...⟩
          length := len' }
    else
      fail .panic
```

**Semantics**: Appends `value` at the physical end of `buf`. `head` is unchanged. `length` is incremented by 1.

**Post-state**: `buf' = buf ++ [value]`, `head' = head`, `length' = length + 1`.

### 2.3 `pop_front` (lines 1009–1024)

```lean
def alloc.collections.vec_deque.VecDeque.pop_front ... :=
  fun self =>
    if self.length = 0#usize then
      ok (none, self)
    else
      if hidx : self.head.val < self.buf.val.length then
        let elem := self.buf.val[self.head.val]'hidx
        do
          let head' ← self.head + 1#usize
          let len' ← self.length - 1#usize
          ok (some elem, { self with head := head', length := len' })
      else
        fail .panic
```

**Semantics**: Reads `buf[head]`, advances `head` by 1, decrements `length` by 1. `buf` is unchanged (no shrinking, no modular wrap-around).

**Post-state**: `elem = buf[head]`, `head' = head + 1`, `length' = length - 1`, `buf' = buf`.

### 2.4 `index_mut` (lines 1111–1126)

```lean
def alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut ... :=
  fun self idx =>
    if idx.val < self.length.val then
      if hphys : self.head.val + idx.val < self.buf.val.length then
        let elem := self.buf.val[self.head.val + idx.val]'hphys
        ok (elem, fun new_elem =>
          { self with buf := ⟨self.buf.val.set (self.head.val + idx.val) new_elem, ...⟩ })
      else
        fail .panic
    else
      fail .panic
```

**Semantics**: Physical index is `head + idx` (linear, no `% cap`). Returns the element and a write-back closure that updates that position.

**Post-state**: `elem = buf[head + idx]`, write-back replaces `buf[head + idx]`.

### 2.5 Other Operations

| Operation | Model | Notes |
|-----------|-------|-------|
| `len` | Returns `self.length` | Trivial |
| `From<[T;N]>::from` | `buf = arr.val`, `head = 0`, `length = N` | Fresh deque |
| `from_iter` | Collects into Vec, wraps with `head = 0` | Fresh deque |
| `into_iter` | Wraps deque into `IntoIter` | `IntoIter.next` is axiomatized |

---

## 3. Consistency Analysis

### 3.1 Internal Consistency ✅

All three core operations (`push_back`, `pop_front`, `index_mut`) are now consistent under the growing-list model:

- **No modular arithmetic** (`% cap`) appears anywhere.
- `head` only increases (via `pop_front`).
- `buf` only grows (via `push_back`).
- Physical position is always `head + idx` (linear).

The logical contents invariant is:

```
logical_contents(vd) = vd.buf.val.drop(vd.head.val).take(vd.length.val)
```

### 3.2 Invariant That Must Hold

For the model to be sound, the following structural invariant must be maintained across all operation sequences:

```
INV(vd) ≡
  vd.head.val + vd.length.val ≤ vd.buf.val.length ∧
  vd.buf.val.length ≤ Usize.max
```

**Verification per operation:**

| Operation | Preserves INV? | Reasoning |
|-----------|---------------|-----------|
| `push_back` | ✅ | `buf` grows by 1, `length` grows by 1, `head` unchanged → `head + (length+1) ≤ (buf.length+1)` |
| `pop_front` (nonempty) | ✅ | `head` grows by 1, `length` shrinks by 1, `buf` unchanged → `(head+1) + (length-1) = head + length ≤ buf.length` |
| `pop_front` (empty) | ✅ | No mutation |
| `index_mut` | ✅ | `buf` same length (`.set`), `head` and `length` unchanged |
| `From<[T;N]>::from` | ✅ | `head = 0`, `length = N`, `buf.length = N` → `0 + N ≤ N` |

### 3.3 Differences from Rust's Physical Model

In real Rust:
- `VecDeque` is a ring buffer with fixed capacity.
- `push_back` writes at `(head + len) % capacity`; grows only when full.
- `pop_front` uses `head = (head + 1) % capacity`.
- Indexing uses `(head + idx) % capacity`.

Our growing-list model differs physically but is **observationally equivalent at the value level**: the sequence of logical elements seen by any caller is identical. The trade-off is:

- ✅ Simpler proofs (no modular arithmetic reasoning).
- ✅ Consistent with the capacity-free `Vec` model used elsewhere.
- ❌ Cannot reason about allocation/reallocation/capacity.
- ❌ `buf` grows monotonically, which diverges from the physical memory layout.

---

## 4. Plausible Scenarios

### Scenario 1: Basic Push-Then-Index (Correct ✅)

**Setup**: Fresh deque from `[a, b, c]`, then `push_back d`.

```
Initial: buf = [a, b, c],  head = 0,  length = 3
After push_back d: buf = [a, b, c, d],  head = 0,  length = 4

index_mut(3) → phys = 0 + 3 = 3 → buf[3] = d ✅
```

### Scenario 2: Pop-Then-Push-Then-Index (The Original Bug Scenario — Now Correct ✅)

**Setup**: Fresh deque `[a, b, c]`, pop all three, then push `x`.

```
Initial:       buf = [a, b, c],  head = 0,  length = 3
pop_front #1:  buf = [a, b, c],  head = 1,  length = 2,  returns a
pop_front #2:  buf = [a, b, c],  head = 2,  length = 1,  returns b
pop_front #3:  buf = [a, b, c],  head = 3,  length = 0,  returns c
push_back x:   buf = [a, b, c, x],  head = 3,  length = 1

index_mut(0) → phys = 3 + 0 = 3 → buf[3] = x ✅
```

Under the OLD ring-buffer model (hypothetical), if `pop_front` used `head = (head+1) % cap`:
```
pop_front #3:  head = (2+1) % 3 = 0,  length = 0
push_back x:   buf = [a, b, c, x],  head = 0,  length = 1  ← buf grew to length 4
index_mut(0) → phys = (0+0) % 3 = 0 → buf[0] = a ❌ (stale!)
```
The old model would fail because `% cap` used the old capacity (3), but `buf` grew to length 4, and the new element at index 3 was unreachable.

### Scenario 3: `chain.Chain.add_epoch` → `send_key` Workflow (The Real Use Case)

This is the actual usage pattern in `Funs.lean` (lines 5635–5800):

1. **`add_epoch`** (line 5663): calls `push_back` on `self.links`, appending a new `ChainEpoch`.
   ```
   links.buf = old_buf ++ [new_epoch]
   links.head = (unchanged)
   links.length = old_length + 1
   ```

2. **`send_key` → `send_key_loop0`** (line 5705): calls `pop_front` repeatedly while `epoch_index > EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`, trimming old epochs from the front.
   ```
   Each pop_front: head += 1, length -= 1, buf unchanged
   ```

3. **`send_key` → `send_key_loop1`** (line 5742): calls `index_mut` on remaining epochs to `clear_next`.
   ```
   index_mut(i) → phys = head + i → accesses correct element ✅
   ```

4. **`send_key` final** (line 5785): calls `index_mut(epoch_index)` to extract the send key.

**Why this works under the growing-list model**: After `pop_front` advances `head`, all subsequent `index_mut` calls use `head + idx` which correctly skips the popped prefix. After `push_back` appends to the end, the new element is at `buf[old_length]`, which is `head + (new_logical_length - 1)` — exactly where `index_mut` would find it.

### Scenario 4: `recv_key` Workflow

`recv_key` (line 5808) calls `epoch_idx` to compute the logical index, then `index_mut(val)` to access the epoch's recv direction.

```
epoch_idx computes: val = links.length - 1 - back
index_mut(val) → phys = head + val
```

This is consistent because the logical element at position `val` is at physical position `head + val` in the growing-list model.

### Scenario 5: Potential Issue — Monotonic Memory Growth

**Concern**: In a long-running chain, `buf` grows unboundedly even though `pop_front` logically removes elements. The stale prefix `buf[0..head)` is never reclaimed.

**Impact on proofs**: None — the model is value-level correct. But if we ever needed to reason about memory bounds, the growing-list model would need augmentation.

**Impact on real Rust**: None — real Rust uses a ring buffer that reuses memory. This is only a modeling concern.

### Scenario 6: `IntoIter.next` Is Axiomatized ⚠️

The `IntoIter.next` method (used via `into_iter` in `chain.Chain.into_pb`) is declared as an `axiom`:

```lean
axiom alloc.collections.vec_deque.into_iter.IntoIter.Insts
  .CoreIterTraitsIteratorIterator.next ...
```

This means we cannot verify that iteration visits the correct logical elements (`buf[head..head+length)`) rather than the entire physical `buf`. If a proof ever needs to reason about the elements produced by `into_iter`, this axiom would need to be replaced with a concrete definition consistent with the growing-list model.

---

## 5. Summary and Recommendation

### Current Status

The `VecDeque` model in `FunsExternal.lean` is **internally consistent** under the growing-list model. All three core operations (`push_back`, `pop_front`, `index_mut`) use linear `head + idx` indexing without modular arithmetic. The docstrings explicitly document this choice.

### No Downstream Dependencies Yet

No files in `Spqr/` reference `VecDeque`, `push_back`, or `pop_front` — meaning no spec proofs currently depend on these definitions. This is a good time to lock down the invariants before downstream proofs are written.

### Recommendations

1. **State and prove the structural invariant** (`head + length ≤ buf.length`) as a separate lemma, and show it is preserved by all operations.
2. **Define `logical_contents`** as `buf.drop(head).take(length)` and prove that:
   - `push_back` appends to `logical_contents`.
   - `pop_front` returns the head of `logical_contents` and drops it.
   - `index_mut(i)` accesses `logical_contents[i]`.
3. **Replace the `IntoIter.next` axiom** with a concrete definition that pops from the inner deque, ensuring iteration is consistent with the growing-list model.
4. **Consider a `normalize` / `compact` operation** (optional): a logical no-op that resets `buf := buf.drop(head), head := 0` to prevent unbounded list growth in proofs that unfold many steps. This wouldn't affect soundness but could simplify proof terms.
