# Code Defects Identified from Specification Theorems

This report lists properties of the **Rust code** in `src/` that the Lean spec theorems under
`Spqr/Specs/` had to *assume away* as preconditions, or *surprising behaviour* that their
postconditions pin down. All spec theorems referenced are proved; the "defects" are in the Rust
source (or its documentation), not in the proofs. Findings are ranked by practical impact.

Methodology: the 221 spec files under `Spqr/Specs/` were surveyed, their
preconditions/postconditions were cross-referenced against the Rust sources in `src/` (and the
`sorted-vec` 0.8.6 dependency), and the chain-related spec modules were rebuilt with `lake build`
to confirm the referenced theorems compile as read.

---

## 1. Deserialized chain state is never validated → panics reachable from a corrupted/malicious state blob (HIGH)

**Specs that expose it**

- `Spqr/Specs/Chain/ChainEpochDirection/FromPb.lean`: postcondition is
  `ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }`; docstring says
  *"Always succeeds (no validation)"*.
- `Spqr/Specs/Chain/ChainEpochDirection/NextKeyInternal.lean` requires
  `h_next_len : next.length = 32`.
- `Spqr/Specs/Chain/KeyHistory/Get.lean` (`get_spec`) requires
  `h_data_aligned : self.data.length % 36 = 0`; docstring: *"Preconditions model the Rust
  `assert_eq!` panic"*.
- `Spqr/Specs/Chain/KeyHistory/Gc.lean` (`gc_spec`) requires
  `h_key_ge : trim_threshold ≤ data.length → max_ooo ≤ current_key` (models
  `assert!(current_key >= max_ooo)`), and `Key.lean` needs the extra invariant
  `h_prev_ctr : prev.data.length ≤ 36 * ctr` to discharge it.

**Rust defect** (`src/chain.rs`)

```rust
fn from_pb(pb) -> Result<Self, Error> {
    Ok(Self { ctr: pb.ctr, next: pb.next, prev: KeyHistory { data: pb.prev } })   // L306-312
}
```

None of `next.len() == 32`, `prev.len() % 36 == 0`, or `prev.len() ≤ 36·ctr` is checked, yet
each is required downstream:

| Field | Consumer | Failure |
|---|---|---|
| `next.len() ≠ 32` (non-empty) | `next_key_internal`: `next.copy_from_slice(&genr8r[..32])` (L241) | panic (length mismatch) |
| `prev.len() % 36 ≠ 0` | `KeyHistory::get`: `assert_eq!(self.data.len() % KEY_SIZE, 0)` (L191) | panic |
| `prev` large, `ctr` small | `KeyHistory::gc`: `assert!(current_key >= max_ooo)` (L149) | panic |

The spec theorems are only provable because these facts are *assumed*; nothing in
`from_pb`/`decode_state` establishes them. A state blob that is prost-valid but semantically
inconsistent turns `recv`/`send` into a panic instead of `Err(StateDecode)`.

**Fix**: validate in `ChainEpochDirection::from_pb` (return `Error::StateDecode`), which would let
the `h_*` hypotheses become provable invariants.

## 2. `u32` overflow in `KeyHistory::get` trimmed-check (MEDIUM)

`Spqr/Specs/Chain/KeyHistory/Get.lean` and `Key32.lean` require
`h_ooo_no_overflow : at1 + maxOoo ≤ U32.max`.

```rust
if at + (params.max_ooo_keys_or_default()) < current_ctr {   // chain.rs L192
```

`at` is the attacker-supplied message `index` (a `u32` decoded from a varint). When `ctr`
approaches `u32::MAX`, `at + max_ooo` overflows: debug builds panic, release builds wrap to a
small value so the branch is taken and a *valid* key is reported as `KeyTrimmed`. `key()` itself
guards the analogous `self.ctr + max_ooo` only via `hax_lib::assume!`, which Aeneas erases — hence
`h_ctr_bound : i + 1 ≤ U32.max - 390451572` in `Key.lean`.

**Fix**: use `at.checked_add(..)` / `saturating_add`.

## 3. `u64 → usize` truncation in `Chain::epoch_idx` on 32-bit targets (MEDIUM, 32-bit only)

`Spqr/Specs/Chain/Chain/EpochIdx.lean` needs
`h_diff_fits : epoch ≤ current_epoch → current_epoch - epoch ≤ Usize.max` and proves it with
`cases System.Platform.numBits_eq`.

```rust
let back = (self.current_epoch - epoch) as usize;   // chain.rs L376
if back >= links { return Err(EpochOutOfRange) }
Ok(links - 1 - back)
```

On a 32-bit platform a difference ≥ 2³² truncates, so the bounds check can pass and the function
returns an index for the **wrong epoch**, silently handing out a key from another epoch.
Impractical to reach today (requires 2³² epochs) but the spec correctly refuses to prove
correctness without the hypothesis.

**Fix**: `usize::try_from(..).map_err(..)`.

## 4. Rust comment in `PolyDecoder::add_chunk` contradicts actual semantics (LOW / documentation, potentially behavioural)

`Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean` models the push as
`IsSortedPushResult`, whose second disjunct is `new = old.take j ++ [p] ++ old.drop (j+1)` —
i.e. **replacement**. The external model `SrcTranslated/FunsExternal.lean:2146` has
`.eq => ok (i, some a, x :: rest)`.

The Rust source claims the opposite (`polynomial.rs` L896-898):

```rust
// This will discard new points whose X value matches a previous
// old point, since we've implemented equality for the Pt object
// to only care about the X value.
self.pts[poly].push(Pt { x, y });
```

`sorted-vec 0.8.6` `SortedSet::push` on `Equal` does `pop()` then `push(element)` (and `replace`
swaps), so the **new** `y` wins. The verified model is right; the comment is wrong. Because
`Pt::eq`/`Ord` ignore `y` (`Spqr/Specs/Encoding/Polynomial/Pt/Eq.lean`: *"returns true iff
self.x.value = other.x.value (y ignored)"*), a re-sent chunk index with different payload
overwrites earlier points rather than being ignored. For the honest protocol it is harmless (same
index ⇒ same data) and tampering is caught by the MAC.

**Fix**: correct the comment, or use `find_or_push` if "discard new" is the intended semantics.

## 5. `PolyEncoder` index truncation `u32 → u16` (LOW)

`Spqr/Specs/Encoding/Polynomial/PolyEncoder/NextChunk.lean` needs `h_idx_fits : self.idx ≤ U16.max`
to prove `chunk.index = self.idx`; `PolyEncoder/FromPb.lean` yields `encoder.idx = pb.idx` for any
`u32`.

```rust
let out = self.chunk_at(self.idx as u16);      // polynomial.rs L735
self.idx = self.idx.wrapping_add(1);
```

`idx` is a `u32` but only 16 bits are meaningful; after 65 535 chunks (or from a persisted
`pb.idx > 65535`) the emitted `chunk.index` silently wraps.

**Fix**: store `idx: u16`, or reject out-of-range values in `from_pb`.

## 6. `decode_chunk` mutates the cursor before its bounds check (LOW)

Documented in `Spqr/Specs/V1/Chunked/States/Serialize/DecodeChunk.lean`: *"on the two error paths
of `decode_chunk` itself the cursor has already advanced by `n + 32`"*, so the postcondition only
proves `at ≤ *future(at)` rather than `*future(at) = at` on error — unlike `decode_varint`, which
restores it. `Message::deserialize` discards the cursor on error, so no exploit, but it is an
inconsistent contract. Also `hax_lib::assume!(*at < usize::MAX - 32)` is erased in translation, so
the spec needs `from.len() + 32 ≤ usize::MAX`.

## 7. `decode_varint` accepts non-canonical encodings and truncates bit 64+ (LOW)

`DecodeVarint.lean` (`varintBlockAt`) explicitly: *"admit non-canonical encodings (`1` as
`0x81 0x00`)"* and *"truncated to 64 bits… silent truncation of the 10th byte's high bits"*.
Multiple byte strings decode to the same value, i.e. serialisation is not injective; benign for
this protocol but worth noting for any future roundtrip theorem.

## 8. `usize` overflow in `ChainParams::trim_size` on 32-bit (LOW, local config only)

`Spqr/Specs/Chain/ChainParams/TrimSize.lean` needs `h_ooo : max_ooo_keys < 390451572` because
`hax_lib::assume!` is erased; `Gc.lean`/`Key32.lean` tighten it to `< 108458770` so
`trim_size * 36` fits in 32 bits. `max_ooo * 11` overflows for large (mis)configured
`max_ooo_keys`. Since `chain_params` comes from the local `Params` (not the peer), this is a
configuration footgun rather than an attack surface.

## 9. Design smells surfaced by biconditional specs (INFO)

- `MaxJumpOrDefault.lean` / `MaxOooKeysOrDefault.lean` / `ChainParams/IntoPb.lean`: "zero means
  unset" makes `max_jump = 0` / `max_ooo_keys = 0` unrepresentable and `into_pb ∘ from_pb` not the
  identity (default values are zeroed).
- `Pt/Eq.lean` `pt_eq_iff`: `PartialEq` is strictly coarser than structural equality, violating the
  usual expectation that `derive(Clone)`-ed values compare equal to themselves iff structurally
  equal.

## 10. Arithmetic bug in the claimed bound `data.len() <= KEY_SIZE * trim_size()` on `KeyHistory` (MEDIUM / specification, LOW / behavioural)

**Summary.** `src/chain.rs` asserts — as a `hax_lib::requires` precondition on `KeyHistory::add`
and `KeyHistory::remove`, as a `hax_lib::assume!` inside `ChainEpochDirection::key`, and as the
struct-level comment on `KeyHistory::data` — that the key history never exceeds the GC threshold:

```rust
struct KeyHistory {
    // data.len() <= KEY_SIZE*TRIM_SIZE                                            // L94
    data: Vec<u8>,
}
#[hax_lib::requires(... && self.data.len() <= KeyHistory::KEY_SIZE * _params.trim_size())]
fn add(&mut self, k: (u32, [u8; 32]), _params: &pqrpb::ChainParams) { ... }        // L138
#[hax_lib::requires(... && self.data.len() <= KeyHistory::KEY_SIZE * _params.trim_size())]
fn remove(&mut self, ...)                                                           // L174
// inside key():
hax_lib::assume!(params.trim_size() < 119304647
    && self.prev.data.len() <= KeyHistory::KEY_SIZE * params.trim_size());         // L281-282
self.prev.add(k, params);
```

The bound is **false**: the history can grow to almost twice the threshold before `gc` runs.
While attempting to prove `add_spec` with this bound as a *provable invariant* rather than a
hypothesis, the proof agent produced the counterexample below; the statement was then weakened to
the correct bound and the proof completed for the corrected statement. The bound the Rust code
actually maintains is

  * **at rest** (between calls to `key`): `data.len() < KEY_SIZE * trim_size()` (strict — `gc`
    runs whenever `≥` holds, and afterwards at most `max_ooo` live records remain); and
  * **inside `key`, immediately before `gc`**:
    `data.len() ≤ KEY_SIZE * ((trim_size() − 1) + (max_ooo − 1))`.

With the library defaults (`max_ooo_keys = 2000`, `trim_size() = 2201`) the claimed maximum is
2201 records (79 236 B) whereas the true pre-GC maximum is 4199 records (151 164 B).

**Why the bound is wrong.** `key(at)` only clears `prev` when `at > ctr + max_ooo`. In the
boundary case `at = ctr + max_ooo` nothing is cleared and the advancing loop stores every one of
the `at − ctr − 1 = max_ooo − 1` intermediate keys **on top of** whatever is already there, and
`gc` is called only *after* the loop (L288). So the loop can start from `trim_size() − 1` records
(the largest at-rest size) and add `max_ooo − 1` more before anything is trimmed.

**Counterexample** (`max_ooo_keys = 10`, `max_jump = 100`, hence `trim_size() = 12`, threshold
`432 B`), reproduced both by the arithmetic model in
[`docs/key_history_bound_counterexample.py`](./key_history_bound_counterexample.py) and by a test
against the real crate (run on a scratch copy, see below):

| call | `prev` cleared? | records added | records before `gc` | records after `gc` |
|---|---|---|---|---|
| `key(11)` | yes (`11 > 0 + 10`) | 1…10 | 10 (360 B) | 10 |
| `key(14)` | no | 12, 13 | 12 (432 B) | 10 (drops 1, 2) |
| `key(24)` | **no** (`24 = 14 + 10`) | 15…23 | **19 (684 B)** | 10 |

During `key(24)` the 4th to 9th `add` calls execute with `data.len() ∈ {468, …, 648} B`, all
strictly greater than `KEY_SIZE * trim_size() = 432 B`, so the `hax_lib::requires` on `add` is
violated at run time by the crate's own caller. The instrumented Rust test observed
`worst_before_add = 18 * 36 = 648 B` and confirmed `648 + 36 ≤ 36 * (11 + 9) = 720 B`, the
corrected bound.

**Impact.**

- *Specification / proof*: any proof that relies on the `hax_lib::requires` of `add`/`remove` (or on
  the `assume!` in `key`) as a real invariant is unsound — the hypothesis is unsatisfiable on
  reachable states. The Lean specs are **not** affected: `Add.lean` (`add_spec`) only assumes
  `self.data.length + 36 ≤ Usize.max`, `Remove.lean` only assumes
  `my_array_index + 36 ≤ self.data.length`, and `Key.lean` carries the honest hypotheses
  `h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val` and
  `h_kh_cap : self.prev.data.length + 36 * (ats − self.ctr) ≤ Usize.max`. This finding *explains*
  why those weaker hypotheses were the strongest ones that could be discharged.
- *Behavioural*: memory use of `prev` is up to ~2× what the comment promises (bounded, so not a
  DoS vector). The 32-bit `trim_size() < 119304647` guard in the same `requires` is also stated
  against the wrong quantity: what must not overflow is `KEY_SIZE * (trim_size − 1 + max_ooo − 1)`,
  not `KEY_SIZE * trim_size`.

**Related off-by-one surfaced by the same counterexample.** After `key(24)` the record with tag 13
survives `gc` (horizon `23 − 10 = 13`, and `gc` drops only tags *strictly below* the horizon,
L152), yet `prev.get(13, 24, ..)` returns `Err(KeyTrimmed(13))` because `get` tests
`at + max_ooo < current_ctr` with the *post-increment* counter 24 (L192). `gc` and `get` therefore
disagree at the window boundary by exactly one: a key that is still stored is reported as trimmed.
This is consistent with `Get.lean`, whose postcondition pins the `KeyTrimmed` branch to
`ats + maxOoo < self.ctr`, and with the `KeyTrimmed`-vs-`KeyAlreadyRequested` case split in
`Key.lean`; both specs faithfully describe the asymmetric behaviour rather than a symmetric window.

**Fixes.**

1. Correct the comment on `KeyHistory::data` and the `hax_lib::requires`/`assume!` to
   `self.data.len() <= KEY_SIZE * ((trim_size() - 1) + (max_ooo_keys_or_default() - 1))`
   (or drop the length clause from `add`/`remove`, which only need `len + 36 ≤ usize::MAX` and
   `idx + 36 ≤ len` respectively — exactly what `add_spec`/`remove_spec` require).
2. Either call `gc` inside the loop (restoring `len < KEY_SIZE * trim_size()` as a true
   invariant) or accept the larger bound and size `Vec::with_capacity` accordingly.
3. Make `get` and `gc` agree on the window: use `at + max_ooo < current_ctr - 1` in `get`, or
   pass the pre-increment counter, or make `gc` use `>=`.

**Verification of this finding.** `docs/key_history_bound_counterexample.py` reproduces the table
above and, over 2000 random 30-step walks, observed a maximum pre-GC size of exactly
`(trim_size − 1) + (max_ooo − 1) = 20` records while the at-rest invariant `< trim_size` never
failed. Two `cargo test` cases exercising the real `ChainEpochDirection::key`, `KeyHistory::add`,
`gc` and `get` (added to a scratch copy of the crate, not to `src/`, per project policy) pass and
assert the numbers quoted here. The full demonstration file — `src/chain.rs` plus the two tests —
is [`docs/chain.rs`](./chain.rs); the tests alone are in
[`docs/key_history_bound_counterexample.rs.txt`](./key_history_bound_counterexample.rs.txt).

---

## Notes / limitations

- All findings are grounded in hypotheses the existing (proved) spec theorems require, or in
  postconditions they establish. Items 1, 4 and 10 are the recommended priorities (item 1 for
  robustness, items 4 and 10 for correcting erroneous source annotations/comments that informally
  reason about arithmetic bounds).
- Finding 10 is the only one backed by an executable counterexample (Python model + two Rust tests
  in `docs/`); the Rust tests were run on a scratch copy because `src/` is a pinned upstream tree.
- The full `lake build` of all 221 spec files was not re-run for this report; only the chain
  modules touched by findings 1–3 were built.
