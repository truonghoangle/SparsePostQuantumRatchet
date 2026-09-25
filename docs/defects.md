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

## 11. `compare` silently truncates when slice lengths differ — potential authentication bypass (MEDIUM)

**Location**: `src/util.rs`, lines 25–33.

```rust
pub(crate) fn compare(lhs: &[u8], rhs: &[u8]) -> u8 {
    let mut r: u8 = 0;

    for i in 0..lhs.len() {
        r |= lhs[i] ^ rhs[i];
    }

    is_non_zero(r)
}
```

**Defect.** The loop iterates over `0..lhs.len()` only. The equal-length precondition
(`lhs.len() == rhs.len()`) is guarded by `#[cfg_attr(hax, hax_lib::requires(...))]`, which is
**erased in non-hax builds** — there is no runtime check. Two failure modes result:

| Condition | Behaviour |
|---|---|
| `rhs.len() > lhs.len()` | Trailing bytes in `rhs` are never examined; `compare` returns `0` (equal) even when the slices differ beyond `lhs.len()`. This is a **silent truncation** that could allow an authentication bypass if an attacker controls one slice's length. |
| `rhs.len() < lhs.len()` | Index `rhs[i]` panics at `i == rhs.len()`, causing a denial-of-service and leaking timing information (panic vs. normal return). |

**Current callers are safe.** Both `verify_ct` and `verify_hdr` in `src/authenticator.rs` pass
`expected_mac` (whose length is checked by a `hax_lib::requires` with `MACSIZE`) and the output of
`mac_ct`/`mac_hdr` (which always returns exactly `MACSIZE` bytes). So the bug is **latent** today.

**Why it still matters.** `compare` is a security-critical constant-time primitive. The original
code in `libcrux-ml-kem/src/constant_time_ops.rs` operates on fixed-size arrays where a length
mismatch is impossible at the type level. When it was ported to accept slices in this codebase,
the type-level safety was lost and replaced only with a hax-time annotation that has no runtime
effect. Any future caller passing mismatched-length slices would silently get a wrong answer or a
panic.

**Fix**: add a runtime assertion at the top of `compare`:

```rust
assert_eq!(lhs.len(), rhs.len());
```

Alternatively, return `1` (not-equal) when lengths differ, which avoids panics entirely:

```rust
if lhs.len() != rhs.len() {
    return 1;
}
```

---

## 12. Audit of the constant-time comparison / FO-transform path (NO DEFECT FOUND in SPQR; libcrux 0.0.7 clean)

**Motivation.** Several ML-KEM implementations shipped bugs in the Fujisaki–Okamoto re-encryption
check where the comparison was incomplete or the constant-time select was a no-op, so
decapsulation returned a value that depended on the decrypted message even when re-encryption
failed (key-recovery class). This item records a targeted check of the analogous code reachable
from SPQR.

**Where the FO transform lives.** *Not* in `src/`. `incremental_mlkem768::decaps` delegates to
`libcrux_ml_kem::ind_cca::incremental::decapsulate_compressed_key`, which concatenates
`ct1 ‖ ct2` into the full 1088-byte ciphertext and calls `ind_cca::decapsulate`. The FO check is
`compare_ciphertexts_select_shared_secret_in_constant_time(ciphertext, expected_ciphertext,
shared_secret, implicit_rejection_shared_secret)` in `libcrux-ml-kem-0.0.7/src/constant_time_ops.rs`.

**Checked in libcrux-ml-kem 0.0.7 (pinned in `Cargo.lock`).**

| Property | Result |
|---|---|
| `compare` iterates `0..lhs.len()` over the **full** `CIPHERTEXT_SIZE` array | ✔ complete comparison |
| `inz(v) = ((!v as u16).wrapping_add(1) >> 8) & 1` | ✔ exhaustively verified `= (v≠0)` for all 256 bytes |
| `select_ct`: `mask = is_non_zero(sel).wrapping_sub(1)`; `out = (lhs & mask) \| (rhs & !mask)` | ✔ verified: `sel=0 → lhs`, all `sel∈1..=255 → rhs` (implicit-rejection secret) |
| Both candidate secrets computed **before** the select, unconditionally | ✔ no data-dependent early return |
| `#[inline(never)]` + `black_box` on compare/select wrappers | ✔ |

**Checked in SPQR's own port (`src/util.rs`, used by `Authenticator::verify_ct/verify_hdr`).**

- `inz` uses `((v \| (!v).wrapping_add(1)) >> 8) & 1` lifted to `u16`. Proved in
  `Spqr/Specs/Util/Inz.lean` (`inz_spec`) and exhaustively tested.
- `compare` proved in `Spqr/Specs/Util/Compare.lean`: `0 ↔ ∀ j, lhs[j] = rhs[j]`.
  `verify_ct_spec`/`verify_hdr_spec` give `Ok () ↔ expected_mac = mac_*(…)`. All three modules
  rebuilt with `lake build` for this item.
- Release AArch64 assembly inspected: `compare` inlines into the verifiers as a NEON `eor/orr`
  accumulation loop plus scalar tail — no early exit, no data-dependent branch; `is_non_zero`
  survives out-of-line and branchless. The only branch is the final `!= 0` on the public
  accept/reject outcome.
- Protocol level (`v1/unchunked/send_ek.rs::recv_ct2`): `decaps` (never fails, implicit
  rejection) → HKDF → `auth.update` → `verify_ct(…)?`. On MAC failure, `?` discards the updated
  state and returns `Err(InvalidCtMac)` with **no** secret-derived data; `EpochSecret` is built
  only on the `Ok` path.
- Chunked path: `decoded_message()` yields exactly `pts_needed*2` bytes, so
  `split_off(CIPHERTEXT2_SIZE)` / `split_off(HEADER_SIZE)` always yield a 32-byte MAC, satisfying
  the `expected_mac.len() == MACSIZE` requirement item 11 relies on.

**Residual observations (hardening, not bugs).**

1. Item 11 still stands: `compare` has no runtime length guard; all current callers are safe by construction.
2. SPQR's `compare` lacks libcrux's `#[inline(never)]`; it is inlined and auto-vectorised. Still
   branchless, but this relies on LLVM rather than a barrier. Adding `#[inline(never)]` is cheap hardening.
3. The Lean model of `core::hint::black_box` is the identity, so the spec theorems establish
   *functional* correctness only; constant-time behaviour was checked via assembly inspection.
4. On any `libcrux-ml-kem` bump, re-run the two exhaustive checks (`inz` over all bytes;
   `select_ct` over all selectors) — milliseconds, and they catch the no-op-mask bug class.

---

## 13. `PolyEncoder::from_pb` does not validate per-polynomial point counts → `debug_assert` panic / silently wrong chunks (MEDIUM)

**Specs that expose it**

- `Spqr/Specs/Encoding/Polynomial/PolyEncoder/PointAt.lean`, `ChunkAt.lean`, `NextChunk.lean` all
  require
  `h_admissible : ∀ pts, self.s = .Points pts → ∀ j < 16, len ∈ {0, 1, 3, 5, 30, 34, 36}`.
- `Spqr/Specs/Encoding/Polynomial/Poly/FromCompletePoints.lean` (`from_complete_points_spec`)
  requires the same `h_len_ok` disjunction; there is *no* spec for the `_ =>` fallback arm.
- `Spqr/Specs/Encoding/Polynomial/PolyEncoder/FromPb.lean` (`from_pb_spec`) has **no** such
  hypothesis and proves `Ok` for any `pb.pts` whose 16 entries have even length.

**Rust defect** (`src/encoding/polynomial.rs`)

`from_pb` (L573-603) only checks `pts.len() % 2 == 0` per slot. The admissible-length fact is
carried into `point_at` solely by `hax_lib::assume!(pt_vec.len() == 0 || … || 36)` (L646-654),
which is erased at runtime. On the first cache miss `point_at` calls
`Poly::from_complete_points`, whose fallback arm is

```rust
_ => { debug_assert!(false, "missing precomputed poly of size {}", pts.len()); … }   // L310
```

| Build | Behaviour with a persisted `PolynomialEncoder` whose slots hold 2 points each |
|---|---|
| debug | **panic** `missing precomputed poly of size 2` on the 3rd `next_chunk()` |
| release | `debug_assert!` is compiled out; the fallback Lagrange path runs and emits chunks (observed all-zero for the probe input), i.e. the encoder produces data for a state the protocol never defines |

Reproduced by `encoder_from_pb_inadmissible_len` in
[`docs/polynomial_from_pb_counterexample.rs.txt`](./polynomial_from_pb_counterexample.rs.txt)
(run against a scratch copy of the crate with the `test-utils` feature). Reachable from any
chunked-state `from_pb` (`v1/chunked/send_ek/serialize.rs`, `send_ct/serialize.rs`) given a
prost-valid but semantically inconsistent state blob — the same trust boundary as item 1.

**Fix**: in `PolyEncoder::from_pb`, reject slots whose `pts.len()/2 ∉ {0,1,3,5,30,34,36}` (and
`polys[i].len()/2 > MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1`) with `SerializationInvalid`. That would
let `h_admissible` become a provable invariant instead of a hypothesis.

## 14. `PolyDecoder::from_pb` does not bound stored point-set sizes → `MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` precondition violated at runtime (LOW–MEDIUM)

**Specs that expose it**

- `Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean` and friends are stated for
  arbitrary `pts.length` (only `+1 ≤ Usize.max`), but the Rust carries
  `#[hax_lib::requires(pts.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1)]` (L105, L143, L230)
  and the struct refinement `coefficients.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1 + 1` (L86).
- `Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean` (`from_pb_spec`) proves `Ok` with
  `decoder.pts_needed = pb.pts_needed` for any `pts_needed : u32` and any number of 4-byte points
  per slot — nothing ties them to `MAX_STORED_POLYNOMIAL_DEGREE_V1` or to the fixed V1 message
  sizes.

**Rust defect** (`src/encoding/polynomial.rs` L815-854)

`from_pb` validates `pts.len() != 16` and `% 4`, nothing else. `into_pb` (L800) and
`decoded_message` (L949-951) both rely on `hax_lib::assume!(… ≤ MAX_*)`, erased at runtime.
The probe `decoder_from_pb_interpolate_oversized` builds a decoder with `pts_needed = 1600` and
100 points per slot (x = 1..100, so every lookup misses and `lagrange_interpolate` runs on 100
points — ~3× the stated maximum); `decoded_message()` returns `Some(3200 bytes)` without error.

Consequences: (a) the `hax_lib::requires`/`refine` annotations on the polynomial core are
*not* invariants of the deployed code — they are only true for states the honest protocol
produces; (b) O(N²) interpolation cost is controlled by the state blob (`pts_needed` is a
free `u32`), so a corrupted state can make `recv` arbitrarily slow — bounded only by the
protobuf size. No memory-safety issue: all indexing is bounds-checked.

**Fix**: in `PolyDecoder::from_pb`, require `pts_needed ≤ 576` (the V1 maximum noted in the
struct comment, L743) and each slot `len/4 ≤ 2·MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 71`,
returning `SerializationInvalid` otherwise.

## 15. Remaining `sorry`s and axioms bounding what the specs can claim (INFO)

Not Rust defects, but they delimit findings above:

- `Spqr/Specs/Lib/DecodeState.lean:54` — `decode_state` round-trip left as `sorry` because
  the prost-generated `Message` impl is replaced by `sorry` in translation (issue #102). Hence
  nothing about *which* state blobs `decode_state` accepts is formally established; items 1,
  13, 14 all sit behind this boundary.
- `Spqr/Specs/Aeneas/MapCollectBridge.lean` — single assumed bridge for `.map().collect()`
  (aeneas#1043); `ConstPolysToPolys.lean` depends on it.
- `SrcTranslated/Funs.lean` still contains four `sorry`-using declarations (reported by
  `lake build`), all in generated protobuf code.

---

# Part II — Logic defects not tied to erased `hax_lib` annotations

The items above mostly stem from `assume!`/`requires` that vanish at runtime. The following
are ordinary logic bugs that the spec *postconditions* pin down directly.

## 16. `Poly::serialize`/`Poly::deserialize` are not inverses on the zero polynomial → `PolyEncoder` state round-trip fails (MEDIUM)

**Specs that expose it**

- `Spqr/Specs/Encoding/Polynomial/Poly/Zero.lean` (`zero_spec`): `result.coefficients.length = 0`.
- `Spqr/Specs/Encoding/Polynomial/Poly/Serialize.lean` (`serialize_spec`):
  `result.length = 2 * self.degree` — so a zero polynomial serialises to `[]`.
- `Spqr/Specs/Encoding/Polynomial/Poly/Deserialize.lean` (`deserialize_spec`) explicitly requires
  `h_nonempty : serialized.length ≠ 0`; the docstring states *"rejects empty … input"*.
- `Spqr/Specs/Encoding/Polynomial/PolyEncoder/FromPb.lean` (`FromPbWellFormed`) requires every
  `polys[j]` to be non-empty for the `Polys` branch to succeed.

Together these say: **`from_pb ∘ into_pb` is not the identity whenever any of the 16 stored
polynomials is zero.**

**Rust defect** (`src/encoding/polynomial.rs`)

```rust
pub fn serialize(&self) -> Vec<u8> { /* 2 bytes per coefficient; zero poly → [] */ }   // L329
pub fn deserialize(serialized: &[u8]) -> Result<Self, _> {
    if serialized.is_empty() || serialized.len() % 2 == 1 { return Err(SerializationInvalid) } // L343
```

`Poly::zero(_)` has **no** coefficients (`Vec::with_capacity`, L94–97), and `from_complete_points`
of an empty point list returns `lagrange_sum([], [])` = zero polynomial (L302, L279). So any
`PolyEncoder` in `EncoderState::Polys` with an empty slot serialises to `polys[j] = []` and can
never be reloaded.

**When is a slot empty?** Whenever the encoded message has fewer than 32 bytes: `encode_bytes`
round-robins 2-byte words over 16 slots, so a 10-byte message leaves 11 slots with 0 points. The
V1 protocol only encodes 96/1152/960/160-byte messages, so **the honest V1 protocol never hits
this**; but the encoder is a public, `pub struct`, generic component and its own tests
(`encode_and_decode_small`, L972) use exactly such a short message.

**Reproduction** ([`docs/poly_roundtrip_counterexample.rs.txt`](./poly_roundtrip_counterexample.rs.txt),
release build):

```
encoder_polys_roundtrip_with_empty_poly: polys = 16, empty polys = 11
from_pb(into_pb(e)) = Some(SerializationInvalid)      ← FAILED
encoder_polys_roundtrip_v1_size:                       ← ok (control, 96-byte message)
```

**Fix**: either make `deserialize` accept `[]` as the zero polynomial (drop the `is_empty()`
check — the loop already handles length 0), or make `serialize` emit `[0, 0]` for the zero
polynomial. The first is simpler and also matches `zero_spec`.

## 17. `PolyDecoder::is_complete` is write-never → dead field, redundant O(N²) work, and a misleading spec surface (LOW)

**Specs that expose it**

- `Spqr/Specs/Encoding/Decoder/New.lean`: `pd.is_complete = false`.
- `Spqr/Specs/Encoding/Decoder/AddChunk.lean`, `PolyDecoder/IntoPb.lean`, `PolyDecoder/FromPb.lean`:
  `is_complete` is *preserved* by every operation.

No spec ever establishes `is_complete = true`, because no Rust code path does.

**Rust defect** (`src/encoding/polynomial.rs`)

`grep is_complete` finds five sites: declaration (L760), `false` in `new_with_poly_count`
(L789), copy in `into_pb`/`from_pb` (L797, L851), and the *read* at the top of
`decoded_message` (L912: `if self.is_complete { return None; }`). It is never assigned `true`.
Consequences:

1. The early-return in `decoded_message` is dead code; a fully-received decoder recomputes the
   Lagrange interpolation (up to 16 polynomials of degree ≤ 35) on **every** call. The chunked
   state machine calls `decoded_message()` after each `add_chunk`, so once a message is complete
   any further late chunk for that epoch triggers a full redundant decode.
2. The persisted `PolynomialDecoder.is_complete` protobuf field carries no information, yet
   `from_pb` honours it: a state blob with `is_complete = true` makes `decoded_message()` return
   `None` forever, silently stalling that epoch of the ratchet (no error is surfaced).

Confirmed by `decoder_is_complete_never_set` in
[`docs/decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt): after a successful
1088-byte decode, `into_pb().is_complete == false`.

**Fix**: either set `is_complete = true` (and drop the point sets) when `decoded_message`
succeeds — which the state machines already treat as terminal — or delete the field and the
protobuf column. If kept, `from_pb` should reject `is_complete = true` with a non-empty `pts`.

## 18. Duplicate chunk index → last write wins (confirms item 4 behaviourally) (LOW)

`decoder_duplicate_index_last_wins` in the same probe file feeds two chunks with index 0 from two
different messages and observes the decoder output follows the **second** one
(`"ABCDEFGHIJ"`), contradicting the source comment *"This will discard new points whose X value
matches a previous old point"* (L896–898). The Lean models in
`Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean` / `FromPb.lean`
(`.eq ⇒ … dropLast ++ [p]`) are correct; the comment is not. Behaviourally benign for an honest
peer and MAC-protected against a malicious one, but it means a replayed chunk with a bit-flip
*does* corrupt the reconstruction until the MAC check fails, rather than being ignored.

## 19. Unauthenticated chunk poisoning is *persistent*: one forged low-index chunk permanently stalls the epoch (MEDIUM, protocol-level DoS)

Sharpens items 4 and 18. Those items note that a same-index chunk with a different payload
overwrites the stored point and that "tampering is caught by the MAC". The MAC check happens only
*after* `decoded_message()` returns `Some` (in `recv_header`/`recv_ct2`), and on failure the whole
`recv` returns `Err` — the *poisoned decoder state is not rolled back or flagged*, because the
state that was already persisted on the earlier `Ok` path contains the poisoned point.

**Specs that expose it**

- `Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean` / `Decoder/AddChunk.lean`: the
  guard is `poly_idx < necessary_points(i) ∨ pts[poly].len() < necessary_points(i)`. For any
  `chunk.index < necessary_points` the first disjunct is *unconditionally* true, so the point is
  always inserted, and the `IsSortedPushResult` `.eq` branch is *replacement*
  (`FunsExternal.lean:2146`, `sorted_vec 0.8.6 SortedSet::push`).
- `Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean` / `FromPb.lean`: every stored point
  (including a replaced one) round-trips through the persisted protobuf unchanged.
- `Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean`: `Message::deserialize`
  performs no authentication; `Chunk.index`/`Chunk.data` are attacker-controlled.

**Rust defect** (`src/encoding/polynomial.rs` L888–899, `src/v1/chunked/*.rs`)

1. An on-path attacker sends `{epoch, Hdr/Ek/Ct1/Ct2, index: k, data: garbage}` with `k` below
   `necessary_points` (e.g. `k = 0`) for the epoch currently being received.
2. `add_chunk` replaces the honest `x = k` point (or pre-seeds it if not yet received).
   `decoded_message()` is still `None` → `recv` returns `Ok` and the poisoned decoder is
   **persisted** in the returned `SerializedState`.
3. When the honest chunks complete the message, interpolation uses the garbage point →
   `verify_hdr`/`verify_ct` fails → `recv` returns `Err(MacVerifyFailed)`. The caller keeps the
   *old* (poisoned) state. Every later honest chunk yields the same `Err`, because the only way to
   overwrite the `x = k` point is another chunk with index exactly `k`, and the honest sender
   emits index `k` again only after wrapping through 65 536 chunks (`PolyEncoder::next_chunk`).
   (Honest indices `≥ necessary_points` are dropped once the slot is full, so they never help.)

Net effect: **one forged, unauthenticated ~40-byte message permanently blocks the PQ ratchet
epoch for the receiver** — no new epoch secret can ever be derived for that direction, and the
peer never learns why. In contrast, the design intent (comment at L896–898: *discard* new points
with a matching X) would make the attack a no-op once the honest chunk arrives first.

Reproduced by `poisoned_low_index_point_persists_and_wins` in
[`docs/decoder_poison_persistence_counterexample.rs.txt`](./decoder_poison_persistence_counterexample.rs.txt)
(run on a scratch copy with `--features test-utils`; the honest `index 0` chunk is received first,
then poisoned, persisted through `into_pb`/`from_pb`, and the completed decode never matches the
original message even after ten more honest chunks).

**Fix options** (any one suffices): (a) use `find_or_push` — first write wins, matching the source
comment; (b) on MAC failure, reset the decoder for that epoch (drop `pts`) so honest retransmits
can recover; (c) keep *both* candidate `y` values per `x` and try alternatives on MAC failure.
Option (a) is the smallest change; note it makes the Lean model in `AddChunk.lean` (replacement)
*wrong* and it would need to be updated to the `find_or_push` semantics.

---

# Part III — Defects in the hand-written Lean models (trusted base)

## 20. `VecDeque::into_iter` model yields the wrong elements whenever `head ≠ 0` (HIGH for soundness of any future spec built on `Chain::into_pb`)

**Location**: `SrcTranslated/FunsExternal.lean` L3733–3759,
`alloc.collections.vec_deque.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next`.

The rest of the project deliberately uses a **growing-list model** for `VecDeque`
(`push_back` appends to `buf`; `pop_front` increments `head` and decrements `length`;
`index`/`index_mut` read `buf[head + idx]`; see L1241–1381). Under that model the logical
elements are `buf[head .. head+length)`. The `into_iter.next` model instead

```lean
if deq.length == 0 then ok (none, intoIter)
else
  let newhead ← (Usize.wrapping_add deq.head 1) % len   -- ← ring-buffer arithmetic
  ok (deq.buf.get? deq.head, { inner := { buf, head := newhead, length := len } })
```

- **never decrements `length`**, so the iterator never terminates on its own; and
- **wraps `head` modulo `length`**, which is the *ring-buffer* invariant of real `std`, not the
  growing-list invariant used everywhere else. It is therefore internally inconsistent with the
  project's own `pop_front`/`push_back`/`index` models.

**Executable counterexample**
([`docs/vecdeque_into_iter_model_counterexample.lean.txt`](./vecdeque_into_iter_model_counterexample.lean.txt),
run with `lake env lean`): after one `pop_front` the growing-list deque is
`{buf := [10,20,30], head := 1, length := 2}` (Rust would iterate `20, 30, None`). Four calls to
the model's `next` yield

```
Aeneas.Std.Result.ok ([some 20, some 10, some 20, some 10], 2)
```

i.e. it returns `10` (the *popped* element), never returns `30`, never terminates, and `length`
is still `2`. Any theorem about `Chain::into_pb` that unfolds this instance would prove
properties of a serialisation containing already-discarded epochs and missing the newest one.

**Current impact**: `Chain.into_pb` (`Funs.lean` L5875 ff.) *does* use this instance, but every
`.map(...).collect()` is routed through the `sorryAx`-based bridge (item 15,
`Spqr/Specs/Aeneas/MapCollectBridge.lean`), and no spec theorem currently states a postcondition
for `Chain::into_pb`/`from_pb` — so nothing proved today is falsified. It is a latent unsoundness
in the trusted base that will bite as soon as chain-serialisation specs are written (the natural
next step after `SendKey.lean`/`RecvKey.lean`, both of which do move `head`).

**Fix**: replace the body with the growing-list semantics consistent with `pop_front`:

```lean
if deq.length.val = 0 then ok (none, intoIter)
else match deq.buf.val[deq.head.val]? with
  | none => fail .panic
  | some elem => do
    let head' ← deq.head + 1#usize
    let len'  ← deq.length - 1#usize
    ok (some elem, ⟨{ deq with head := head', length := len' }⟩)
```

and add a `@[step]` spec mirroring `pop_front_spec_nonempty`.

---

## 21. `Chain::from_pb` does not validate `next_root` length, `links` non-emptiness, or epoch ordering invariants → panics or silent misbehaviour from corrupted state (MEDIUM)

**Extends item 1** (which covers `ChainEpochDirection::from_pb`) to the `Chain`-level deserialiser.

**Rust defect** (`src/chain.rs`, L434–452)

```rust
pub(crate) fn from_pb(pb: pqrpb::Chain) -> Result<Self, Error> {
    Ok(Self {
        dir: pb.direction.try_into().map_err(|_| Error::StateDecode)?,
        current_epoch: pb.current_epoch,
        send_epoch: pb.send_epoch,
        next_root: pb.next_root,                  // ← no length check
        links: pb.links.into_iter().map(…).collect()?,  // ← may be empty
        params: pb.params.ok_or(Error::StateDecode)?,
    })
}
```

Three invariants established by `Chain::new` are not verified on deserialisation:

| Invariant | Established by `new` | Consumers that assume it | Failure mode |
|---|---|---|---|
| `next_root.len() == 32` | `genr8r[0..32].to_vec()` (L345) | `add_epoch` → `hkdf_to_slice(&self.next_root, …)` (L358) | No panic (HKDF accepts any salt length), but KDF output differs from what a correctly-constructed chain would produce — silent state divergence between peers |
| `links.len() ≥ 1` | `VecDeque::from([…])` (L341) | `epoch_idx` computes `links.len() - 1 - back` (L381); `send_key` indexes `self.links[i]` (L398) | Arithmetic underflow on `0 - 1` → panic in debug, wrapping index in release → out-of-bounds panic |
| `send_epoch ≤ current_epoch` | Both start at 0 (L339–340); `send_epoch` only advances to ≤ `current_epoch` in `send_key` (L390) | `send_key` rejects `epoch < self.send_epoch` (L385–386); `epoch_idx` rejects `epoch > self.current_epoch` (L373–374) | If `send_epoch > current_epoch`, *every* `send_key(epoch)` call fails: `epoch ≤ current_epoch < send_epoch` → `Err(SendKeyEpochDecreased)`, or `epoch > current_epoch` → `Err(EpochOutOfRange)` — chain is permanently stuck |

**Impact**: same class as item 1 — a prost-valid but semantically corrupt state blob turns
subsequent operations into panics or silent divergence. No security impact in the absence of a
state-blob injection vector. The `next_root` length case is particularly subtle because it does
not panic; peers would silently derive different chain keys after the next `add_epoch`.

**Fix**: add checks in `Chain::from_pb`:

```rust
if pb.next_root.len() != 32 { return Err(Error::StateDecode); }
// … after collecting links:
if links.is_empty() { return Err(Error::StateDecode); }
if pb.send_epoch > pb.current_epoch { return Err(Error::StateDecode); }
```

---

## 22. `Authenticator::from_pb` does not validate `root_key` / `mac_key` lengths → HMAC with wrong-length keys (LOW)

**Rust defect** (`src/authenticator/serialize.rs`, L16–21)

```rust
pub fn from_pb(pb: &proto::pq_ratchet::Authenticator) -> Self {
    Self {
        root_key: pb.root_key.clone(),   // ← no length check
        mac_key: pb.mac_key.clone(),     // ← no length check
    }
}
```

`Authenticator::new` always produces 32-byte keys via `hkdf_to_vec(…, 64)[..32]` and `[32..]`
(L51–53). `from_pb` accepts arbitrary-length keys. Consequences:

- **`mac_key` wrong length**: HMAC-SHA256 handles any key length (pads/hashes as needed), so no
  panic, but the MAC tag space changes. A 0-byte `mac_key` means every authenticator produces
  the same tags — an attacker who can inject a state blob with `mac_key: []` can then forge
  ciphertext MACs.
- **`root_key` wrong length**: similarly, `update` concatenates `root_key` with the epoch secret
  as IKM to HKDF (L45), so a short/empty `root_key` weakens forward secrecy of the
  authenticator chain.

**Impact**: low. Requires state-blob injection (same attack model as items 1 and 21). No
runtime panic. The HMAC/HKDF APIs are length-agnostic, so the failure is purely semantic.

**Fix**: validate in `from_pb`:

```rust
if pb.root_key.len() != 32 || pb.mac_key.len() != 32 { return Err(…); }
```

(Requires changing the return type to `Result<Self, Error>` and updating the two call sites in
`src/v1/unchunked/send_ek/serialize.rs` and `src/v1/unchunked/send_ct/serialize.rs`.)

---

## 23. `RoundRobinEncoder::chunk_at` panics on empty input; `RoundRobinDecoder::is_complete` is never set (LOW, test-only code)

**Rust defect** (`src/encoding/round_robin.rs`)

Two issues in the `#[cfg(test)]`-only round-robin encoder/decoder:

1. **Empty-input panic** (L17): `chunk_at` computes `idx as usize % self.num_chunks()`. For
   empty input, `num_chunks()` returns 0, so this is a division-by-zero panic. Similarly, for
   input whose length is not a multiple of 32, `chunk_at` slices `data[lb..ub]` where
   `ub = lb + 32` may exceed `data.len()` — index-out-of-bounds panic.

2. **`is_complete` never set** (L76): `decoded_message` returns `None` when
   `self.is_complete` is true, but no code path ever sets it to `true`. This mirrors item 17
   (`PolyDecoder::is_complete`). Unlike the `PolyDecoder` case, this only affects test code,
   but means `decoded_message()` re-checks `can_reconstruct()` on every call after completion
   instead of short-circuiting.

**Impact**: negligible — `round_robin.rs` is gated behind `#[cfg(test)]` (L3) and is not used
in any protocol path.

---

## Notes / limitations

- All findings are grounded in hypotheses the existing (proved) spec theorems require, or in
  postconditions they establish. Items 1, 19, 10, 20 and 21 are the recommended priorities
  (item 1 for robustness, item 19 for a concrete protocol-level DoS, item 10 for correcting
  erroneous source annotations, item 20 for the soundness of the Lean trusted base, item 21
  for silent state divergence). Items 21–23 extend the deserialisation-validation theme of
  item 1 to `Chain::from_pb`, `Authenticator::from_pb`, and the test-only round-robin codec.
- Findings 10, 13, 16, 17, 18, 19 and 20 are backed by executable counterexamples in `docs/`;
  the Rust tests were run on a scratch copy because `src/` is a pinned upstream tree.
- A full `lake build Spqr SrcTranslated` (2553 jobs) was re-run for the 2026-09-24 additions
  (items 19–20) and completes with only the two known `sorry` warnings (`DecodeState.lean`,
  `MapCollectBridge.lean`).
- Axiom audit (`#print axioms`) on representative theorems: `send_key_spec` and `key_spec_*`
  depend only on `hkdf_to_slice_spec` and the `get_unchecked{,_mut}` externals;
  `point_at_spec` additionally depends on `sorryAx` via the `MapCollectBridge` (item 15).
  `mul2_u16_spec` is axiom-free because `aeneas-config.yml` excludes the accelerated
  (`PCLMULQDQ`/`PMULL`) path, so the SIMD GF(2¹⁶) multiplication is *not* covered by any proof —
  only the portable `unaccelerated::mul` is.
