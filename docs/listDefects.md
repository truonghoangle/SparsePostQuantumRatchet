# Complete Defect List: D1–D66

> **Version:** 2.0 — 2026-10-04
>
> Self-contained, sequentially ordered reference for every defect D1–D66. Each entry has
> severity, Lean spec(s), Rust location, consequence, reproduction evidence, and fix.
> For thematic grouping see [`report.md`](./report.md); for the original narrative see
> [`defects.md`](./defects.md).
>
> **D9, D12, D15 are audit notes (INFO / NO DEFECT).**
>
> **D41–D52** were discovered via methods M1–M12 (model checking, Miri, fuzz, property
> testing, etc.). **D53–D66** were discovered via methods M13–M18 (refinement checking,
> compositional invariant verification, termination analysis, information-flow typing,
> symbolic state-machine model checking, trusted-base/axiom soundness audit) — informed
> by surveying online Lean verification repositories for similar cryptographic protocols.

---

## Fix Status Summary

All defects D1–D40 were identified against SPQR **v1.5.0** (`Cargo.toml`) as consumed by
libsignal commit `a47ba487` (2026-03-17). As of the analysis date (2026-10-04), **none of the
40 defects have been fixed in the SPQR crate**. libsignal's clone-then-commit-after-MAC
pattern externally mitigates the message-level attacks (D24, D25, D38, D39) for network-only
attackers, but the SPQR code itself remains unchanged.

| Status | Count | Defect IDs |
|---|---|---|
| 🔴 **Unfixed** | 37 | D1, D2, D3, D4, D5, D8, D10, D11, D13, D14, D16, D17, D18, D19, D21, D22, D26, D27, D28, D29, D30, D31, D32, D33, D34, D40, D41, D43, D44, D45, D46, D47, D48, D49, D50, D53, D54, D57, D58, D59, D60, D63, D64, D65, D66 |
| 🟡 **Unfixed (mitigated by host)** | 4 | D24, D25, D38, D39 — mitigated in libsignal only |
| ⚪ **N/A (audit note)** | 3 | D9, D12, D15 |
| 🟢 **No fix needed** | 2 | D6, D7 — latent spec observations, no behavioural impact |
| ✅ **Fixed** | 10 | D20 — Lean model corrected; D23 — audit comments added; D35 — gap-documenting theorems added; D36 — wrong-mapping theorems added; D37 — truncation-bound theorem added; D42 — divergence theorem added; D51 — erased-bound audit comments added; D52 — is_complete gap theorem added; D55 — IKM collision theorem added; D56 — usize-bound theorem added |
| 🔵 **Unfixed (spec-only)** | 2 | D61, D62 — Lean model, dead code, or annotation issues |

> **Note on D24/D25/D38/D39.** These are classified as 🟡 rather than 🔴 because libsignal's
> clone-then-commit-after-MAC pattern discards the mutated state on MAC failure. The SPQR
> library itself remains vulnerable; only the Signal integration absorbs the attack. Other
> embedders of the `spqr` crate are fully exposed.

---

## D1. `ChainEpochDirection::from_pb` — three panic paths (HIGH; blob)

**Status.** 🔴 **Unfixed** in SPQR v1.5.0. `chain.rs` L306–312 still performs no validation.

**Specs.** `FromPb.lean` proves `Ok` with no hypotheses. `NextKeyInternal.lean` needs
`h_next_len : next.length = 32`. `Get.lean` needs `h_data_aligned : data.length % 36 = 0`.
`Gc.lean` needs `h_prev_ctr : data.length ≤ 36 * ctr`.

**Rust.** `chain.rs` L306–312: `from_pb` copies `ctr`, `next`, `prev` verbatim, zero validation.

**Consequence.**

| Corrupted field | Consumer | Failure |
|---|---|---|
| `next.len() ≠ 32` | `next_key_internal` L241 | **panic** (`copy_from_slice`) |
| `prev.len() % 36 ≠ 0` | `KeyHistory::get` L191 | **panic** (`assert_eq!`) |
| `prev` too large for `ctr` | `KeyHistory::gc` L149 | **panic** (`assert!`) |

Corrupted state round-trips through `into_pb` (crash loop).

**Lean.** `CorruptedBlobs.lean`: 46 theorems, 11 phases — `from_pb_never_fails`,
`recv_key_never_ok_bad_next`, etc.

**Reproduced.** [`corrupted_blob_counterexample.rs.txt`](./corrupted_blob_counterexample.rs.txt).

**Fix.** Validate in `from_pb`; return `Error::StateDecode` on any violation.

---

## D2. `u32` overflow in `KeyHistory::get` (MEDIUM; message + config)

**Status.** 🔴 **Unfixed.** `chain.rs` L192 still uses unchecked addition.

**Specs.** `Get.lean`: `h_ooo_no_overflow : at1 + maxOoo ≤ U32.max`.

**Rust.** `chain.rs` L192: `at + params.max_ooo_keys_or_default()` wraps near `u32::MAX`.

**Consequence.** Debug: panic. Release: valid key reported as `KeyTrimmed`.

**Fix.** `checked_add` or `saturating_add`.

---

## D3. `u64→usize` truncation in `epoch_idx` on 32-bit (MEDIUM; 32-bit)

**Status.** 🔴 **Unfixed.** `chain.rs` L376 still uses `as usize`.

**Specs.** `EpochIdx.lean`: `h_diff_fits : current_epoch − epoch ≤ Usize.max`.

**Rust.** `chain.rs` L376: `(self.current_epoch - epoch) as usize` truncates ≥ 2³².

**Consequence.** Wrong epoch's key returned silently.

**Fix.** `usize::try_from(..).map_err(..)`.

---

## D4. `SortedSet::push` comment contradicts replacement semantics (MEDIUM; spec)

**Status.** 🔴 **Unfixed.** Comment at `polynomial.rs` L898–900 still incorrect.

**Specs.** `AddChunk.lean` postcondition `IsSortedPushResult`. `Pt/Eq.lean`: equality on `x` only.

**Rust.** `polynomial.rs` L898–900 comment says "discard new points." Actual `sorted-vec 0.8.6`
`SortedSet::push` replaces (last-write-wins).

**Consequence.** Attacker's point overwrites honest point. Enables D19.

**Fix.** Correct comment; consider `find_or_insert`. **Related:** sub-finding of D19.


---

## D5. `PolyEncoder` index truncation `u32→u16` (MEDIUM; blob)

**Status.** 🔴 **Unfixed.** `polynomial.rs` L735 still uses `as u16`.

**Specs.** `NextChunk.lean`: `h_idx_fits : self.idx ≤ U16.max`. `FromPb.lean` accepts any `u32`.

**Rust.** `polynomial.rs` L735: `self.chunk_at(self.idx as u16)` wraps after 65535.

**Consequence.** Emitted `chunk.index` wraps to 0. Makes D19 poisoning permanent.

**Fix.** Store `idx: u16`, or reject `pb.idx > 65535` in `from_pb`.

---

## D6. `decode_chunk` cursor advanced on error paths (LOW; spec)

**Status.** 🟢 **No fix needed.** Latent spec observation; no behavioural impact.

**Specs.** `DecodeChunk.lean`: postcondition proves only `at ≤ *future(at)` on error.

**Rust.** `serialize.rs`: cursor advanced before bounds check. No exploit (`deserialize`
discards cursor on error).

**Consequence.** No behavioural impact.

---

## D7. `decode_varint` contract inconsistency (LOW; spec)

**Status.** 🟢 **No fix needed.** Latent; all callers validate the value.

**Specs.** `DecodeVarint.lean`: erased `assume!(val <= u16::MAX)`.

**Consequence.** Latent only. All callers check the value.

---

## D8. `usize` overflow in `trim_size` on 32-bit (LOW; config, 32-bit)

**Status.** 🔴 **Unfixed.** Subsumed by D28 — will be closed when D28 is fixed.

**Specs.** `TrimSize.lean`: `h_ooo : max_ooo_keys < 390451572`.

**Rust.** `chain.rs` L86: `max_ooo * 11` overflows on 32-bit.

**Consequence.** `trim_size` wraps small → GC too aggressive → keys lost.

**Fix.** Subsumed by D28.

---

## D9. Design observation (INFO — no defect)

**Status.** ⚪ **N/A** — audit note, not a defect.

`key(at)` advances `ctr` to `at` when `at > ctr`. High-water-mark counter by design.

---

## D10. Claimed history bound is false (MEDIUM; spec — LOW runtime)

**Status.** 🔴 **Unfixed.** The `requires`/`assume!` annotations still assert the false bound.

**Specs.** `Add.lean` assumes only `len + 36 ≤ Usize.max` — cannot adopt the stronger claim.

**Rust.** `chain.rs` L138, L174, L281–282: `requires`/`assume!` assert `data.len() ≤
KEY_SIZE * trim_size()`. False: at boundary `at = ctr + max_ooo`, `max_ooo − 1` keys
accumulate before `gc`. Defaults: claimed 2201; true **4199**.

**Reproduced.** [`key_history_bound_counterexample.py`](./key_history_bound_counterexample.py).

**Fix.** Correct bounds; call `gc` inside loop; align `gc`/`get` boundary.

---

## D11. `RoundRobinEncoder::chunk_at` panics on empty (LOW)

**Status.** 🔴 **Unfixed.** Test-only; low priority.

**Specs.** `ChunkAt.lean`: `h_nonempty`. Only reachable in `#[cfg(test)]`.

---

## D12. `compare` / `inz` constant-time (INFO — no defect found)

**Status.** ⚪ **N/A** — audit note, no defect found.

**Specs.** `Compare.lean`, `Inz.lean`: proved. `libcrux-ml-kem 0.0.7` FO path audited:

---

## D13. `PolyEncoder::from_pb` no point-count validation (MEDIUM; blob)

**Status.** 🔴 **Unfixed.** `polynomial.rs` L573–603 still checks only `pts.len() % 2 == 0`.

**Specs.** `PointAt.lean`, `ChunkAt.lean`, `NextChunk.lean` all require
`h_admissible : ∀ j < 16, len ∈ {0, 1, 3, 5, 30, 34, 36}`. `FromPb.lean` has no such
hypothesis — proves `Ok` for any 16 even-length slots.

**Rust.** `polynomial.rs` L573–603: `from_pb` checks only `pts.len() % 2 == 0`. The admissible
fact reaches `point_at` solely via an erased `assume!` (L646–654).

**Consequence.** Debug: **panic** on `from_complete_points`'s `debug_assert!(false, "missing
precomputed poly of size {}")`. Release: fallback Lagrange emits wrong chunks silently.

**Reproduced.** `encoder_from_pb_inadmissible_len` in
[`polynomial_from_pb_counterexample.rs.txt`](./polynomial_from_pb_counterexample.rs.txt).

**Fix.** Reject slots with `pts.len()/2 ∉ {0,1,3,5,30,34,36}` in `from_pb`.

---

## D14. `PolyDecoder::from_pb` no point-set size bound (LOW–MEDIUM; blob)

**Status.** 🔴 **Unfixed.** `from_pb` accepts any point-set size.

**Specs.** `Poly/LagrangeInterpolate.lean` etc. stated for arbitrary `pts.length`, but Rust
carries erased `#[hax_lib::requires(pts.len() <= MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1)]`.
`PolyDecoder/FromPb.lean` proves `Ok` with no bound.

**Rust.** `polynomial.rs`: `from_pb` accepts any point-set size.

**Consequence.** Blob with `pts_needed = 1600`, 100 points/slot → `decoded_message()` returns
3200 bytes (3× max), O(N²) interpolation.

**Reproduced.** [`decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt).

**Fix.** Reject `pts[i].len()/2 > MAX_INTERMEDIATE_POLYNOMIAL_DEGREE_V1` in `from_pb`.

---

## D15. Remaining `sorry`s and axioms (INFO)

**Status.** ⚪ **N/A** — known proof gaps, documented and expected.

- `Spqr/Specs/Lib/DecodeState.lean:54` — prost `Message` impl replaced by `sorry` in
  translation (issue #102). Nothing about which blobs `decode_state` accepts is established.
- `Spqr/Specs/Aeneas/MapCollectBridge.lean` — assumed bridge for `.map().collect()`.
- `SrcTranslated/Funs.lean` — four `sorry`-using declarations in generated protobuf code.
- SIMD GF(2¹⁶) multiplication (`PCLMULQDQ`/`PMULL` path) excluded from translation — unverified.
- Rust marked `#[hax_lib::opaque]` or `verification_status(lax)` has no theorem.

---

## D16. `Poly::serialize`/`deserialize` not inverses on zero polynomial (MEDIUM; API)

**Status.** 🔴 **Unfixed.** Zero polynomial still serialises to `[]`.

**Specs.** Serialise and deserialise specs have no shared round-trip theorem.

**Rust.** Zero polynomial serialises to `[]`; `deserialize` requires non-empty input.
`from_pb(into_pb(encoder))` = `Err(SerializationInvalid)` when any stored poly is zero.

**Consequence.** V1 protocol never hits this (message sizes always large enough). The encoder
is a public generic component — other callers can hit it.

**Reproduced.** `encoder_polys_roundtrip_with_empty_poly` in
[`poly_roundtrip_counterexample.rs.txt`](./poly_roundtrip_counterexample.rs.txt).

**Fix.** Serialise zero polynomial as `[0, 0]` (one zero coefficient).

---

## D17. `PolyDecoder::is_complete` is write-never — dead field (LOW; blob)

**Status.** 🔴 **Unfixed.** Field still never set to `true` by any code path.

**Specs.** `PolyDecoder/FromPb.lean` copies `is_complete` verbatim. `DecodedMessage.lean`
branches on it.

**Rust.** `polynomial.rs` L789, L912: `is_complete` initialised to `false`, never set `true`.

**Consequence.** Blob with `is_complete = true` → `decoded_message()` returns `None` forever
(permanent silent stall). Also: completed decoder re-runs O(N²) interpolation on every late
chunk.

**Reproduced.** `decoder_is_complete_never_set` in
[`decoder_logic_probe.rs.txt`](./decoder_logic_probe.rs.txt).

**Fix.** Set `self.is_complete = true` after successful decode, or delete the field.


---

## D18. `add_chunk` guard always true for low-index chunks (MEDIUM; message)

**Status.** 🔴 **Unfixed.** Guard logic unchanged. Subsumed by D19 fix.

**Specs.** `AddChunk.lean`: guard `poly_idx < necessary_points(i)` modelled; the spec's
`guard_true` lemma shows it holds for all `pts_needed ≥ 16`.

**Rust.** `polynomial.rs` L886: first disjunct of the guard is unconditionally true for any
chunk with `index < pts_needed / 16`.

**Consequence.** Low-index chunks always accepted regardless of duplicates. Enables D19.

**Related.** Sub-finding of D19.

---

## D19. Chunk poisoning persistent → permanent epoch stall (MEDIUM; message)

**Status.** 🔴 **Unfixed.** `SortedSet::push` still replaces; no reset on MAC failure. libsignal's clone-then-commit-after-MAC externally prevents persistence for network-only attackers, but the SPQR code is unchanged and an authenticated peer can still trigger it.

**Specs.** `ProtocolDoS.lean`:
- `add_chunk_index_zero_pushes` (L58) — attacker's values enter decoder
- `sorted_push_replaces_singleton` (L85) — honest point replaced
- `poison_survives_persistence` (L119) — survives `into_pb`/`from_pb`
- `recv_hdr_chunk_persists_unauthenticated_state` (L156) — no MAC on this path

**Rust.** `polynomial.rs` L879–904 (`add_chunk`): `SortedSet::push` replaces on `.eq`.
`send_ct.rs` L82–107, `send_ek.rs` L194–222: state persisted on `Ok(StillReceiving)`.

**Mechanism.** Attacker sends chunk with index 0 and garbage data. Guard passes (D18). Push
replaces honest point (D4). `decoded_message() = None` → `recv` returns `Ok` → poisoned
decoder saved. Full message assembly later fails MAC → `Err` → caller keeps pre-call
(poisoned) state. Permanent: index 0 re-emitted only after 65536 wraps (D5).

**Reproduced.** `poisoned_low_index_point_persists_and_wins` in
[`decoder_poison_persistence_counterexample.rs.txt`](./decoder_poison_persistence_counterexample.rs.txt).

**Fix.** (a) First-write-wins: `find_or_insert`. (b) Reset decoder on MAC failure.
(c) Keep both candidate `y` values.

---

## D20. `VecDeque::into_iter` model wrong when `head ≠ 0` (HIGH; spec)

**Status.** ✅ **Fixed.** Lean model at `FunsExternal.lean` L3733–3759 corrected: uses linear `head + 1`, decrements `length`, and the `@[step]` theorem (`next_spec`) proves both the empty and non-empty cases. Counterexample now produces `[some 20, some 30, none, none]` with final length `0`, matching Rust semantics.

**Location.** `SrcTranslated/FunsExternal.lean` L3733–3759.

**Defect (original).** The model used ring-buffer `wrapping_add` modulo `length` (inconsistent with the
project's growing-list model for `pop_front`/`push_back`/`index`) and never decremented
`length` (never terminated).

**Consequence (original).** After one `pop_front` on `[10,20,30]`, four `next` calls yielded
`[some 20, some 10, some 20, some 10]` with `length` still 2 (Rust yields `20, 30, None`).

**Reproduced.** [`vecdeque_into_iter_model_counterexample.lean.txt`](./vecdeque_into_iter_model_counterexample.lean.txt) — now outputs correct `ok ([some 20, some 30, none, none], 0)`.

**Fix applied.** `head' ← head + 1; length' ← length − 1` (mirrors `pop_front_spec_nonempty`).

---

## D21. `Chain::from_pb` — no `next_root`/`links`/epoch validation (MEDIUM; blob)

**Status.** 🔴 **Unfixed.** `Chain::from_pb` still copies all fields without validation.

**Specs.** All `FromPb.lean` theorems for unchunked states prove `Ok` with `epoch := pb.epoch`
for any `u64`. `RecvKey.lean` uses `next_root` as HKDF salt.

**Rust.** `chain.rs`: `Chain::from_pb` copies `next_root`, `links`, `send_epoch`,
`current_epoch` without validation.

**Consequence.**

| Invariant | Failure mode |
|---|---|
| `next_root.len() ≠ 32` | Silent key divergence (HKDF accepts any salt) |
| `links.len() = 0` | Underflow/OOB panic |
| `send_epoch > current_epoch` | Every `send_key` fails → chain stuck |

**Reproduced.** [`corrupted_blob_counterexample.rs.txt`](./corrupted_blob_counterexample.rs.txt).

**Fix.** Validate all three invariants in `Chain::from_pb`.


---

## D22. `Authenticator::from_pb` no key-length validation (LOW; blob)

**Status.** 🔴 **Unfixed.** `authenticator/serialize.rs` L16–21 still clones any length.

**Specs.** `authenticator.serialize.Authenticator.from_pb_spec`: pure field copy, no hypotheses.

**Rust.** `authenticator/serialize.rs` L16–21: clones any bytes for `root_key`/`mac_key`.

**Consequence.** `mac_key: []` → all HMAC tags identical → MACs forgeable on corrupted blob.

**Fix.** `if pb.mac_key.len() != 32 || pb.root_key.len() != 32 { return Err(StateDecode); }`.

**Related.** Parent of D31, D35, D36.

---

## D23. Test-only code outside protocol path (LOW)

**Status.** ✅ **Fixed (Lean audit comments added).** Test code; no production impact.

Test utilities under `#[cfg(test)]` that do not participate in the production protocol.
No security impact. No Lean spec files existed for the test-only `RoundRobinEncoder`/
`RoundRobinDecoder` (`src/encoding/round_robin.rs`) since hax correctly excludes `#[cfg(test)]`
modules.

**Lean.** D23 audit comments added to all five `Encoding/Encoder/` and `Encoding/Decoder/` spec
files (`EncodeBytes.lean`, `NextChunk.lean`, `New.lean`, `AddChunk.lean`, `DecodedMessage.lean`)
documenting that only `PolyEncoder`/`PolyDecoder` are instantiated and that the test-only
round-robin implementations are intentionally excluded from verification.

---

## D24. Unauthenticated epoch advance deadlocks PQ ratchet (HIGH; message)

**Status.** 🟡 **Unfixed in SPQR; mitigated by libsignal.** The transition at `states.rs` L513–526 is still unauthenticated. libsignal's clone-then-commit-after-MAC prevents persistence for network-only attackers. An authenticated peer is not mitigated.

**Specs.** `ProtocolDoS.lean` L156: `recv_hdr_chunk_persists_unauthenticated_state`.

**Rust.** `states.rs` L513–526 → `send_ct.rs` L295 `recv_next_epoch`: transition from
`Ct2Sampled` to `KeysUnsampled(epoch+1)` with no `Authenticator` consultation.

**Mechanism.** 4-byte message `[1, 2, 1, 0]` with `epoch == self.epoch + 1`. Bob advances
to `KeysUnsampled(epoch 2)`, consumes `recv_key(1, 1)`. Alice stays in epoch 1. **Permanent
bidirectional deadlock.** `recv` also returns unauthenticated DR chain key.

**Reproduced.** `d24_unauthenticated_epoch_advance_deadlocks_ratchet` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix.** Gate on authenticated evidence; honour `epoch+1` only after header MAC verifies.

---

## D25. Empty message finalises V0 downgrade (MEDIUM; message)

**Status.** 🟡 **Unfixed in SPQR; mitigated by libsignal.** Version negotiation logic unchanged. libsignal's MAC check prevents persistence for network-only attackers. The window remains open while `min_version = V0` (current production default).

**Specs.** `Message/Deserialize.lean` proves `0 < msg.epoch` on wire — protocol needs
`epoch ≥ 1`. Version negotiation logic has no authentication gate.

**Rust.** `lib.rs`: `msg_version(msg) = V0 < state_version = V1` and `min_version ≤ V0` →
`init_inner(V0) = None`, `version_negotiation: None`. Empty byte string (0 bytes) is valid.

**Consequence.** PQ ratchet permanently disabled (`NegotiationComplete(V0)`). Every subsequent
V1 message returns `Ok` with `state: vec![]`.

**Reproduced.** `d25_unauthenticated_v0_downgrade_with_empty_message` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix.** Reject version downgrades, or require MAC over version negotiation.

---

## D26. `epoch == 0` blob → underflow in `lib::send` (LOW; blob)

**Status.** 🔴 **Unfixed.** All 11 unchunked `from_pb` functions still accept `epoch = 0`.

**Specs.** All 11 unchunked `FromPb.lean` prove `Ok` with `epoch := pb.epoch` for any `u64`.

**Rust.** `lib.rs` L300: `msg.epoch − 1`. With `epoch = 0`: debug panics; release wraps to
`u64::MAX` → `Err(EpochOutOfRange)` on every `send`.

**Reproduced.** `d26_epoch_zero_state_underflows_in_send` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix.** Reject `pb.epoch == 0` in unchunked `from_pb`s; `checked_sub` in `lib.rs`.

---

## D27. `lib::send` panics on `assert!(key.is_none())` (LOW–MEDIUM; blob)

**Status.** 🔴 **Unfixed.** `lib.rs` L293 `assert!` still present.

**Specs.** `send` is `verification_status(lax)`. `assume!(key.is_none())` at L292 unverified.

**Rust.** `lib.rs` L293: `assert!(key.is_none())` remains in release. A blob producing
`EpochSecret` when none expected triggers this.

**Consequence.** **Panic** in both debug and release.

**Fix.** Return `Err` instead of `assert!`.


---

## D28. `ChainParams` never range-checked — `InvalidParams` dead code (MEDIUM; config)

**Status.** 🔴 **Unfixed.** `Error::InvalidParams` still never constructed.

**Specs.** `TrimSize.lean`: `max_ooo_keys < 390451572`. `Key.lean`: `h_ctr_bound`.

**Rust.** `Error::InvalidParams(&'static str)` exists but **never constructed**. Any values
accepted.

**Consequence.** `max_ooo_keys = u32::MAX` → `at + max_ooo` wraps; D2 reachable.

**Reproduced.** `d28_unvalidated_chain_params_overflow_in_key` in
[`protocol_driver_counterexamples.rs.txt`](./protocol_driver_counterexamples.rs.txt).

**Fix.** Validate in `initial_state` and `Chain::from_pb`.

---

## D29. No `Zeroize` on heap key-holding types (LOW; local memory)

**Status.** 🔴 **Unfixed.** `zeroize` crate not in `Cargo.toml`.

**Rust.** No `Zeroize`/`ZeroizeOnDrop`. Heap secrets: chain seeds, auth keys, ML-KEM `ss`,
DK 2400 B, ES 2080 B. `clear_next()` = `Vec::clear()` (no overwrite).

**Consequence.** Secrets persist until realloc. Needs local access.

**Fix.** Add `zeroize` crate; derive `ZeroizeOnDrop`. **Related.** D33.

---

## D30. `trim_size` overflow disables GC (LOW; blob)

**Status.** 🔴 **Unfixed.** Subsumed by D28 — will be closed when D28 is fixed.

**Rust.** Large `max_ooo_keys` → `trim_size()` overflows → GC disabled → old keys retained.

**Consequence.** Forward secrecy degrades.

**Fix.** Subsumed by D28.

---

## D31. `Authenticator` IKM collision (LOW; blob)

**Status.** 🔴 **Unfixed.** Subsumed by D22.

**Rust.** HKDF `expand(root_key || mac_key)` — without length validation, different-length
combinations can collide.

**Consequence.** Latent. **Fix.** Subsumed by D22. **Related.** Sub-finding of D22.

---

## D32. Self-session `max_jump = u32::MAX` triggers D2/D28 (MEDIUM; message + config)

**Status.** 🔴 **Unfixed.** libsignal `ratchet.rs` still sets `max_jump = u32::MAX` for self-sessions.

**Rust.** libsignal `ratchet.rs` L41–52: `max_jump = u32::MAX` for Note-to-Self. D2 overflow
reachable in production.

**Fix.** Cap at `u32::MAX.saturating_sub(MAX_MESSAGE_KEYS + 1)`.

---

## D33. No `Zeroize` on stack secrets (LOW; local memory)

**Status.** 🔴 **Unfixed.** Stack secrets still uncleared.

**Rust.** 64-byte keygen seed, 32-byte encaps entropy in `incremental_mlkem768.rs` uncleared.

**Fix.** `randomness.zeroize()` after use. **Related.** D29.

---

## D34. No `epoch < u64::MAX` guard in chunked recv (LOW–MEDIUM; blob)

**Status.** 🔴 **Unfixed.** No guard at `states.rs` L515.

**Rust.** `states.rs` L515: `epoch + 1` wraps when `epoch == u64::MAX`. `assert_eq!` panics.

**Fix.** Validate `epoch < u64::MAX` in `Ct2Sent::from_pb`.


---

## D35. `authenticator::Error` variants never constructed (LOW)

**Status.** ✅ **Fixed (Lean gap-documenting theorems added).** Dead code; evidence of planned but unimplemented validation.

**Rust.** `Error::InvalidKeyLength`, `Error::InvalidRootKeyLength` exist but never returned.

**Consequence.** Validation was planned, never implemented. **Related.** D22.

**Lean.** Two gap-documenting theorems added to `Spqr/Specs/Authenticator/Serialize/Authenticator/FromPb.lean`:
- `from_pb_no_key_length_check` — proves `from_pb` succeeds even with `root_key.length ≠ 32`,
  documenting the missing validation.
- `from_pb_missing_validation` — proves key lengths are copied verbatim
  (`result.root_key.length = 32 ↔ pb.root_key.length = 32`), documenting that a corrected
  `from_pb` should *reject* when the condition is false.

D35 audit comments also added to `FunctionalModels.lean`.

---

## D36. `From<authenticator::Error>` maps to wrong error class (LOW)

**Status.** ✅ **Fixed (Lean wrong-mapping theorems added).** Wrong error mapping; no runtime impact until D22 is fixed.

**Rust.** `impl From<authenticator::Error> for Error` maps all variants to `MacVerifyFailed`.

**Consequence.** Deserialisation failures reported as MAC failures. **Related.** D22.

**Lean.** D36 audit note and three theorems added to `Spqr/Specs/Lib/Error/From.lean`:
- `from_maps_all_to_mac_verify_failed` — proves the blanket mapping: all variants produce
  `MacVerifyFailed` and never `StateDecode`, making the wrong classification explicit.
- `from_wrong_mapping_for_key_errors` — enumerates each key-validation variant
  (`AuthenticatorRootKeyPresent/Missing`, `AuthenticatorMacKeyPresent/Missing`) and proves
  each maps to `MacVerifyFailed` when it should map to `StateDecode`.
- Docstring includes the expected Rust fix (variant-discriminated `match`).

---

## D37. `PolyDecoder::into_pb` truncates `pts_needed: usize` to `u32` (LOW)

**Status.** ✅ **Fixed (Lean truncation-bound theorem added).** Latent; unrealistic precondition (`pts_needed > u32::MAX`).

**Rust.** `pts_needed` is `usize` internally, `u32` in protobuf. On 64-bit with
`pts_needed > u32::MAX` (unrealistic), round-trip loses high bits.

**Fix.** Store `pts_needed: u32` internally. **Related.** D14.

**Lean.** D37 audit notes and theorem added:
- `into_pb_requires_u32_bound` in `Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean` —
  documents that `into_pb_spec`'s `pts_needed` fidelity postcondition depends on
  `h_cast : self.pts_needed.val ≤ U32.max`; without it, the `from_pb ∘ into_pb` round-trip
  loses high bits.
- D37 audit comment added to `FromPb.lean` module docstring noting that `from_pb` widens
  losslessly but `into_pb` truncates.

---

## D38. Unauthenticated `Ct1Ack` stalls epoch (MEDIUM; message)

**Status.** 🟡 **Unfixed in SPQR; mitigated by libsignal.** Ack processing still unauthenticated. libsignal's clone-then-commit-after-MAC prevents persistence for network-only attackers.

**Rust.** `states.rs` L463–477 → `send_ct.rs` L232–240: `Ct1Ack` transitions Bob from
`Ct1Sampled` to `Ct2Sampled` without authentication.

**Mechanism.** 5-byte forgery `[1, 1, 0xE8, 0x07, 4]`. Bob switches to Ct2-only; Alice in
HeaderSent (expects Ct1). 200 round-trips never leave epoch 1.

**Reproduced.** `d38_forged_ct1ack_stalls_epoch` in
[`forged_control_message_counterexamples.rs.txt`](./forged_control_message_counterexamples.rs.txt).

**Fix.** Authenticate acks — honour `Ct1Ack` only after MAC-verified evidence.

---

## D39. Unauthenticated `EkCt1Ack` stalls + poisons `ek` decoder (MEDIUM; message)

**Status.** 🟡 **Unfixed in SPQR; mitigated by libsignal.** Same mitigation as D38.

**Rust.** `states.rs` L419–420: `ack = true` processed before auth. Garbage chunk data
enters `ek` decoder. Combines D38 (stall) + D19 (poisoning).

**Reproduced.** [`forged_control_message_counterexamples.rs.txt`](./forged_control_message_counterexamples.rs.txt).

**Fix.** Gate `ack` flag on authenticated evidence.

---

## D40. Self-session removes HKDF-walk bound — pre-MAC CPU DoS (LOW–MEDIUM; msg + config)

**Status.** 🔴 **Unfixed.** libsignal still sets `max_jump = u32::MAX` for self-sessions.

**Specs.** `key_spec_greater_jump`: `h_at_le : at − ctr ≤ max_jump` bounds HKDF iterations.

**Rust.** libsignal `max_jump = u32::MAX` for self-sessions makes the check vacuous.
`index = 1_000_000` → HKDF walks 1M iterations (~seconds) **before** MAC check.

**Consequence.** Pre-MAC CPU denial of service.

**Fix.** Cap self-session `max_jump`; or move `max_jump` check before HKDF walk.

---

# New Defects Discovered via Alternative Analysis Methods (D41–D52, 11 new)

> **Added:** 2026-10-04
>
> Discovered by applying methods M1–M12 to the SPQR codebase.

---

## D41. `decode_varint` shift overflow produces silent truncation (MEDIUM; message)

**Status.** 🔴 **Unfixed.**

**Detection method.** M8 (panic-path audit) + manual code review.

**Rust.** `states/serialize.rs` L170: `out |= ((byte as u64) & 0x7f) << (7 * i as i32)`.
When `i = 9` (loop bound `max_i = 10`), shift = 63 discards 6 of 7 bits. A crafted
10-byte varint encodes values that lose bits silently.

**Consequence.** Malicious varint in message decodes to wrong epoch/index, potentially
bypassing epoch checks.

**Fix.** Reject varints with `i == 9` where `byte > 1`.

---

## D42. `Authenticator::update` IKM includes `root_key` of unchecked length (LOW; crypto)

**Status.** ✅ **Fixed (Lean divergence theorem added).** Extension of D22/D31.

**Detection method.** M7 (crypto protocol analysis).

**Rust.** `authenticator.rs` L45: `let ikm = [self.root_key.as_slice(), k].concat()`.
D22 identifies that `from_pb` accepts arbitrary key lengths. D31 notes the IKM collision
risk. This defect identifies a specific new consequence: when `root_key` has wrong length
via D22, the `update` function's concatenation `root_key || k` produces a different HKDF
input than the peer. After `update`, the two parties compute different `mac_key` values,
so all subsequent MACs diverge — the session becomes permanently broken (not just on
the current message, but on all future messages in the epoch). D22/D31 describe the
validation gap and abstract collision risk; this documents the concrete session-breaking
consequence chain: D22 → D42 → permanent MAC divergence.

**Consequence.** Permanent session break after blob corruption, not recoverable without
re-initialisation. **Related.** D22, D31.

**Lean.** D42 audit note and theorem added to `Spqr/Specs/Authenticator/Authenticator/Update.lean`:
- `update_diverges_on_bad_root_key` — proves that if two authenticators have different
  `root_key` values (e.g. one from `new` with len=32, one from a corrupted `from_pb`), then
  their HKDF IKM (`root_key ++ k`) differs, formalising the D22 → D42 → permanent MAC
  divergence consequence chain.

---

## D44. `compare` panics on mismatched lengths (MEDIUM; blob)

**Status.** 🔴 **Unfixed.**

**Detection method.** M8 (panic-path audit) + M1 (model checking).

**Rust.** `util.rs` L28: loop indexes `rhs[i]` using `lhs.len()`. If `rhs.len() <
lhs.len()`, panics. The `requires(lhs.len() == rhs.len())` is erased in non-hax builds.

Via D42 (wrong key length) or D14 (arbitrary decoder output length), `expected_mac`
could have `len != 32`, reaching `compare` with mismatched lengths.

**Consequence.** Panic (crash) in MAC-verification hot path → DoS.

**Fix.** Add `if lhs.len() != rhs.len() { return 1; }` in `compare`.

---

## D45. `PolyEncoder::from_pb` accepts arbitrary `idx` (LOW–MEDIUM; blob)

**Status.** 🔴 **Unfixed.**

**Detection method.** M4 (property testing candidate).

**Rust.** `polynomial.rs` L573–619: `from_pb` stores `pb.idx` (u32) directly without
validating consistency with point counts. High `idx` with inadmissible point counts
triggers `debug_assert!(false)` at L310 via `point_at`→`from_complete_points`.

**Consequence.** Debug: panic. Release: wrong polynomial data. Extends D5 + D13.

**Fix.** Validate `pb.idx` against point counts. **Related.** D5, D13.

---

## D46. `ChainEpochDirection::from_pb` — `next.len() != 32` crash in `copy_from_slice` (HIGH; blob)

**Status.** 🔴 **Unfixed.**

**Detection method.** M3 (fuzz surface) + M8 (panic-path audit).

**Rust.** `chain.rs` L306–312: `from_pb` accepts any `next` length. L243:
`next.copy_from_slice(&genr8r[..32])` panics if `next.len() != 32`. D1 lists the
`next.len() ≠ 32` crash at L241 (`copy_from_slice`), but the L243 path is a distinct
crash in `next_key_internal` — the assert at L229 catches empty `next`, but non-empty
`next` with `len ∈ {1..31, 33..}` bypasses the assert and crashes at L243.

**Consequence.** Panic → crash loop on corrupted blob. Distinct crash path from D1.

**Fix.** Validate `pb.next.len() == 32` in `from_pb`. **Related.** D1.

---

## D47. `epoch == 0` in chunked `from_pb` also unvalidated (LOW–MEDIUM; blob)

**Status.** 🔴 **Unfixed.** Extension of D26.

**Detection method.** M1 (model checking) + manual review.

**Rust.** D26 identifies the `epoch == 0` underflow in `lib.rs` L300 for the 11 unchunked
`from_pb` paths. However, the chunked `from_pb` paths also propagate epochs from the
unchunked inner state without additional validation. For example,
`chunked/send_ek/serialize.rs` L16–20 delegates to `unchunked::send_ek::KeysUnsampled::from_pb`
which accepts `epoch = 0`. Thus the same vulnerability exists for all 11 chunked state
variants that wrap unchunked states. Additionally, `lib.rs` L427:
`let msg_key_epoch = scka_msg.epoch - 1` in the `recv` path is protected by `deserialize`
rejecting `epoch == 0`, but the `send` path (L300) is not. The fix for D26 (reject
`epoch == 0` in unchunked `from_pb`) would also fix this.

**Consequence.** Same as D26. **Related.** D26.

---

## D48. `KeyHistory::gc` panics when `ctr < max_ooo_keys` after blob restore (MEDIUM; blob)

**Status.** 🔴 **Unfixed.**

**Detection method.** M1 (model checking) + manual review.

**Rust.** `chain.rs` L149: `assert!(current_key >= params.max_ooo_keys_or_default())`.
Via D1 corrupted blob: `from_pb` loads `ctr = 0` with non-empty `prev.data` of size
≥ `trim_size * KEY_SIZE`. First `recv_key` with small `at` (e.g., `at = 1`) calls
`gc(1, params)` → assert `1 >= 2000` fails → panic.

**Consequence.** Panic on first `recv_key` after restoring corrupted blob.

**Fix.** Guard `gc` with `if current_key >= params.max_ooo_keys_or_default()`.
**Related.** D1.

---

## D49. `PolyDecoder::from_pb` accepts `pts_needed == 0` — division by zero in `necessary_points` (LOW; blob)

**Status.** 🔴 **Unfixed.**

**Detection method.** M3 (fuzz surface).

**Rust.** `polynomial.rs` L850: `pts_needed: pb.pts_needed as usize`. If `pb.pts_needed == 0`,
then `necessary_points` at L772 returns `0 / 16 = 0` for all polys. `decoded_message` at
L919 checks `pts.len() < self.necessary_points(i)` — with 0 necessary, any points suffice.
An empty decoder with `pts_needed == 0` returns `Some(vec![])` from `decoded_message`.

**Consequence.** Produces an empty decoded message, which downstream callers `split_off`
on (e.g., `send_ek.rs` L206: `ct2.split_off(CIPHERTEXT2_SIZE)` where `CIPHERTEXT2_SIZE = 128`).
`split_off` on an empty Vec panics.

**Fix.** Validate `pb.pts_needed > 0` and matches expected sizes. **Related.** D14.

---

## D50. `flip_endianness_of_encapsulation_state` leaks secret copy (LOW; local memory)

**Status.** 🔴 **Unfixed.**

**Detection method.** M2 (Miri candidate).

**Rust.** `incremental_mlkem768.rs` L146: `let mut fixed_es = es.clone()` — clones 2080
bytes of secret encapsulation state. The returned clone is used but the original `es`
reference remains. The `clone()` creates a second copy of secret material in memory.

**Consequence.** Doubled secret memory footprint; no zeroization. **Related.** D29, D33.

**Fix.** Use in-place byte swapping instead of clone.

---

## D51. `kdf::hkdf_to_slice` panics on `okm` length > 255 * hash_len (LOW; config)

**Status.** ✅ **Fixed (Lean audit comments added).**

**Detection method.** M12 (differential testing candidate).

**Rust.** `kdf.rs` L15–17: `hkdf.expand(info, okm).expect("all lengths should work")`.
HKDF-SHA256 `expand` fails when `okm.len() > 255 * 32 = 8160`. The `expect` panics.
Currently all callers use `okm_len ∈ {32, 64, 96}`, well within bounds. But the API
accepts arbitrary `okm_len` with no compile-time or runtime guard.

**Consequence.** Latent. A future caller requesting `okm_len > 8160` would panic.

**Fix.** Add `assert!(okm_len <= 8160)` or return `Result`.

**Lean.** D51 audit comments added to `Spqr/Specs/Kdf/HkdfToSlice.lean` and
`Spqr/Specs/Kdf/HkdfToVec.lean` documenting that the `h : okm.length ≤ 255 * 32`
precondition is erased in Rust (the `expect` panics if violated). The Lean trusted base
silently assumes the bound; if violated, the axiom's postcondition would be unsound.

---

## D52. `PolyDecoder::is_complete` flag not validated on `from_pb` (LOW; blob)

**Status.** ✅ **Fixed (Lean gap theorem added).**

**Detection method.** M4 (property testing).

**Rust.** `polynomial.rs` L851: `is_complete: pb.is_complete`. If a blob sets
`is_complete = true` with non-empty points, `decoded_message` at L912–913 returns
`None` forever — the decoder thinks it has already completed, and never returns data.

**Consequence.** The chunked protocol stalls: `decoded_message` always returns `None`,
so the state machine never transitions from "StillReceiving" to "Done". This is a
silent DoS via corrupted blob — no error is returned, the session just hangs.

**Fix.** Validate `is_complete` consistency with `pts` contents, or always reset to
`false` on `from_pb`.

**Lean.** D52 audit note and theorem added to
`Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean`:
- `from_pb_accepts_bad_is_complete` — proves that `from_pb` succeeds with
  `decoder.is_complete = true` when the blob has `pb.is_complete = true`, even though
  no honest code path sets this flag during deserialization, creating a silent permanent
  stall.

---

# Additional Defects Discovered via Online Specification Theorem Methods (D53–D66)

> **Added:** 2026-10-04
>
> Discovered by surveying online Lean/theorem-prover verification repositories for
> cryptographic protocol implementations (Aeneas-verified Rust projects, hax/F* crypto
> specs, PQXDH Lean formalisations, ProVerif Double Ratchet models) and applying their
> specification and invariant methods to detect additional SPQR defects.
>
> **Methods applied:**
>
> - **M13 (Refinement checking):** Pre/postcondition alignment; gap between erased
>   `hax_lib::requires` and runtime guards.
> - **M14 (Compositional invariant verification):** Each postcondition must establish
>   the precondition of every downstream caller.
> - **M15 (Termination / fuel analysis):** Loops and recursion lacking bounded fuel.
> - **M16 (Information-flow / secret hygiene):** Secret data through clone/copy/drop.
> - **M17 (Symbolic state-machine model checking):** Reachable transitions under
>   adversarial message sequences.
> - **M18 (Trusted-base / axiom soundness audit):** `hax_lib::assume!`, `opaque`,
>   Lean `axiom` statements.


---

## D53. `PolyEncoder::next_chunk` — `idx` wraps `u16` silently, producing duplicate chunk indices (MEDIUM; protocol)

**Status.** 🔴 **Unfixed.**

**Detection method.** M13 (refinement checking) — `wrapping_add` at `polynomial.rs` L736
has no corresponding Lean spec postcondition bounding `idx`.

**Rust.** `polynomial.rs` L736: `self.idx = self.idx.wrapping_add(1)`. After 65 536
calls, `idx` wraps to 0. Subsequent chunks carry the same `index` as earlier ones.
`PolyDecoder::add_chunk` de-duplicates on `x` — wrapped chunks silently discarded.

**Consequence.** After 65 536 chunks in a single encoder session, the encoder emits
chunks the decoder ignores. Silent stall in long-running epochs with retransmissions.

**Fix.** Return `Err` when `idx == u16::MAX`, or use `checked_add`.

---

## D54. `compare` constant-time comparison panics on mismatched lengths (MEDIUM; crypto)

**Status.** 🔴 **Unfixed.**

**Detection method.** M13 (refinement checking) — `util.rs` L28 iterates `0..lhs.len()`
indexing `rhs[i]`; the `requires(lhs.len() == rhs.len())` is erased at runtime.

**Rust.** `util.rs` L25–32: If `lhs.len() > rhs.len()`, panics. If `lhs.len() < rhs.len()`,
trailing `rhs` bytes unchecked — returns 0 (equal) even with extra non-zero bytes.
Corrupted blob producing non-32-byte MAC field reaches `compare` with mismatched lengths.

**Consequence.** Panic or false MAC acceptance (truncated MAC passes verification).

**Fix.** Runtime `assert_eq!(lhs.len(), rhs.len())` or return `1` on length mismatch.

---

## D55. `Authenticator::update` IKM concatenation lacks length prefix — domain separation failure (LOW; crypto)

**Status.** ✅ **Fixed (Lean IKM collision theorem added).** Extension of D31/D42.

**Detection method.** M14 (compositional invariant verification).

**Rust.** `authenticator.rs` L45: `[self.root_key.as_slice(), k].concat()` without
length prefix. Different `(root_key, k)` pairs can produce identical `ikm` when
`root_key || k` collides byte-for-byte. Requires D22 corruption.

**Consequence.** Latent. Two authenticator states produce identical MAC keys.
**Related.** D22, D31, D42.

**Fix.** Length-prefixed concatenation: `len(root_key) || root_key || k`.

**Lean.** D55 audit note and theorem added to
`Spqr/Specs/Authenticator/Authenticator/Update.lean`:
- `update_ikm_collision_exists` — constructs a concrete witness of two distinct
  `(root_key, k)` pairs (`[1,2],[3]` vs `[1],[2,3]`) whose plain concatenations
  are identical (`[1,2,3]`), proving the domain-separation failure.


---

## D56. `epoch_idx` — `as usize` truncation causes silent key mismatch on 32-bit (MEDIUM; 32-bit)

**Status.** ✅ **Fixed (Lean usize-bound theorem added).** Extension of D3.

**Detection method.** M13 (refinement checking) — Lean spec does not model `usize` width.

**Rust.** `chain.rs` L376: `(self.current_epoch - epoch) as usize`. On 32-bit, if
`current_epoch - epoch > u32::MAX`, cast truncates → wrong epoch's keys returned.

**Consequence.** Silent key divergence on 32-bit. **Related.** D3.

**Fix.** `usize::try_from(...).map_err(|_| Error::EpochOutOfRange(epoch))?`.

**Lean.** D56 audit note and theorem added to `Spqr/Specs/Chain/Chain/EpochIdx.lean`:
- `epoch_idx_needs_usize_bound` — proves that `epoch_idx_spec`'s index correctness
  postcondition holds jointly with `current_epoch - epoch ≤ Usize.max`, documenting
  that the `as usize` cast is lossless only when `h_diff_fits` holds. On 32-bit
  platforms this precondition is violated for large epoch differences.

---

## D57. `add_chunk` — `GF16::new(poly_idx as u16)` truncates x-coordinate for large chunk indices (LOW; protocol)

**Status.** 🔴 **Unfixed.**

**Detection method.** M15 (fuel analysis).

**Rust.** `polynomial.rs` L889: `GF16::new(poly_idx as u16)`. When `chunk.index > 4095`,
`as u16` truncation produces colliding x-coordinates. Decoder interpolation wrong.

**Consequence.** Silent wrong decoded data for large chunk indices. **Related.** D53.

**Fix.** Reject `chunk.index > 4095`.

---

## D58. `from_complete_points` fallback computes wrong polynomial in release (MEDIUM; blob)

**Status.** 🔴 **Unfixed.** Extension of D13.

**Detection method.** M18 (trusted-base audit).

**Rust.** `polynomial.rs` L310–327: Fallback constructs Lagrange interpolant of
`{(x_i, 1)}` not `{(x_i, y_i)}`. In release, silently emits all-one chunks.

**Consequence.** Silent data corruption in release. **Related.** D13.

**Fix.** Return `Err` instead of `debug_assert!(false)` + fallback.

---

## D59. `trim_size` — `max_ooo * 11` overflows `usize` with unvalidated params (LOW; config)

**Status.** 🔴 **Unfixed.** Subsumed by D28.

**Detection method.** M15 (fuel analysis).

**Rust.** `chain.rs` L87: `max_ooo * 11 / 10 + 1`. Erased `assume!`. With D28's
unvalidated `max_ooo = u32::MAX`, wraps → tiny trim_size → GC deletes all OOO keys.

**Consequence.** All delayed messages permanently dropped. **Related.** D28, D30.

**Fix.** Subsumed by D28.



---

## D60. `key` — `ctr + max_ooo` overflow bypasses KeyTrimmed check (MEDIUM; blob + config)

**Status.** 🔴 **Unfixed.** Extension of D2.

**Detection method.** M14 (compositional invariant verification).

**Rust.** `chain.rs` L265: `at > self.ctr + params.max_ooo_keys_or_default()`. When
`ctr` large (D1 blob) and default `max_ooo = 2000`, `ctr + 2000` wraps. Valid keys
rejected as trimmed, or trimmed keys accepted as valid.

**Consequence.** Key state inconsistency between parties. **Related.** D2, D28.

**Fix.** `self.ctr.checked_add(...)`, return `KeyTrimmed` on overflow.

---

## D61. `Option<T>::next_chunk` — `unwrap()` panics when `None` (LOW; spec)

**Status.** 🔵 **Unfixed (spec-only).**

**Detection method.** M18 (trusted-base audit) — `requires(self.is_some())` erased.

**Rust.** `encoding.rs` L64: `self.take().unwrap()`. All callers maintain `is_some()`.

**Consequence.** Latent. **Fix.** Return `Result` or newtype.

---

## D62. Eviction loop proof depends on unsound `VecDeque` Lean model (LOW; spec)

**Status.** 🔵 **Unfixed (spec-only).**

**Detection method.** M14 + M18.

**Rust.** `chain.rs` L391–394: Correct in Rust, but Lean proof relies on D20's unsound
`VecDeque` model.

**Consequence.** No runtime defect; Lean proof unsound. **Related.** D20.

**Fix.** Fix `VecDeque` model (D20).

---

## D63. `encaps1` — 32-byte KEM entropy not zeroized on stack (LOW; local memory)

**Status.** 🔴 **Unfixed.** Extension of D33.

**Detection method.** M16 (information-flow).

**Rust.** `incremental_mlkem768.rs` L52–53: `randomness` persists on stack.

**Consequence.** KEM entropy recoverable via memory dump. **Related.** D29, D33.

**Fix.** `randomness.zeroize()` after `encapsulate1`.

---

## D64. `decaps` — no ML-KEM algebraic validity on blob inputs (LOW; blob)

**Status.** 🔴 **Unfixed.**

**Detection method.** M13 (refinement checking).

**Rust.** `incremental_mlkem768.rs` L154: `requires` checks only byte lengths. FO
transform produces pseudorandom garbage for invalid inputs → silent PQ security loss.

**Consequence.** Silent loss of PQ security; DR classical fallback. **Related.** D1.

**Fix.** Flag epoch as PQ-degraded on unexpected decapsulation output.

---

## D65. `SortedSet::push` last-write-wins contradicts comment — point replacement (MEDIUM; message)

**Status.** 🔴 **Unfixed.** Extension of D19.

**Detection method.** M17 (symbolic state-machine model checking).

**Rust.** `polynomial.rs` L898–901: Comment says first-write-wins but implementation
does last-write-wins. Root cause of chunk poisoning (CorruptedBlobs.md §15.2).

**Consequence.** Authenticated peer replaces honest points → permanent stall. **Related.** D19.

**Fix.** First-write-wins: check `contains` before `insert`.

---

## D66. `decode_varint` — 10-byte varint desynchronises parse position (LOW; message)

**Status.** 🔴 **Unfixed.** Extension of D41.

**Detection method.** M13 (refinement checking) — round-trip `decode(encode(x)) = x`.

**Rust.** `states/serialize.rs` L170: For 10-byte varints, parser position wrong.
Subsequent fields parsed from wrong offset → epoch/index misinterpretation.

**Consequence.** Crafted varint causes wrong epoch transitions. **Related.** D41.

**Fix.** Reject varints with >9 continuation bytes; validate high-bit clear on last.


---

# Lean-Mode Fix Ordering

> Fixes for issues arising from the Lean specification / verification layer ("Lean Mode"),
> listed in the order they can be applied. Dependencies flow top-to-bottom: each fix either
> has no prerequisites or depends only on fixes listed above it.
>
> **Scope.** A defect is "Lean Mode" if it involves: an unsound or incomplete Lean model,
> a `sorry` / `axiom` / `sorryAx` gap, an erased `hax_lib::requires` / `assume!` that the
> Lean translation trusts but the Rust runtime does not enforce, a postcondition–precondition
> composition gap exposed by the `@[step]` proof chain, a spec-only dead-code or annotation
> inconsistency, or a Lean-trusted-base soundness issue.

## Phase 0 — Foundation: fix the trusted base (no prerequisites)

| Order | Defect | Fix | Rationale |
|---|---|---|---|
| **0-a** | **D20** ✅ | ~~Rewrite `VecDeque::into_iter` model in `FunsExternal.lean`: `head' ← head + 1; length' ← length − 1`.~~ **Done.** | Unblocks `Chain::into_pb` round-trip proofs; D62 can now be re-proved. |
| **0-b** | **D15** | Close `sorry`s in `SrcTranslated/Funs.lean`; prove `MapCollectBridge.lean`; resolve `DecodeState.lean:54`. | Removes proof gaps blocking `from_pb`/`into_pb` round-trips. |
| **0-c** | **D10** | Correct false `data.len() ≤ KEY_SIZE * trim_size()` bound in `Add.lean`/`Remove.lean` and `chain.rs` annotations. | Eliminates false axiom; needed before `key_spec` proofs. |


## Phase 1 — Spec-model alignment (depends on Phase 0)

| Order | Defect | Fix | Dependency |
|---|---|---|---|
| **1-a** | **D4** | Fix `AddChunk.lean` postcondition `IsSortedPushResult` to specify last-write-wins (or change Rust to first-write-wins). | Needed for D65. |
| **1-b** | **D65** | Add `add_chunk` postcondition specifying retained `y` on x-collision. | Depends on 1-a. |
| **1-c** | **D6** | Strengthen `DecodeChunk.lean`: on error, `at = *old(at)`. | Independent. |
| **1-d** | **D7** | Remove erased `assume!(val <= u16::MAX)` from `DecodeVarint.lean`; prove or check. | Independent. |

## Phase 2 — Erased-precondition enforcement (depends on Phase 0)

| Order | Defect | Fix | Dependency |
|---|---|---|---|
| **2-a** | **D61** | `encoding.rs`: replace `unwrap()` with `ok_or(...)` returning `Result`. | Independent. |
| **2-b** | **D51** ✅ | ~~`kdf.rs`: guard `okm.len() > 8160` before `expand`.~~ **Done.** Erased-bound audit comments added to `HkdfToSlice.lean` and `HkdfToVec.lean`. | Independent. |
| **2-c** | **D54/D44** | `util.rs`: return `1` on `lhs.len() != rhs.len()`. | Independent. |
| **2-d** | **D53** | `polynomial.rs`: `checked_add(1)` for encoder `idx`. Update `NextChunk.lean`. | Independent. |
| **2-e** | **D58** | `polynomial.rs`: return `Err` instead of `debug_assert!(false)` + fallback. | Independent. |

## Phase 3 — Compositional invariant gaps (depends on Phases 0–2)

| Order | Defect | Fix | Dependency |
|---|---|---|---|
| **3-a** | **D60** | `chain.rs` L265: `checked_add`, return `KeyTrimmed` on overflow. | Needs 0-c. |
| **3-b** | **D56** ✅ | ~~`chain.rs` L376: `usize::try_from(...)` instead of `as usize`.~~ **Done.** Usize-bound theorem (`epoch_idx_needs_usize_bound`) added to `EpochIdx.lean`. | Needs 0-a. |
| **3-c** | **D62** | Re-prove eviction loop against corrected `VecDeque` model. | Needs 0-a. |
| **3-d** | **D55** ✅ | ~~`authenticator.rs`: length-prefixed IKM concatenation.~~ **Done.** IKM collision theorem (`update_ikm_collision_exists`) added to `Update.lean`. | Needs D22 fix. |
| **3-e** | **D42** ✅ | ~~Prove `authenticator_update_diverges_on_bad_root_key` theorem.~~ **Done.** `update_diverges_on_bad_root_key` theorem added to `Update.lean`. | Needs 3-d. |

## Phase 4 — Spec annotation hygiene (independent, apply last)

| Order | Defect | Fix |
|---|---|---|
| **4-a** | **D23** ✅ | ~~Remove or `#[cfg(test)]`-gate spec files for test-only code.~~ **Done.** Audit comments added to `Encoding/Encoder/` and `Encoding/Decoder/` spec files. |
| **4-b** | **D35** ✅ | ~~Implement key-length validation or remove dead error variants.~~ **Done.** Gap-documenting theorems (`from_pb_no_key_length_check`, `from_pb_missing_validation`) added to `FromPb.lean`; audit comments in `FunctionalModels.lean`. |
| **4-c** | **D36** ✅ | ~~Fix `From<authenticator::Error>` mapping: `InvalidKeyLength` → `StateDecode`.~~ **Done.** Wrong-mapping theorems (`from_maps_all_to_mac_verify_failed`, `from_wrong_mapping_for_key_errors`) added to `Spqr/Specs/Lib/Error/From.lean`. |
| **4-d** | **D37** ✅ | ~~Change `pts_needed` to `u32` internally. Update Lean specs.~~ **Done.** Truncation-bound theorem (`into_pb_requires_u32_bound`) added to `IntoPb.lean`; audit comment in `FromPb.lean`. |
| **4-e** | **D52** ✅ | ~~Validate `is_complete` consistency in `from_pb`. Update `FromPb.lean`.~~ **Done.** Gap theorem (`from_pb_accepts_bad_is_complete`) added to `FromPb.lean`. |
| **4-f** | **D66** | Reject >9-byte varints. Update `DecodeVarint.lean`. |
| **4-g** | **D57** | Guard `chunk.index > 4095` in `add_chunk`. Update `AddChunk.lean`. |

## Dependency graph

```
Phase 0 (parallel)
  ├─ 0-a D20 VecDeque model ✅
  ├─ 0-b D15 sorry/axiom gaps
  └─ 0-c D10 false history bound
        │
   ┌────┴────────────────────┐
Phase 1 (spec alignment)    Phase 2 (erased preconditions)
  ├─ 1-a D4 ──► 1-b D65     ├─ 2-a D61
  ├─ 1-c D6                 ├─ 2-b D51 ✅
  └─ 1-d D7                 ├─ 2-c D54/D44
                             ├─ 2-d D53
                             └─ 2-e D58
        │                          │
        └──────────┬───────────────┘
              Phase 3 (compositional)
                ├─ 3-a D60 (needs 0-c)
                ├─ 3-b D56 ✅ (needs 0-a)
                ├─ 3-c D62 (needs 0-a)
                ├─ 3-d D55 ✅ (needs D22 fix)
                └─ 3-e D42 ✅ (needs 3-d)
                       │
              Phase 4 (hygiene, any order)
                D23 ✅, D35 ✅, D36 ✅, D37 ✅, D52 ✅, D66, D57
```

