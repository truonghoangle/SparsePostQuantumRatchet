# Evaluation of `docs/CorruptedBlobs.md` Against the Requested Questions

**Evaluated document**: `docs/CorruptedBlobs.md` (899 lines)
**Supporting artefact**: `Spqr/Specs/Bugs/CorruptedBlobs.lean` (Phases 1–10, 0 `sorry`)
**Source cross-checked**: `src/chain.rs`, `src/authenticator/serialize.rs`,
`src/encoding/polynomial.rs`, `Spqr/Specs/Chain/**`, `Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean`
**Evaluation date**: 2026‑09‑26

---

## 1. Scorecard

| # | Question | Answered? | Confidence | Evidence type |
|---|---|---|---|---|
| 1 | Does `from_pb` accept protobuf‑valid but semantically invalid SPQR states? | **Yes — answered** | High | Code reading + machine‑checked Lean (Phases 1, 6, 7, 8) — summarised in §2 |
| 2 | Which SPQR invariants can be violated by a state returned as `Ok` from `from_pb`? | **Yes — answered (substantially)** | High for the primary set; Medium for the `Chain`‑level and `PolyDecoder` rows | Per‑invariant tables in report §3, §7, §8, §9, §10.2; 9 of 15 identified invariants have a Lean witness |
| 3 | Can such an invalid state reach a downstream SPQR operation such as `key`, `get`, or `gc`? | **Yes — answered** | High for `recv_key` → `key`/`get`/`gc` (Lean end‑to‑end + runtime repro, §3A); Medium for `send_key` → `next_key` (prose in report, runtime repro added here) | Report §2, §2.1, §4–§6 call chains, §12; Lean Phases 3, 4, 9, 10; **five compiled‑Rust probes executed during this evaluation** (§3A.3) |
| 4 | Does the downstream operation panic/assert rather than return a recoverable error? | **Yes — answered (with one correction and two omissions)** | High for the three `assert!` sites + `copy_from_slice` (source + Lean + runtime); Medium for the failure‑mode *taxonomy* (report treats "panic" as the only hard failure and omits two sites and the profile dependence) | Report §4–§6 (source excerpts), §7/§13 (graceful `Err` cases), §14.6 (panic vs `Err` fix); Lean `*_never_ok` theorems; **five additional compiled probes in debug and release** (§3B.3) |
| 5 | Can the malformed state be persisted/round‑tripped, allowing the same invalid state to be restored again? | **Partially answered** — *Yes* is asserted and mechanised for `ChainEpochDirection` only (Phase 5); the `Chain`/`Authenticator`/`PolyDecoder` levels, the prost wire layer, and the **`Ok`‑path re‑persistence** (corruption written back by a *successful* `send`/`recv`) are missing or prose‑only | High that the answer is "yes" (confirmed at runtime here, §3C.3); Medium on the report's own evidence and framing | Report Exec. Summary / §1 / §12.1 / §13 ("crash loop"), §10.4 Phase 5 `corrupted_state_roundtrips`, §9 (cites `ProtocolDoS.lean`), §14.6 test #1; **four compiled probes in debug and release** (§3C.3) |

**Result: 4 of 5 requested questions fully answered; Q5 is partially answered by the report
and is closed empirically by this evaluation (§3C).** Q2 is answered *completely* at the level of
"which invariants", but the *evidence* for six of the fifteen invariants is prose‑only and
one invariant (`ctr` range) is named without analysis. Q3 is answered affirmatively and
mechanised for the `recv` path; the `send_key` path (I9) was prose‑only in the report and has
now been confirmed at runtime (§3A.3). Q4 is answered affirmatively for every panic‑class
invariant the report names, and the report also correctly identifies the *non*‑panicking
outcomes (`Err(EpochOutOfRange)`, silent divergence, stall); the residuals are one
mis‑attributed panic site, two unlisted panic sites and the debug/release dependence of the
overflow cases (§3B.4). Q5 is answered "yes" in prose and mechanised for one of the four
`from_pb` levels; the report's crash‑loop argument also conflates *reloading an unchanged old
blob after a panic* with *re‑persisting the corruption through an `Ok` call* — only the
latter is a property of SPQR, and the report never demonstrates it (§3C.4). An execution
plan to close the remaining gaps is given in §5.

---

## 2. Q1 Recap

All four persistence‑layer `from_pb` functions accept prost‑decodable blobs that violate
downstream structural invariants:

| `from_pb` | Source | What is checked | What is **not** checked |
|---|---|---|---|
| `ChainEpochDirection::from_pb` | `src/chain.rs:306‑312` | nothing (unconditional `Ok`) | `next.len()`, `prev.len() % 36`, `prev.len()` vs `ctr`, `ctr` range |
| `Chain::from_pb` | `src/chain.rs:434‑452` | `direction` enum, `Option` presence | `next_root.len()`, epoch ordering, per‑position `send.next`, `params` ranges |
| `Authenticator::from_pb` | `src/authenticator/serialize.rs:16‑21` | nothing (returns `Self`, infallible) | `root_key.len()`, `mac_key.len()` |
| `PolyDecoder::from_pb` | `src/encoding/polynomial.rs:815‑854` | `pts.len() == 16`, each slot `% 4 == 0` | per‑slot size bound, `is_complete`, `pts_needed` |

Machine‑checked: `from_pb_never_fails` (Phase 1), `authenticator_from_pb_no_validation`
(Phase 6), `chain_from_pb_admits_wrong_next_root` (Phase 7),
`poly_decoder_from_pb_admits_premature_is_complete` (Phase 8).

---

## 3. Q2 — Which invariants can be violated by an `Ok` state?

The report answers this question by enumerating, per `from_pb`, the field conditions that
downstream consumers *assume* (via a Lean spec hypothesis, a `hax_lib::requires`, a
`hax_lib::assume!`, or a runtime `assert!`) but that `from_pb` never establishes. The
consolidated table below is what the report supports; each row was re‑verified against the
current `src/` and `Spqr/Specs/` during this evaluation.

### 3.1. Invariants on `ChainEpochDirection` (report §3–§6, §10.2)

| # | Invariant (spec name) | Where required | Consumer | Failure when violated | Mechanised? |
|---|---|---|---|---|---|
| I1 | `next.length = 32` (`h_next_len`) | `NextKeyInternal.lean:41`, `NextKey.lean:29`, `Key.lean:483`, `recvKeyPre` (`Chain/Defs.lean:97`) | `next_key_internal` (`chain.rs:229` `assert!`, `:243` `copy_from_slice`) | **panic** | ✅ `from_pb_admits_wrong_next_length`, `next_key_internal_never_ok`, `key_never_ok_of_bad_next`, `restore_then_recv_panics_bad_next`, `recv_key_never_ok_bad_next` |
| I2 | `prev.data.length % 36 = 0` (`h_data_aligned` / `h_prev_aligned`) | `Get.lean:40,352`, `Gc.lean:85`, `Key.lean:488`, `recvKeyPre` (`Defs.lean:103`) | `KeyHistory::get` (`chain.rs:191` `assert_eq!`) | **panic** | ✅ `from_pb_admits_misaligned_prev`, `get_never_ok`, `key_never_ok_of_misaligned_prev`, `restore_then_recv_panics_misaligned_prev`, `recv_key_never_ok_misaligned_prev` |
| I3 | `prev.data.length ≤ 36 · ctr` (`h_prev_ctr`), implying `h_key_ge : trim_threshold ≤ data.length → max_ooo ≤ current_key` | `Key.lean:350`, `Gc.lean:798`, `recvKeyPre` (`Defs.lean:104`) | `KeyHistory::gc` (`chain.rs:149` `assert!`) | **panic** (unsigned‑underflow guard) | ✅ `from_pb_admits_large_prev_small_ctr`, `gc_never_ok`, `key_never_ok_of_large_prev_small_ctr`, `restore_then_recv_panics_large_prev_small_ctr`, `recv_key_never_ok_large_prev_small_ctr` |
| I4 | `ctr ≤ U32.max − 390451572` (`h_ctr_bound`; 32‑bit variant `U32.max − 108458770`) and `ctr < U32.max` (`h_ctr_lt`) | `Key.lean:537,487`, `Key32.lean:615`, `recvKeyPre` (`Defs.lean:100,102`) | `key()` — `self.ctr + max_ooo_keys` (`chain.rs:265,279`) guarded only by `hax_lib::assume!` (`chain.rs:262‑264`); `next_key_internal` `*ctr += 1` (`chain.rs:230`) | **debug: overflow panic; release: wrapping arithmetic** → wrong GC / clear decisions | ⚠️ Listed in report §10.2 table (`h_ctr_bound`) but **no analysis, no Lean witness, no fix**; absent from §13/§15 |
| I5 | `prev.data.length + 36·(index − ctr) ≤ Usize.max` (`h_kh_cap`) | `Key.lean:486`, `recvKeyPre` (`Defs.lean:101`) | `KeyHistory::add` (`chain.rs:140‑141`) | Allocation failure only for absurd sizes — not reachable from a realistic blob | ❌ Not in report (reasonably omitted; noted for completeness) |

### 3.2. Invariants on `Chain` (report §7, §14.1a, §14.2)

| # | Invariant | Where required | Consumer | Failure when violated | Mechanised? |
|---|---|---|---|---|---|
| I6 | `next_root.length = 32` | Construction (`Chain::new`, `chain.rs:345`; `add_epoch`, `chain.rs:364`) | `add_epoch` → `kdf::hkdf_to_slice` with `next_root` as salt (`chain.rs:357‑361`) | **No panic** — silent key divergence from the next epoch; surfaces as a Signal‑layer decryption failure, not `InvalidCtMac` | ✅ `chain_from_pb_admits_wrong_next_root` (Phase 7); downstream divergence **not** mechanised |
| I7 | `send_epoch ≤ current_epoch` | `send_key` / `epoch_idx` (`chain.rs:372‑388`) | `epoch_idx` | Graceful `Err(EpochOutOfRange)`; send stall until `add_epoch` catches up | ❌ Prose only |
| I8 | `links.length ≥ 1` and `current_epoch − send_epoch < links.length` | `epoch_idx` (`chain.rs:378`) | `epoch_idx` | Graceful `Err(EpochOutOfRange)` — report correctly notes this is *not* a panic | ❌ Prose only |
| I9 | Position‑dependent `send.next`: `links[i].send.next.length = 32` for all `i ≥ epoch_idx(send_epoch)` (only `i < send_idx` may be cleared by `clear_next()`, `chain.rs:396‑399`); `recv.next.length = 32` for all `i` | `send_key` `hax_lib::assume!` (`chain.rs:401‑405`); `recvKeyPre` for `recv` | `send_key` → `next_key` → `next_key_internal` | **panic** (`chain.rs:229`) — the case §14.1's weak check alone cannot catch | ❌ Prose only for `send` (the `recv` side is I1) |
| I10 | `params.max_ooo_keys_or_default() < 390451572` | `hax_lib::assume!` (`chain.rs:86, 262‑264, 275‑277`); `h_maxooo_bound` (`Key.lean:63,197`), `h_ooo` (`Gc.lean:797,833`), `recvKeyPre` (`Defs.lean:99`) | `key()` `ctr + max_ooo_keys` (`chain.rs:265,279`); `trim_size()` `max_ooo * 11 / 10` (`chain.rs:87`) | **debug: overflow panic; release: wrap** → GC horizon / clear decision computed on wrapped values | ❌ Prose only (§7 table, §14.1a) |
| I11 | `params.trim_size() < 119304647` and `prev.data.len() ≤ 36 · trim_size()` | `hax_lib::requires` on `KeyHistory::add`/`remove` (`chain.rs:138,174`); `hax_lib::assume!` (`chain.rs:280‑283`) | `add`, `remove`, `gc` (`chain.rs:146` `trim_size() * KEY_SIZE`) | Oversized `trim_size` disables GC → unbounded `prev.data` growth; `trim_size() * 36` may overflow `usize` on 32‑bit | ❌ Prose only (§7 table, §14.1a) |
| I12 | `index + max_ooo_keys ≤ U32.max` (`h_ooo_no_overflow`) | `Get.lean:354`, `Key.lean:491`, `recvKeyPre` (`Defs.lean:105`) | `KeyHistory::get` (`chain.rs:192`) | Overflow on `at + max_ooo` | ➖ **Correctly excluded** by report §10.2: `index` is message‑derived (Finding 4 in `report.md`), not a blob invariant. A corrupted `params.max_ooo_keys` (I10) does make it easier to violate. |

### 3.3. Invariants on `Authenticator` (report §8)

| # | Invariant | Where required | Consumer | Failure when violated | Mechanised? |
|---|---|---|---|---|---|
| I13 | `root_key.length = 32 ∧ mac_key.length = 32` | Construction (`Authenticator::new`, HKDF → 32 bytes each) | `mac_ct` / ratchet step | No panic (HMAC accepts any key length); non‑standard key material — LOW severity, robustness only | ✅ `authenticator_from_pb_admits_empty_mac_key`, `…_empty_root_key`, `…_wrong_key_lengths` (Phase 6) |

### 3.4. Invariants on `PolyDecoder` (report §9)

| # | Invariant | Where required | Consumer | Failure when violated | Mechanised? |
|---|---|---|---|---|---|
| I14 | `is_complete = false` unless the message has actually been decoded | Construction (`new_with_poly_count`, `polynomial.rs:789`) | `decoded_message` (`polynomial.rs:912‑914` returns `None` when `is_complete`) | Permanent epoch stall (Finding 5) — no panic | ✅ `poly_decoder_from_pb_admits_premature_is_complete`, `…_stalled_decoder` (Phase 8) |
| I15 | `pts[i].len() ≤ 2·MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1 = 71` per slot | `hax_lib::assume!` in `into_pb` (`polynomial.rs:801`); `add_chunk` gating (`polynomial.rs:895‑896`) | `into_pb`; `decoded_message` uses only `&pts[..necessary_points(i)]` (`polynomial.rs:922`) | Extra points are **ignored** by `decoded_message`, so an oversized slot is neither a panic nor a stall — only excess memory / serialised size. **The report's "silent stall" attribution for this row is not substantiated.** | ❌ Prose only |
| (I16) | `pts_needed ≤ 576` | Every V1 call site checks `pts_needed` exactly (`src/v1/chunked/send_*/serialize.rs`) | — | Not violable in production; report §9 correctly classifies as defense‑in‑depth only | ➖ Correctly excluded |

### 3.5. Summary of the Q2 answer

**Invariants violable by an `Ok` result of `from_pb`** — 15 identified, 12 with a real
behavioural consequence:

- **Panic class** (session bricked): I1, I2, I3, I9; plus I4, I10 in debug builds (release
  builds wrap instead).
- **Silent‑divergence class** (session unusable, cause obscured): I6.
- **Stall / graceful‑`Err` class**: I7, I8 (graceful `Err`), I14 (permanent stall),
  I11 (GC disabled → unbounded growth).
- **Weakened‑crypto‑property class** (robustness only): I13.
- **No practical consequence / correctly excluded**: I5, I12, I15 (memory only), I16.

The report explicitly names **I1, I2, I3, I4 (table row only), I6, I7, I8, I9, I10, I11,
I13, I14, I15** and explicitly *excludes* **I12 and I16** with correct reasoning. It does
not mention I5, which is acceptable (unreachable from any realistic blob).

---


## 3A. Q3 — Can an invalid `Ok` state reach `key`, `get`, or `gc`?

**Short answer: Yes.** Nothing sits between `from_pb` and the consumers. The report answers
this in three layers, all of which were re‑verified against `src/` during this evaluation,
and a fourth layer (compiled‑Rust execution) was added here because the report had none.

### 3A.1. Static call‑chain evidence (report §2, §2.1, §4–§6)

| Entry point | Path to consumer | Guard between `from_pb` and consumer? |
|---|---|---|
| `spqr::recv` (`lib.rs:356`) | `decode_state` (`:362`) → `chain_from` (`:428`) → `Chain::from_pb` (`chain.rs:434`) → `ChainEpochDirection::from_pb` (`:306`) → `chain.recv_key(epoch, index)` (`lib.rs:435`) → `epoch_idx` (`chain.rs:410`) → `links[i].recv.key(index, params)` (`:411`) | **None.** Only `epoch_idx` (epoch range) and the `msg_key_epoch == 0 && index == 0` shortcut (`lib.rs:432`) can skip `key`. Neither inspects `next`/`prev`/`ctr`. |
| `ChainEpochDirection::key` (`chain.rs:247`) → `KeyHistory::get` (`:255`) | `at < ctr` branch — first statement is `assert_eq!(data.len() % 36, 0)` (`:191`) | None |
| `key` → `next_key_internal` (`:274`, `:293`) | `ctr < at ≤ ctr + max_jump` branch — `assert!(!next.is_empty())` (`:229`), `copy_from_slice` (`:243`) | Only `hax_lib::assume!` (`:273`, `:291`) — a proof hint, **not** a runtime check |
| `key` → `KeyHistory::gc` (`:289`) | every forward‑path call, unconditionally, after the advancing loop | None; `assert!(current_key >= max_ooo)` (`:149`) |
| `spqr::send` (`lib.rs:265`) | `decode_state` → `Chain::from_pb` (`:288`) → `chain.send_key(msg.epoch − 1)` (`:300`) → `links[send_idx].send.next_key()` (`chain.rs:406`) → `next_key_internal` | Only `hax_lib::assume!` (`chain.rs:401‑405`) — not a runtime check |
| Version‑downgrade branch of `recv` (`lib.rs:401‑404`) | `chain_from(prenegotiated_state_pb.chain, …)` → `Chain::from_pb` | None (then falls into the same `recv_key` path) |

The only way `Chain::from_pb` is bypassed is the very first `send`/`recv` of a session
(`chain == None`, `lib.rs:333‑341`), so once a chain has been persisted, **every** subsequent
`send()`/`recv()` loads it through `from_pb` and immediately drives it into `send_key` or
`recv_key`.

### 3A.2. Mechanised reachability (`Spqr/Specs/Bugs/CorruptedBlobs.lean`, 0 `sorry`)

| Consumer | Reached from | Lean theorem(s) | Hypotheses (the "when") |
|---|---|---|---|
| `next_key_internal` | `key` (forward path) | `key_never_ok_of_bad_next` (Phase 3), `key_loop_preserves_next_length` | `ctr < at ≤ ctr + maxJump`, `next.length ≠ 32` |
| `KeyHistory::get` | `key` (out‑of‑order path) | `key_never_ok_of_misaligned_prev` (Phase 3) | `at < ctr`, `prev.length % 36 ≠ 0` |
| `KeyHistory::gc` | `key` (`at = ctr + 1`) | `key_never_ok_of_large_prev_small_ctr` (Phase 3) | `at = ctr + 1`, `(maxOoo·11/10+1)·36 ≤ prev.length`, `ctr < maxOoo` |
| all three | `from_pb` ∘ `key` | `restore_then_recv_panics_{bad_next,misaligned_prev,large_prev_small_ctr}` (Phase 4) | `from_pb pb = ok (Ok ced)` + the above |
| all three | **`Chain.recv_key`** | `recv_key_never_ok_of_key_never_ok`, `recv_key_never_ok_{bad_next,misaligned_prev,large_prev_small_ctr}` (Phase 10) | `epoch ≤ current_epoch`, `current_epoch − epoch < links.length` (i.e. `epoch_idx` succeeds) |
| `recv_key_spec` precondition | — | `recvKeyPre_unsatisfiable_*` (Phase 9) | shows the *spec* cannot even be applied to corrupted state |

Phase 10 is the strongest form: `∀ r, Chain.recv_key self epoch index ≠ ok r`, i.e. the
public `recv_key` **itself** has no non‑panicking execution once its `recv` direction is
corrupted and the epoch is in range. That is precisely Q3 for the `recv` side.

**Not mechanised for Q3**: (a) the `send_key` → `next_key` route (I9); (b) the lift from
`spqr::recv`/`spqr::send` (`lib.rs`) down to `Chain::recv_key`/`send_key` — the Lean model
stops at the `Chain` API. Both are covered by the runtime probes below.

### 3A.3. Runtime confirmation (performed during this evaluation)

Because the report contained no compiled‑Rust reproduction (gap G5), five probe tests were
added to the existing `#[cfg(test)] mod test` in `src/chain.rs`, executed with
`cargo test --lib q3_probe -- --nocapture --test-threads=1` (5 passed), and then **removed**
from `src/chain.rs` (working tree restored with `git checkout -- src/chain.rs`). The probe
source is preserved as `docs/corrupted_blob_counterexample.rs.txt`, following the repo
convention for `docs/*_counterexample.rs.txt`.

| Probe | Blob mutation (after `into_pb()`) | Operation | Observed panic (stable‑aarch64, debug) |
|---|---|---|---|
| `q3_probe_bad_next_reaches_next_key_internal_via_recv_key` (I1) | `links[0].recv.next = vec![0; 31]` | `Chain::from_pb(pb)` → `Ok`; `recv_key(0, 1)` | `src/chain.rs:243:14` — `copy_from_slice: source slice length (32) does not match destination slice length (31)` |
| `q3_probe_misaligned_prev_reaches_get_via_recv_key` (I2) | `recv.ctr = 5`, `recv.prev = vec![0; 37]` | `recv_key(0, 1)` (`at < ctr`) | `src/chain.rs:191:9` — `assertion left == right failed` (`37 % 36 ≠ 0`) |
| `q3_probe_large_prev_small_ctr_reaches_gc_via_recv_key` (I3) | `recv.ctr = 0`, `recv.prev = vec![0; 36·2201]` | `recv_key(0, 1)` | `src/chain.rs:149:13` — `assertion failed: current_key >= params.max_ooo_keys_or_default()` |
| `q3_probe_empty_send_next_reaches_next_key_via_send_key` (I9) | `links[0].send.next = vec![]` | `send_key(0)` | `src/chain.rs:229:9` — `assertion failed: !next.is_empty()` |
| `q3_probe_top_level_recv_reaches_panic` (full production path) | Two real `send`/`recv` round‑trips via the public API (`initial_state`/`send`/`recv`), then `PqRatchetState::decode` the persisted blob, set every `links[i].recv.next = vec![0]`, re‑encode; peer sends one more message | **`spqr::recv(&corrupted, &msg)`** (`lib.rs:356`) | `src/chain.rs:243:14` — `copy_from_slice: … destination slice length (1)` |

All five `Chain::from_pb` calls returned `Ok` on the corrupted blob, and all five downstream
operations panicked at exactly the line the report predicts (`:243`, `:191`, `:149`, `:229`).
The fifth probe closes the `lib.rs` → `Chain` gap: the corruption reaches `next_key_internal`
through the **public** `spqr::recv` entry point, after `decode_state`, `States::from_pb` and
`chain_from`, with no intervening check.

### 3A.4. Verdict on Q3

- **Reachability**: established for all three named consumers (`key`, `get`, `gc`) on the
  `recv` path — statically (call chain), formally (Lean Phases 3/4/10), and empirically
  (compiled probes). Also established for `next_key_internal` on the `send` path
  (empirically here; prose only in report §7).
- **Trigger conditions** are ordinary protocol traffic, not attacker‑chosen inputs: the very
  next in‑order message (`at = ctr + 1`) hits `next_key_internal` and `gc`; any out‑of‑order
  message (`at < ctr`) hits `get`; any `send()` hits `next_key`.
- **Residual weakness of the report's own Q3 answer**: it relies on the Lean model plus prose
  for the `send_key` route and for the `lib.rs` lift; it had no executable reproduction.
  That is now supplied (§3A.3) and should be folded back into the report (§5, Step 2).

---

## 3B. Q4 — Does the downstream operation panic/assert rather than return a recoverable error?

**Short answer: Yes, for every panic‑class invariant the report names (I1, I2, I3, I9).**
The consumers `next_key_internal`, `KeyHistory::get` and `KeyHistory::gc` fail via
unconditional `assert!`/`assert_eq!`/slice‑length panics, not via `Err`. The report is also
careful — and correct — to classify several *other* corrupted fields as **recoverable or
silent** rather than panicking (`send_epoch > current_epoch`, empty `links`, `next_root`,
`Authenticator` keys, `PolyDecoder::is_complete`). The residual issues are of taxonomy, not
substance: one panic is attributed to the wrong line, two panic sites are not listed, and
the arithmetic‑overflow cases (I4, I10) are described without noting that they panic *only*
in debug builds.

### 3B.1. What the report says

| Report location | Claim | Verified against `src/chain.rs`? |
|---|---|---|
| §4 (Panic Path 1) | `next_key_internal` fails on `assert!(!next.is_empty())` (`:229`) and, for `0 < len ≠ 32`, on `copy_from_slice` (`:243`) | ✅ Both are unconditional panics. `next_key_internal` returns `(u32, [u8; 32])` — it has **no** `Err` channel at all. |
| §5 (Panic Path 2) | `KeyHistory::get` fails on `assert_eq!(data.len() % 36, 0)` (`:191`) | ✅ Panics *before* the `Err(KeyTrimmed)` / `Err(KeyAlreadyRequested)` branches it otherwise returns. |
| §6 (Panic Path 3) | `KeyHistory::gc` fails on `assert!(current_key >= max_ooo)` (`:149`) | ✅ `gc` returns `()` — no `Err` channel. |
| §7 table, §13 | `send_epoch > current_epoch`, `links.is_empty()` → graceful `Err(EpochOutOfRange)`; `next_root` → silent divergence, `Ok` returned | ✅ `epoch_idx` (`:372‑382`) returns `Err` on both conditions; confirmed at runtime (§3B.3, probe 5). |
| §8, §9 | `Authenticator` / `PolyDecoder` corruption → no panic (weak MAC / stall) | ✅ Consistent with source (HMAC accepts any key length; `decoded_message()` gated on `is_complete`). |
| §13 "No graceful degradation" | "Failures are `panic!`/`assert!` crashes, not `Err` returns" | ✅ For I1–I3/I9. Slightly over‑broad as a blanket statement given §7's own graceful cases — but §13 is explicitly scoped to the §4–§6 paths. |
| §14.6 | Proposes converting the asserts to `Err(Error::InternalInvariantViolation)`; correctly notes `gc` and `next_key_internal` need **signature changes** because they currently have no `Result` return | ✅ Matches source: only `get` already returns `Result`. |
| §2.1, Exec. Summary | Panics become bridge‑level `UnexpectedPanic`; session unrecoverable because libsignal never resets `pq_ratchet_state` | Consistent with `docs/evaluate.md` Q1/Q7 verification of libsignal `a47ba487`. |

The Lean evidence is of exactly the right form for this question: every `*_never_ok`
theorem (`next_key_internal_never_ok`, `get_never_ok`, `gc_never_ok`, `key_never_ok_of_*`,
`recv_key_never_ok_*`) states `∀ r, f … ≠ ok r` — i.e. *no* `Result` value, neither `Ok`
nor `Err`, is produced. In the Aeneas model that is precisely "diverges/panics", so the
theorems distinguish "panic" from "returns `Err`" mechanically, not just by prose.

### 3B.2. Cross‑check of every panic candidate on the `key` path

Independent enumeration of every operation between `Chain::from_pb` and the end of
`ChainEpochDirection::key` that can abort, compared with the report:

| Site (`src/chain.rs`) | Construct | Trigger from a blob | Profile | In report? |
|---|---|---|---|---|
| `:229` | `assert!(!next.is_empty())` | `next = []` (recv, or send at/after `send_idx`) | debug **and** release | ✅ §4 |
| `:243` | `next.copy_from_slice(&genr8r[..32])` | `next.len() ∉ {0, 32}` | debug and release | ✅ §4 |
| `:191` | `assert_eq!(data.len() % 36, 0)` | misaligned `prev`, `at < ctr` path | debug and release | ✅ §5 |
| `:149` | `assert!(current_key >= max_ooo)` | large aligned `prev`, small `ctr` | debug and release | ✅ §6 |
| **`:157`** | `self.data[i..i + 4]` in `gc` loop | **misaligned `prev` whose length ≥ `trim_size·36`, on the *forward* path (`at > ctr`)** — `gc` has no alignment assert, so the loop runs off the end | debug and release | ❌ **Not listed.** The report treats misalignment as a `get`‑only panic (§5) and says of `gc` only "the assertion guards against unsigned underflow". Confirmed at runtime: `range end index 4 out of range for slice of length 1` (§3B.3, probe 2). |
| **`:265`, `:279`** | `self.ctr + params.max_ooo_keys_or_default()` | `ctr` near `u32::MAX`, or `ctr` + huge `max_ooo_keys` (I4/I10) | **debug only** (`overflow-checks`); release wraps silently | ⚠️ Mentioned in §7 as "overflows … causing incorrect GC / key‑skip behaviour" and in §14.1a as "wrapping arithmetic" — the report never says it **panics in debug/test builds** (confirmed: `attempt to add with overflow` at `:265`, probe 3) nor that release builds instead return `Ok` with wrong semantics (probe 3, release). `Cargo.toml` sets no `[profile]` overrides, so libsignal release builds wrap. |
| `:230` | `*ctr += 1` in `next_key_internal` | `ctr = u32::MAX` with `at > ctr` — unreachable, since `at: u32` cannot exceed `u32::MAX` and `at == ctr` returns `Err(KeyAlreadyRequested)` | — | n/a (correctly not raised) |
| `:250` | `at - self.ctr` | guarded by `Ordering::Greater` | — | n/a |
| `:192` | `at + max_ooo` in `get` | `at` near `u32::MAX` **and** `at < ctr` — requires `ctr ≈ u32::MAX` too; debug‑only overflow | debug only | ❌ Not listed (very low practical relevance; noted for completeness) |
| `:244` | `.try_into().expect("correct size")` | `genr8r[32..]` is always 32 bytes — unreachable | — | n/a |
| `:140‑141` | `Vec::extend_from_slice` in `add` | allocation failure only (`h_kh_cap`) | — | n/a |

**Attribution nuance in the report.** §4 correctly attributes the `next.len() = 31` case to
`:243` (`copy_from_slice`), but §12.1 and §13 describe the primary trigger generically as
"assert at `:229`". For `next = []` the panic is indeed `:229`; for a 31‑byte `next` the
`assert!` passes and the panic is the `copy_from_slice` length mismatch at `:243` (§3A.3).
Both are panics, so the Q4 *answer* is unaffected, but the "expected panic site" column in
any regression test must distinguish them.

### 3B.3. Runtime confirmation (performed during this evaluation)

Five further probes were added to `#[cfg(test)] mod test` in `src/chain.rs`, executed in
**both** profiles, then removed (`git checkout -- src/chain.rs`). Source appended to
`docs/corrupted_blob_counterexample.rs.txt` under the "Q4 probes" banner.

```
cargo test --lib           q4_probe -- --nocapture --test-threads=1   # 5 passed
cargo test --release --lib q4_probe -- --nocapture --test-threads=1   # 5 passed
```

| # | Probe | Blob mutation | Call | Debug result | Release result |
|---|---|---|---|---|---|
| 1 | `q4_probe_empty_recv_next_hits_assert_229` | `recv.next = []` | `recv_key(0, 1)` | **panic** `chain.rs:229:9 assertion failed: !next.is_empty()` | **panic** (same) |
| 2 | `q4_probe_misaligned_large_prev_forward_path_hits_gc_slice_index` | `recv.ctr = 5000`, `recv.prev = [0; 36·2201 + 1]` | `recv_key(0, 5001)` (forward path → `gc`) | **panic** `chain.rs:157:48 range end index 4 out of range for slice of length 1` | **panic** (same) |
| 3 | `q4_probe_ctr_overflow_profile_dependent` | `recv.ctr = u32::MAX − 1` | `recv_key(0, u32::MAX)` | **panic** `chain.rs:265:17 attempt to add with overflow` | **`Ok(32‑byte key)`** — silent wrap |
| 4 | `q4_probe_max_ooo_overflow_profile_dependent` | `params.max_ooo_keys = u32::MAX` | `recv_key(0, 1)` | `Ok(32‑byte key)` (no overflow: `0 + u32::MAX` fits; `trim_size()` is computed in `usize`) | `Ok(32‑byte key)` |
| 5 | `q4_probe_graceful_err_epoch_inversion` | `send_epoch = 7` (> `current_epoch = 0`) | `send_key(7)`; `send_key(0)` | `Err(EpochOutOfRange(7))`; `Err(SendKeyEpochDecreased(7, 0))` — **recoverable** | same |

Together with the five Q3 probes (§3A.3: panics at `:243`, `:191`, `:149`, `:229`, and
`:243` via public `spqr::recv`), this gives direct runtime evidence for the answer.

Probe 4 is an instructive negative: with `ctr = 0`, `max_ooo_keys = u32::MAX` does **not**
overflow at `:265`, and `trim_size()` (`chain.rs:86‑88`) is evaluated in `usize`, so the
`assume!`d bound `max_ooo < 390451572` being violated has no immediate panic — it only
disables GC (`trim_size·36` ≈ 170 GB threshold). The report's §7 wording ("overflows the
`ctr + max_ooo_keys` addition") is therefore only true once `ctr` is also large; the
practically relevant consequence is unbounded `prev` growth, as §7's `trim_size` row says.

### 3B.4. Verdict on Q4

- **Answered: Yes.** For I1, I2, I3 and I9 the downstream operation panics — established by
  source excerpts (§4–§6), by the `∀ r, … ≠ ok r` Lean theorems, and now by compiled probes
  in both debug and release. `next_key_internal` and `gc` have no `Result` return at all, so
  a recoverable error is not even representable without the §14.6 signature changes.
- **The report correctly separates the recoverable cases** (`Err(EpochOutOfRange)` for
  epoch inversion / empty `links`; `Ok` with silent divergence for `next_root`; stall for
  `is_complete`) and does not over‑claim panics for them.
- **Residual gaps** (feed into §5):
  - **G7** — unlisted panic site `chain.rs:157` (`gc` slice index on misaligned + large
    `prev`, forward path). This matters for §14.6: converting `get`'s `assert_eq!` to `Err`
    alone leaves `gc` panicking on the same corruption.
  - **G8** — I4/I10 overflow described as "wrapping" only; the report should state that the
    `+` at `:265`/`:279` **panics in debug/test builds and wraps in release**, and that
    `Cargo.toml` has no `overflow-checks` override. The wrapped release value then feeds
    `prev.clear()` and the `add` guard, i.e. wrong GC decisions rather than a crash.
  - **G9** — §12.1/§13 conflate the `:229` and `:243` panic sites; regression tests must
    expect the right one per mutation.
  - **G10** — §13's "Failures are `panic!`/`assert!` crashes, not `Err` returns" should be
    scoped to §4–§6 explicitly, since §7 documents `Err` outcomes.

---

## 3C. Q5 — Can the malformed state be persisted/round‑tripped, allowing the same invalid state to be restored again?

**Short answer: Yes — and the report says so, but proves it for only one of the four
`from_pb` layers and only in the weakest of the three senses that matter.** Every
`into_pb` in the persistence path is a pure field‑by‑field repackaging with no
normalisation, so `into_pb ∘ from_pb` is the identity on every protobuf‑valid blob,
corrupted or not. This evaluation confirmed the identity at runtime for all ten corruption
classes of §3 (I1–I4, I6, I7, I9, I10 plus `max_jump`) at the `Chain` level, through the
real prost wire encoding, and for `Authenticator` and `PolyDecoder`. It also demonstrated
the stronger, previously undocumented form: a corrupted blob can pass through a
**successful** `spqr::recv()` and be written back — still corrupted — into the state the
caller is told to persist.

### 3C.1. What the report says

| Report location | Claim | Verified? |
|---|---|---|
| Exec. Summary; §1 table ("crash loop on reload"); §12.1 steps 4–6 ("Every restart loads the corrupted state and panics"); §13 ("every restart loads the same corrupted state and panics again") | The corrupted blob is reloaded on every restart and the panic recurs | ✅ True, but this is the **panic → no re‑write** case: the state is never replaced *because* the call aborted. That property depends on the host keeping the pre‑call blob (libsignal does, `docs/evaluate.md` Q7), not on anything SPQR does. |
| §10.4 / Phase 5 `corrupted_state_roundtrips` (`CorruptedBlobs.lean:581‑607`) | `into_pb (from_pb pb)` returns `pb'` with `pb'.ctr = pb.ctr ∧ pb'.next = pb.next ∧ pb'.prev = pb.prev` | ✅ Machine‑checked, 0 `sorry`. Scope: **`ChainEpochDirection` only.** Composed from `from_pb_spec` and `into_pb_spec` (`Spqr/Specs/Chain/ChainEpochDirection/IntoPb.lean:25`). |
| §9 (cites `Spqr/Specs/Bugs/ProtocolDoS.lean` `poison_survives_persistence`) | Poisoned `PolyDecoder` points survive `into_pb` | ✅ Mechanised, but for **`into_pb` alone** (point coordinates + `is_complete` preserved), and for Finding 2's poisoned *y*‑values rather than the corrupted‑blob fields of this study. |
| §7 Phase 7 `chain_from_pb_admits_wrong_next_root` | `next_root` survives `Chain::from_pb` | ✅ Mechanised — but only the `from_pb` half. `Chain::into_pb` is `#[hax_lib::opaque]` (`chain.rs:414`), so no Lean statement exists for `Chain`‑level `into_pb ∘ from_pb`. |
| §14.6 recommended test #1 | A proptest that round‑trips `Chain::into_pb → from_pb` on *valid* states | Recommended, not done. Purpose is regression protection for the §14.2 fix, not evidence for Q5. |
| §8 `Authenticator` | Wrong‑length keys accepted | ✅ (Phase 6), but **no round‑trip statement at all** for `Authenticator`, although `serialize.rs:9‑21` is trivially identity. |

**Absent from the report:** (a) any statement that the *prost* layer preserves the blob
(`encode_to_vec`/`decode` on `pqrpb::Chain`); (b) any demonstration that a corrupted state
can be re‑serialised by an **`Ok`** `send`/`recv` — i.e. that SPQR itself, not the host's
"keep old state on error" policy, propagates the corruption; (c) the observation that some
corruptions are **latent** (survive many successful round‑trips before the first panic).

### 3C.2. Source analysis: why the round‑trip is the identity

| Layer | `into_pb` | `from_pb` | Identity on corrupted input? |
|---|---|---|---|
| `ChainEpochDirection` | `chain.rs:298‑304` — moves `ctr`, `next`, `prev.data` | `chain.rs:306‑312` — moves them back | ✅ Trivially (mechanised, Phase 5) |
| `Chain` | `chain.rs:415‑431` — `dir.into()`, epochs, `links.map(into_pb)`, `next_root`, `Some(params)` | `chain.rs:434‑452` — `direction.try_into()`, epochs, `links.map(from_pb)`, `next_root`, `params.ok_or` | ✅ For every blob `from_pb` accepts: the only lossy step is `Direction` `i32 ↔ enum`, and `from_pb` rejects unknown values, so accepted blobs round‑trip exactly. `links` ordering is preserved by `VecDeque` ↔ `Vec`. |
| `Authenticator` | `serialize.rs:9‑14` | `serialize.rs:16‑21` (`clone`) | ✅ Byte‑exact for any key lengths |
| `PolyDecoder` | `polynomial.rs:793‑811` — re‑serialises each `Pt` as 4 bytes, `polys = 16`, copies `is_complete`, `pts_needed as u32` | `polynomial.rs:815‑854` — requires 16 slots, each `%4 == 0` | ✅ For accepted blobs with `polys == 16` and `pts_needed ≤ u32::MAX` (both hold for any blob `into_pb` produced). `Pt::deserialize`/`serialize` are inverse on 4‑byte groups; `SortedSet::push` only de‑duplicates equal `x` — a corrupted slot with **duplicate `x`** would be *normalised* (last‑write‑wins), the one non‑identity case, and it moves the state *toward* validity. |
| prost wire | `PqRatchetState::encode_to_vec` (`lib.rs:315, 445`) | `decode_state` (`lib.rs:472‑481`) | ✅ Proto3 scalars/bytes/repeated fields are canonical; verified empirically (§3C.3, probe 1). |

Because `spqr::send`/`recv` unconditionally re‑encode `chain.into_pb()` into the returned
`state` (`lib.rs:301, 313, 443`), **whatever `Chain::from_pb` accepted and the operation did
not mutate is written back verbatim.**

### 3C.3. Runtime confirmation (performed during this evaluation)

Four probes were added to `#[cfg(test)] mod test` in `src/chain.rs`, run with
`cargo test --lib q5_probe -- --nocapture --test-threads=1` (debug) and
`cargo test --release --lib q5_probe -- --test-threads=1` (release) — **4 passed in each
profile** — then removed (`git checkout -- src/chain.rs`). The source is appended to
`docs/corrupted_blob_counterexample.rs.txt` under the "Q5 probes" banner.

| Probe | What it does | Result |
|---|---|---|
| `q5_probe_chain_level_roundtrip_is_identity_on_corrupted_blobs` | For each of 10 mutations (`recv.next` = 31 B / `[]`; `recv.prev` = 37 B; `ctr = 0` + 79 236 B `prev`; `ctr = u32::MAX`; `next_root` = 16 B; `send_epoch = 7 > current_epoch`; `send.next = []`; `max_ooo_keys = u32::MAX`; `max_jump = u32::MAX`): `Chain::from_pb(pb)` → `Ok`, `into_pb()` `== pb`, and prost `encode_to_vec`/`decode` `== pb` | ✅ All 10 blobs round‑trip **byte‑for‑byte** through both the struct layer and the wire layer |
| `q5_probe_misaligned_prev_survives_ok_recv_and_is_repersisted` | `recv.ctr = 5`, `recv.prev = 37 B`; `recv_key(0, 7)` (in‑order, forward) | ✅ Returns **`Ok`** (32‑byte key); `into_pb()` shows `ctr = 7`, `prev.len() = 73` (37 + 36 — still `% 36 ≠ 0`). Reloading that blob with `from_pb` succeeds; the next out‑of‑order `recv_key(0, 6)` then panics at `chain.rs:191`. |
| `q5_probe_top_level_recv_ok_repersists_misaligned_prev` | Full public‑API path: two real `send`/`recv` exchanges, decode A's blob, `prev.push(0)` on every `recv.prev`, re‑encode; B sends one more in‑order message | ✅ **`spqr::recv(&corrupted, &msg)` returns `Ok`**, the derived key equals B's send key (corruption is invisible to the protocol), and the **returned `state`** decodes to a chain whose `recv.prev` length is `1` — misaligned. The host would persist this as the new good state. |
| `q5_probe_authenticator_and_poly_decoder_roundtrip_corruption` | `Authenticator { root_key: 5 B, mac_key: [] }`; `PolynomialDecoder { is_complete: true, pts: 16 × [] }` | ✅ Both `into_pb(from_pb(pb)) == pb` |

Both overflow‑class blobs (`ctr = u32::MAX`, `max_ooo_keys = u32::MAX`) also round‑trip
unchanged in release; combined with §3B.4/G8 this means the release‑profile *wrapping*
behaviour is applied to a value that persists indefinitely.

### 3C.4. Verdict on Q5

- **Answered: Yes, the malformed state persists and can be restored** — in three distinct
  senses, of which the report covers only the first explicitly and mechanises the second
  for one layer:
  1. **Reload after panic** (report §12.1/§13): the aborted call never produces a new blob,
     so the host reloads the old one. True, but a host‑policy property, not an SPQR one.
  2. **Identity round‑trip** (report Phase 5, `ChainEpochDirection` only): `into_pb ∘ from_pb
     = id` on corrupted input. Now confirmed at every layer — `Chain`, prost wire,
     `Authenticator`, `PolyDecoder` — by probes 1 and 4.
  3. **Propagation through an `Ok` call** (not in the report): a corrupted blob can be
     loaded, used successfully, and written back still corrupted (probes 2 and 3). This is
     the form that defeats any host‑side "roll back to last good state" strategy, because
     the *last good state* is itself corrupted; it also means corruption survives backups
     taken *after* the corruption event and can reach another device via state sync while
     looking healthy.
- **Latent vs immediate corruption.** The report treats all §3 corruptions as crashing on
  the "next `recv()`". That is accurate for `next.len() ≠ 32` (`next_key_internal` runs on
  every forward message) and for `ctr = 0` + large `prev` (GC fires on the next message),
  but **misaligned `prev`** panics only on the *out‑of‑order* path (`get`, `:191`) or once
  `prev` exceeds the GC threshold (`gc` slice index, `:157`, G7). Until then every in‑order
  message succeeds and re‑persists the misalignment (probe 2 shows it *growing*: 37 → 73).
- **Residual gaps** (feed into §5):
  - **G11** — Round‑trip is mechanised only for `ChainEpochDirection`. `Chain::into_pb` /
    `from_pb` are `#[hax_lib::opaque]`, so a `Chain`‑level `corrupted_chain_roundtrips`
    theorem needs the manual case‑split style of Phase 7; `Authenticator` and
    `PolyDecoder` round‑trip theorems are straightforward (`into_pb_spec`/`from_pb_spec`
    already exist for both) but absent.
  - **G12** — No statement (Lean or prose) of the `Ok`‑path re‑persistence in sense 3.
    `Key.lean`'s forward‑path spec should imply `prev.data.length % 36` is *preserved*
    (adds are 36 bytes); stating that as a corollary would formalise "misalignment is
    invariant under successful `key`".
  - **G13** — §12.1/§13 attribute the crash loop to SPQR ("no graceful recovery path *inside
    SPQR*") without separating host‑policy reload (sense 1) from SPQR re‑serialisation
    (senses 2–3). §2.1 and `docs/evaluate.md` Q7 already establish the host behaviour; §13
    should cite them and add senses 2–3.
  - **G14** — No executable round‑trip evidence in the report (§14.6 test #1 is a
    *valid*‑state regression proptest, not a corrupted‑state witness). Supplied here.

---

## 4. Assessment of the Q2 Answer

### 4.1. Strengths

1. **Every invariant is traced to a concrete requirement site** — a Lean hypothesis name
   (`h_next_len`, `h_data_aligned`, `h_key_ge`, `h_prev_ctr`, `h_ctr_bound`), a
   `hax_lib::requires`/`assume!`, or a runtime `assert!` — with file:line references that
   this evaluation confirmed against `src/chain.rs` and `Spqr/Specs/Chain/**`.
2. **Failure modes are correctly classified and not over‑claimed.** `links.is_empty()` and
   `send_epoch > current_epoch` are reported as graceful `Err(EpochOutOfRange)`, not panics;
   `next_root` is reported as *no panic but silent divergence at the Signal layer*.
3. **The position‑dependent `send.next` invariant (I9)** is the subtlest one — a naive
   `next.len() == 32` check in `ChainEpochDirection::from_pb` would reject *valid* states
   (cleared pre‑send‑epoch `send` directions). The report identifies the asymmetry, explains
   why the strong check must live in `Chain::from_pb`, and gives a `send_idx` computation
   that mirrors `epoch_idx` (`chain.rs:372‑382`).
4. **The primary set I1–I3 is mechanised end‑to‑end**: `from_pb pb = Ok ced` →
   `recv_key` has no `ok` result (Phases 1–5, 9–10), and `recvKeyPre` in
   `Spqr/Specs/Chain/Chain/Defs.lean:95‑106` is exactly the conjunction of I1–I5, I10, I12
   — so the report's list matches the formal precondition the proofs actually need.
5. **`h_ooo_no_overflow` (I12) is deliberately excluded** with the correct justification
   that `index` is message‑derived — the report distinguishes blob invariants from message
   invariants.

### 4.2. Weaknesses / residual gaps

| Gap | Detail | Impact on Q2 |
|---|---|---|
| G1 | **I4 (`h_ctr_bound`) is listed in §10.2 but never analysed.** `ctr` is copied verbatim; a blob with `ctr = u32::MAX − 5` reaches `self.ctr + max_ooo_keys` at `chain.rs:265` under an `assume!`, not a check. Debug build: panic; release: wrap and the `at > ctr + max_ooo` branch takes the wrong arm. §13 blast radius, §14.1 fix and §15 summary omit it. | One violable invariant is under‑reported; low practical severity in normal use, but a corrupted blob can set `ctr` directly. |
| G2 | **I7, I8, I9, I10, I11 rest on prose only** (report is candid — §7 "Not mechanised"). I9 is the highest‑value unproved claim because it is a *panic*. | Correctness verified here by code reading; evidence weaker than for I1–I3. |
| G3 | **I15 consequence is mis‑stated.** §9 groups the slot‑size bound with "silent stall", but `decoded_message` slices `&pts[..necessary_points(i)]` (`polynomial.rs:922`) so excess points are ignored. Real consequence: memory / `into_pb` size only. | Minor over‑claim in the severity column; the "violable" verdict stands. |
| G4 | **`h_maxooo_bound`/`h_ooo` (I10) is a Lean hypothesis** in `Key.lean`, `Gc.lean` and `recvKeyPre`, yet the §10.2 table omits it while listing `h_ctr_bound`. §7 covers it from the Rust side. | Presentation inconsistency only. |
| G5 | **No runtime Rust reproduction** — no `#[test]` in `src/chain.rs` builds a corrupted `pb`; `docs/corrupted_blob_counterexample.rs.txt` (recommended in §14.6) does not exist. | Lean model ≠ compiled binary; a concrete panic trace would make Q2 bullet‑proof. |
| G6 | No single **"invariant → fix that establishes it"** table. §14.5 covers I1–I3; I4 has no fix; I10/I11 are in §14.1a; I9 in §14.2. | Traceability incomplete. |

---

## 5. Execution Plan to Close the Q2, Q4 and Q5 Gaps

Ordered by value‑per‑effort. Steps 1–5 address Q2/Q4 (G1–G10); Step 6 addresses Q5
(G11–G14) and is independent of the others.

### Step 1 — Docs corrections: `ctr` row, I15 severity, I10 hypothesis, traceability (closes G1, G3, G4, G6) — ~1 h

1. `CorruptedBlobs.md` §3 table: add a row
   `ctr ≤ u32::MAX − 390451572` | `key()` (`chain.rs:262‑265`) | `Key.lean`: `h_ctr_bound` |
   **debug‑panic / release‑wrap**.
2. §14.1: add `if pb.ctr > u32::MAX - 390451572 { return Err(Error::StateDecode); }`
   (the constant already `assume!`d at `chain.rs:263`; use `108458770` if 32‑bit targets
   must be covered, per `Key32.lean`).
3. §10.2 table: add `h_maxooo_bound` (`Key.lean:63,197`) / `h_ooo` (`Gc.lean:797,833`).
4. §9: reword the slot‑size bullet — consequence is excess memory and `into_pb` size, not
   stall; cite `polynomial.rs:922`.
5. End of §14: add an "Invariant → Fix" traceability table using the I1–I15 numbering.


### Step 2 — Runtime Rust repro for each panic‑class invariant (closes G5) — ~2 h, **partially done**

**Status**: I1, I2, I3, I9 and the full `spqr::recv` path were executed during this
evaluation (§3A.3); the source is in `docs/corrupted_blob_counterexample.rs.txt`. Remaining
work: (a) commit them as permanent tests in `src/chain.rs` (they are currently *not* in the
tree), (b) add the I4 / I10 debug‑overflow probes below, (c) add a `spqr::send`‑level probe
mirroring `q3_probe_top_level_recv_reaches_panic` for the I9 route, and (d) reference
§3A.3 from `CorruptedBlobs.md` §4–§7 and §14.6.

Add to the existing `#[cfg(test)] mod test` in `src/chain.rs` (already imports
`Direction`, `Error`, `proptest`) one test per panic‑class invariant, following:

```rust
#[test]
fn corrupted_blob_recv_next_wrong_length_panics() {                    // I1
    let chain = Chain::new(b"1", Direction::A2B, ChainParams::default().into_pb()).unwrap();
    let mut pb = chain.into_pb();
    pb.links[0].recv.as_mut().unwrap().next = vec![0u8; 31];
    let mut c = Chain::from_pb(pb).expect("from_pb accepts the corrupted blob");
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c.recv_key(0, 1)));
    assert!(r.is_err(), "expected panic at chain.rs:243 (copy_from_slice)");
}
```

| Test | Mutation on `pb` | Call | Expected panic site |
|---|---|---|---|
| I1 | `recv.next = vec![0; 31]` | `recv_key(0, 1)` | `chain.rs:243` |
| I2 | `recv.prev = vec![0; 37]`, `recv.ctr = 5` | `recv_key(0, 1)` (`at < ctr`) | `chain.rs:191` |
| I3 | `recv.ctr = 0`, `recv.prev = vec![0; 36 * 2201]` | `recv_key(0, 1)` | `chain.rs:149` |
| I9 | drive `send_key`/`add_epoch` so `send_idx ≥ 1`, then `links[send_idx].send.next = vec![]` | `send_key(current_epoch)` | `chain.rs:229` |
| I4 | `recv.ctr = u32::MAX - 1` | `recv_key(0, u32::MAX)` | **debug only**: `chain.rs:265` overflow; release: `Ok` (confirmed, §3B.3 probe 3) — gate with `#[cfg(debug_assertions)]` |
| I10 | `params.max_ooo_keys = u32::MAX` **and** `recv.ctr ≥ 1` | `recv_key(0, ctr+1)` | debug only: `chain.rs:265`. With `ctr = 0` there is **no** overflow (§3B.3 probe 4) — the earlier "`chain.rs:87`" guess is wrong, `trim_size` is `usize` arithmetic |
| I2′ (new, G7) | `recv.ctr = 5000`, `recv.prev = vec![0; 36 * 2201 + 1]` | `recv_key(0, 5001)` (forward path) | `chain.rs:157` slice index in `gc` (confirmed, §3B.3 probe 2) |
| I7 (graceful) | `send_epoch = 7` | `send_key(7)` | **no panic**: `Err(EpochOutOfRange(7))` — keep as a positive assertion that this case is recoverable (§3B.3 probe 5) |

Commit pre‑fix copies as `docs/corrupted_blob_counterexample.rs.txt` (repo convention, cf.
`docs/*_counterexample.rs.txt`). Run `cargo test corrupted_blob` in **both** profiles
(`cargo test` and `cargo test --release`) so the debug/release divergence of I4 is exercised.

### Step 2a — Q4 documentation fixes in `CorruptedBlobs.md` (closes G7–G10) — ~1 h

1. **§5 / §6 (G7)**: add "Panic Path 2b: `KeyHistory::gc` slice index (`chain.rs:157`)" —
   misaligned `prev` reaches `gc` on the forward path (`at > ctr`) where there is *no*
   alignment assert; the `self.data[i..i + 4]` slice panics with `range end index … out of
   range`. Add `:157` to the §14.6 list of sites to convert (`L149, L157, L191, L229, L243`).
2. **§7 / §14.1a (G8)**: for the `max_ooo_keys` and `ctr` rows, replace "overflows … causing
   incorrect GC" with the two‑profile statement: *debug/test builds panic at `:265`/`:279`
   (`attempt to add with overflow`); release builds (no `overflow-checks` in `Cargo.toml`)
   wrap and return `Ok` with a wrong `prev.clear()`/`add` decision*. Note that the overflow
   requires `ctr + max_ooo > u32::MAX`, so `max_ooo_keys = u32::MAX` alone with `ctr = 0` does
   not trigger it.
3. **§12.1 / §13 (G9)**: state the panic site per mutation — `next = []` → `:229`
   (`assert!`), `next.len() ∉ {0, 32}` → `:243` (`copy_from_slice`).
4. **§13 (G10)**: reword "Failures are `panic!`/`assert!` crashes, not `Err` returns" to
   "Failures on the §4–§6 paths are panics …; the §7 epoch‑ordering cases return
   `Err(EpochOutOfRange)` and the `next_root`/`Authenticator`/`PolyDecoder` cases return
   `Ok` with wrong semantics".
5. **§14.6**: add that `KeyHistory::gc` also needs a `data.len() % 36 == 0` guard (or a
   `Result` return) before its loop, otherwise §14.6's `get` conversion is incomplete.
6. Optionally add a §4–§6 "Failure‑mode taxonomy" table with columns
   *Panic (both profiles) / Panic (debug only) / `Err` / `Ok`‑but‑wrong*, populated from
   §3B.2 of this evaluation.

### Step 3 — Mechanise I9, I7, I8 (closes the panic part of G2) — ~half a day

Extend `Spqr/Specs/Bugs/CorruptedBlobs.lean` with a Phase 11, reusing the Phase 7 pattern
(case‑split on the Aeneas `?` early‑return arms of `Chain.from_pb`):

1. `chain_from_pb_admits_empty_send_next_at_send_idx` — `Chain.from_pb pb = ok (Ok c)` with
   `links[send_idx].send.next = []` survives; compose with `next_key_internal_never_ok` via
   `send_key` (mirror of Phase 10's `recv_key_never_ok_of_key_never_ok`, using the
   `h_target` shape from `Spqr/Specs/Chain/Chain/SendKey.lean:360‑363`).
2. `chain_from_pb_admits_epoch_inversion` — `pb.send_epoch > pb.current_epoch` survives,
   plus `epoch_idx … = ok (Err (EpochOutOfRange _))` confirming the graceful stall (I7).
   Same shape for `current_epoch − send_epoch ≥ links.length` (I8).

### Step 4 — Mechanise I4, I10, I11 (closes the rest of G2) — ~2 h

`chain_from_pb_admits_params_out_of_range : Chain.from_pb pb = ok (Ok c) → c.params = params`
and `from_pb_admits_large_ctr : from_pb pb = ok (Ok ced) → ced.ctr = pb.ctr` are immediate
from `from_pb_never_fails`; their value is documenting that the `assume!` bounds at
`chain.rs:86, 262‑264, 280‑283` are *unestablished hypotheses*. Because Aeneas models `U32`
addition as failing on overflow, the debug‑build panic is expressible directly: prove
`key_never_ok_of_large_ctr` for `ctr.val + maxOoo > U32.max` (the `ctr + max_ooo_keys` step
at `chain.rs:265` has no `ok` result).

### Step 5 — (Optional) Apply the §14 fixes and flip the oracle — ~1 day

Implement §14.1 (+ the `ctr` bound from Step 1), §14.1a, §14.2, §14.3, §14.4. Then, per
§14.5, retarget the negative theorems as positive `from_pb pb = ok (Err StateDecode)`
theorems and flip the Step‑2 tests to
`assert!(matches!(Chain::from_pb(pb), Err(Error::StateDecode)))`. The clean formal statement
of "no §3 invariant can be violated by an `Ok` state" is then: every blob‑derived conjunct
of `recvKeyPre` (`Defs.lean:95‑106`, i.e. all but the `index`‑dependent I12 and I5's
`index` term) is a provable **postcondition** of `Chain::from_pb`.

### Step 6 — Close the Q5 gaps (G11–G14) — ~half a day total

**6a. Docs (`CorruptedBlobs.md`) — ~1 h, closes G13, G14**

1. §13 "Availability" bullet: split the crash‑loop claim into the three senses of §3C.4 —
   (1) host reloads the unchanged blob after a panic (cite §2.1 / `docs/evaluate.md` Q7);
   (2) `into_pb ∘ from_pb = id` at every layer (cite Phase 5 + the new theorems from 6c);
   (3) a corrupted blob can be *re‑persisted by a successful call* (cite the probes from 6b).
2. §12.3 (one‑byte alignment DoS): add the latent‑corruption observation — in‑order traffic
   succeeds and re‑persists the misalignment (37 → 73 → …); the panic fires on the first
   out‑of‑order message or, via `:157`, once `prev` reaches the GC threshold.
3. §14.6 recommended tests: add a **corrupted‑state** round‑trip test alongside the existing
   valid‑state proptest, and a "re‑persisted‑after‑`Ok`" test (probe 3 of §3C.3). After the
   §14 fixes land, both flip to `assert!(matches!(Chain::from_pb(pb), Err(Error::StateDecode)))`.

**6b. Permanent Rust tests — ~1 h, closes G14**

Promote the four `q5_probe_*` tests from `docs/corrupted_blob_counterexample.rs.txt` into
`src/chain.rs`'s `#[cfg(test)] mod test` next to the Step‑2 tests, under a
`corrupted_blob_roundtrip_*` naming scheme; keep the `catch_unwind` on the final
out‑of‑order call until §14.6 removes the panic. Run in both profiles in CI
(`cargo test --lib` and `cargo test --release --lib`).

**6c. Lean — ~2–3 h, closes G11, G12**

Add a Phase 11 to `Spqr/Specs/Bugs/CorruptedBlobs.lean`:

1. `authenticator_corrupted_roundtrips` — `into_pb (from_pb pb) = pb` for any key lengths;
   both `Spqr/Specs/Authenticator/Serialize` specs already exist, so this is a two‑line
   `spec_mono` composition like Phase 5.
2. `poly_decoder_corrupted_roundtrips` — for `pb.pts.length = 16`, all slots `% 4 = 0`,
   `pb.polys = 16`: `from_pb pb = Ok d → into_pb d ⦃ pb' => pb'.is_complete = pb.is_complete ∧
   pb'.pts_needed = pb.pts_needed ∧ pb'.pts = pb.pts ⦄`. Reuse
   `PolyDecoder/FromPb.lean` + `IntoPb.lean` (`into_pb_spec`); the `pts` equality needs the
   `Pt.serialize ∘ Pt.deserialize = id` lemma on 4‑byte groups and the no‑duplicate‑`x`
   side condition (state it as a hypothesis; the duplicate case is the documented
   normalisation exception of §3C.2).
3. `chain_corrupted_roundtrips` — `Chain.from_pb pb = ok (Ok c) → Chain.into_pb c = ok pb`.
   Both functions are `#[hax_lib::opaque]`, so follow Phase 7's manual case‑split on the
   Aeneas `?` arms; the `links` component reduces to `List.map` over Phase 5.
4. `key_preserves_prev_misalignment` (G12) — from `Key.lean`'s forward‑path spec: if
   `at > ctr`, `at ≤ ctr + maxOoo` and `prev.data.length < trim_threshold` then
   `key … = ok (Ok (k, self'))` with `self'.prev.data.length % 36 = self.prev.data.length % 36`.
   This is the formal statement of sense 3 in §3C.4 and complements
   `key_never_ok_of_misaligned_prev` (which covers the out‑of‑order path).

---

## 6. Conclusion

- **Questions requested**: 5. **Fully answered by the report**: 4 (Q1–Q4). **Partially
  answered**: 1 (Q5) — now closed empirically by this evaluation.
- **Q1: Yes** — all four `from_pb` variants accept protobuf‑valid, semantically invalid
  state (machine‑checked for each function).
- **Q3: Yes** — an invalid `Ok` state reaches `key`, `get` and `gc` through `Chain::recv_key`
  on every post‑first‑message `spqr::recv()`, and reaches `next_key_internal` through
  `Chain::send_key` on every `spqr::send()`. Established by call‑chain reading (§3A.1), Lean
  Phases 3/4/9/10 (§3A.2), and five compiled probes that panicked at `chain.rs:243`, `:191`,
  `:149`, `:229` — including one through the public `spqr::recv` API (§3A.3). The only
  Q3 gap in the report itself is the lack of an executable repro and the prose‑only
  `send_key` route; both are now evidenced here and should be merged back (Step 2).
- **Q2: Answered** — the report identifies 13 distinct violable invariants across
  `ChainEpochDirection` (I1–I4), `Chain` (I6–I11), `Authenticator` (I13) and `PolyDecoder`
  (I14–I15), correctly excludes two non‑blob conditions (I12, I16), and classifies each by
  failure mode. Nine have Lean witnesses; I1–I3 are proved end‑to‑end to a `recv_key`
  panic. Residual gaps: (a) the `ctr` range (I4) is named but not analysed or fixed,
  (b) I7–I11 are prose‑only, (c) the I15 "stall" consequence is over‑stated, and (d) there
  is no compiled‑Rust reproduction.
- **Q4: Yes** — for every panic‑class invariant (I1, I2, I3, I9) the downstream operation
  aborts via `assert!`/`assert_eq!`/slice‑length panic rather than returning `Err`;
  `next_key_internal` and `gc` have no `Result` channel at all. Established by source
  reading (§4–§6), by the `∀ r, … ≠ ok r` Lean theorems, and by ten compiled probes across
  debug and release (§3A.3, §3B.3). The report also correctly identifies the recoverable
  (`Err(EpochOutOfRange)`) and silent (`next_root`, `Authenticator`, `PolyDecoder`) cases.
  Residual gaps: (a) the `gc` slice‑index panic at `chain.rs:157` on misaligned `prev` is not
  listed (G7), (b) the I4/I10 overflow is a **debug‑only** panic and a release‑only silent
  wrap — the report says neither (G8), (c) §12.1/§13 conflate the `:229` and `:243` panic
  sites (G9), (d) §13's blanket "not `Err` returns" needs scoping (G10).
- **Q5: Yes (partially answered by the report; confirmed here)** — the report asserts a
  "crash loop on reload" (§1, §12.1, §13) and mechanises `into_pb (from_pb pb) = pb` for
  `ChainEpochDirection` only (Phase 5). This evaluation verified by source reading (§3C.2)
  and four compiled probes in debug and release (§3C.3) that **every** `from_pb`/`into_pb`
  pair — `ChainEpochDirection`, `Chain`, `Authenticator`, `PolyDecoder` — and the prost wire
  layer are the identity on all ten corruption classes of §3, so the same invalid state is
  restored verbatim on every load. Beyond the report, it showed that a corrupted blob can be
  **re‑persisted by a successful `spqr::recv()`** (misaligned `prev`: `Ok` returned, correct
  key derived, state written back still misaligned and growing 37 → 73 bytes) — a latent
  form of persistence that survives host‑side rollback and post‑corruption backups, and
  that the report does not distinguish from the host's reload‑after‑panic behaviour.
  Residual gaps: (a) round‑trip mechanised for one of four layers (G11), (b) no
  formal/prose statement of `Ok`‑path re‑persistence (G12), (c) §12.1/§13 conflate host
  reload with SPQR re‑serialisation (G13), (d) no executable round‑trip evidence in the
  report (G14; supplied in `docs/corrupted_blob_counterexample.rs.txt`).
- **Recommended next action**: Step 1 (docs corrections, ~1 h), Step 2a (Q4 taxonomy fixes,
  ~1 h), Step 6a (Q5 docs, ~1 h), then Steps 2 and 6b (permanent runtime repros in both
  profiles, ~3 h). Together they make the Q2, Q4 and Q5 answers complete and concretely
  evidenced; Steps 3, 4 and 6c then bring the Lean coverage up to the same level.

