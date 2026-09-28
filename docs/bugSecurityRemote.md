# Does any bug satisfy `SPQR bug: ✅ ∧ V1 security: ✅ ∧ Remote: ✅`?

**Question.** Does the project contain a bug / invariant violation that is simultaneously

1. an **SPQR bug** — the library violates one of its own internal invariants (Lean specs /
   `hax_lib` contracts / struct comments),
2. a **V1 security‑relevant robustness problem** — a security effect (DoS, key loss, crypto
   degradation) when exercised through the deployed V1 protocol in libsignal, and
3. **remotely exploitable** — triggerable by a *purely network‑only* attacker: no local storage
   access, no authenticated‑peer privilege (the attacker is **not** the session counterpart
   and holds no session key).

> **Document status.** Part I (§1–6) answers the question for a *forging* network attacker:
> **No**. Part II (§7–8) re‑asks it for a *non‑forging* (delay/reorder/replay/drop) network
> attacker. It surfaces one real SPQR robustness nit (epoch retention hard‑coded to 1 behind
> `send_epoch`; "future" and "evicted" epochs share one error), but on closer comparison with
> the Double Ratchet's own `MAX_RECEIVER_CHAINS = 5` window it is **not a Signal security
> bug**: the loss window is within one direction change of DR's, and a delaying network
> attacker can already drop messages outright. Final classification of the Part II finding:
> `SPQR bug ✅ (minor) / V1 security ❌ / Remote ✅`. **Overall answer remains: No.** See §8.

**Answer (Part I, forging attacker): No.** After an independent, from‑source investigation
(not relying on the prior `classificationBug.md` / `evaluateV1.md` conclusions), two genuine SPQR
invariant violations *are* reachable from the network without any credential, but in the
deployed V1 integration neither produces a security effect, because libsignal discards the
mutated SPQR state unless the outer Double‑Ratchet MAC verifies. The closest matches are
therefore `✅ / ❌ / ✅` (reachable but harmless) and `✅ / ✅ / ⚠️ authenticated peer`.

---

## 1. Method (independent of existing docs)

| Step | What was done | Where |
|---|---|---|
| 1 | Enumerated the only network‑facing SPQR entry point: `spqr::recv(state, msg)` | `src/lib.rs:356` |
| 2 | Read the wire parser and every `recv_*` state transition to find what an unauthenticated byte string can make SPQR do | `src/v1/chunked/states/serialize.rs:248`, `src/v1/chunked/states.rs:275`, `src/v1/chunked/{send_ct,send_ek}.rs`, `src/v1/unchunked/*` |
| 3 | Read the key‑chain code an attacker‑chosen `index` reaches | `src/chain.rs:247` (`ChainEpochDirection::key`) |
| 4 | Read the **actual libsignal integration** at the pinned commit (`a47ba487`, local checkout `../libsignal`) for the order of `spqr::recv` vs. MAC check and when state is committed | `rust/protocol/src/session_cipher.rs:424‑694`, `rust/protocol/src/state/session.rs:601‑621`, `rust/protocol/src/protocol.rs:86‑175` |
| 5 | Wrote and ran a fresh black‑box harness: 200 honest SPQR states × 200 forged messages each (random bytes, bit‑flips, truncation/extension, structured V1 headers with random chunks), plus a worst‑case `index = max_jump` probe | `docs/remote_attacker_harness.rs.txt` (run as `tests/…rs`; both tests pass) |
| 6 | Re‑ran the existing in‑tree probes `q16c_probe_*` for cross‑check | `src/lib.rs:1180‑1376` |

---

## 2. What a network‑only attacker can make SPQR do (empirical)

Harness output (`cargo test --release --test tmp_remote_fuzz -- --nocapture`):

```
states=200  ok=17379  err=22508  key_from_forgery=121  worst_recv=335µs
index=25000 -> ok=true in 13.7ms
index=40000 -> Some(KeyJump(1, 40000))
```

* **No panic** on any of 40 000 forged inputs. `Message::deserialize` bounds‑checks every
  varint and chunk (`serialize.rs:249‑277`), `decode_chunk` rejects `index > 65535`, and every
  `recv_*` arm returns `Err`/no‑op rather than asserting on attacker data.
* **Bounded CPU**: the worst single message (`index = max_jump = 25 000`) costs ≈ 10–14 ms of
  HKDF; `index > max_jump` is rejected with `KeyJump` (`chain.rs:250`).
* **Two state mutations occur without any authentication** (`key_from_forgery = 121` cases):

| # | Mutation | Code path | Invariant violated |
|---|---|---|---|
| R‑1 | **Epoch advance**: a 4‑byte message `[1, epoch+1, idx, 0]` (type `None`) moves `Ct2Sampled → KeysUnsampled` and bumps `uc.epoch`. | `states.rs:513‑526` → `send_ct.rs:295 recv_next_epoch` → `unchunked/send_ct.rs:201` — no `verify_*` call | "Epoch transitions are driven by authenticated SCKA messages" (the `Authenticator` is keyed per epoch, `authenticator.rs:44`, yet this transition never consults it) |
| R‑2 | **Chunk poisoning**: forged `Hdr`/`Ct1`/`Ek`/`Ct2` chunks are `add_chunk`‑ed into the `PolyDecoder` and returned in the new state; `verify_hdr`/`verify_ct` run only once the decoder is *complete*. | `send_ct.rs:92`, `send_ek.rs:137,204`; `polynomial.rs:879‑904` | "Decoder contents originate from the peer" — proved as `recv_hdr_chunk_persists_unauthenticated_state`, `Spqr/Specs/Bugs/ProtocolDoS.lean:156` |

Both are **real SPQR bugs (criterion 1 ✅)** and **reachable by a network‑only attacker
(criterion 3 ✅)**. The question is criterion 2.

---

## 3. Why criterion 2 fails for a network‑only attacker (libsignal `a47ba487`)

`decrypt_message_with_state` (`session_cipher.rs:599‑694`) runs, in order:

```rust
let chain_key       = get_or_create_chain_key(state, …)?;                       // L624
let message_key_gen = get_or_create_message_key(…, counter)?;                   // L625
let pqr_key = state.pq_ratchet_recv(ciphertext.pq_ratchet()).map_err(…)?;      // L633  ← spqr::recv, mutates `state`
let message_keys = message_key_gen.generate_keys(pqr_key);                      // L648
let mac_valid = ciphertext.verify_mac(their_ik, our_ik, message_keys.mac_key())?; // L657
if !mac_valid { return Err(InvalidMessage(…, "MAC verification failed")); }      // L663
```

and `decrypt_message_with_record` (`L454‑483`) calls it on a **clone**:

```rust
let mut current_state = current_state.clone();                                 // L455
match decrypt_message_with_state(&mut current_state, …) {
    Ok(ptext) => { record.set_session_state(current_state); return Ok(ptext); } // L475  commit
    Err(e)    => { /* clone dropped; previous sessions tried on their own clones */ }
}
```

Consequences for a network‑only attacker (no session keys):

1. **SPQR does run before the MAC** (L633 < L657), so R‑1/R‑2 *do* execute — but on a clone.
2. The attacker cannot make `verify_mac` succeed (needs the DR message key, derived from the DR
   chain key ⊕ `pqr_key`). The MAC covers the whole serialized `SignalMessage` **including
   the `pq_ratchet` field** (`protocol.rs:88‑110`), so forged SPQR bytes cannot be spliced into
   an honestly‑MACed message either.
3. Hence `Err` is returned and the mutated clone is **never committed**: the persisted
   `pq_ratchet_state` is byte‑identical afterwards. No epoch lost, no decoder poisoned, no key
   derived, no panic reachable. Cost to victim ≤ ~14 ms CPU per message
   (`q16c_probe_unauth_cpu_only_no_persist`), comparable to the DR key derivation the attacker
   forces anyway.
4. The **V0 downgrade** (`q16c_probe_peer_forces_v0_downgrade`, `lib.rs:1319`) also happens
   inside `spqr::recv` and likewise dies with the clone.

So for a network‑only attacker **criterion 2 ❌**. The invariant is not maintained by SPQR; it
is maintained by libsignal's *clone‑then‑commit‑after‑MAC* pattern.

---

## 4. Closest candidates and their true classification

| ID | Bug | SPQR bug | V1 security | Remote | Blocking factor |
|---|---|---|---|---|---|
| R‑1 | Unauthenticated `recv_next_epoch` epoch advance | ✅ | ❌ (state dropped) | ✅ reachable | libsignal commit‑after‑MAC |
| R‑2 | Unauthenticated chunk ingestion into `PolyDecoder` | ✅ | ❌ (state dropped) | ✅ reachable | libsignal commit‑after‑MAC |
| R‑3 | Forced V0 downgrade while negotiation open | ✅ | ❌ (state dropped) | ✅ reachable | libsignal commit‑after‑MAC |
| R‑4 | Forged `index ≤ max_jump` forces 25 000 HKDF iterations | ✅ (no rate limit in SPQR) | ❌ (≈10 ms, nothing persisted) | ✅ reachable | bounded by `KeyJump` |
| L4‑2 | R‑2 performed by the **authenticated peer** (MAC passes → poison persists → `MacVerifyFailed` stall) | ✅ | ✅ | ⚠️ auth peer only | needs session keys |
| L4‑1 | Peer steers chain counter toward the proof bound | ✅ | ✅ | ⚠️ auth peer only | needs session keys |
| L1‑x … L3‑x | `from_pb` panics / silent corruption / stall | ✅ | ✅ | ❌ | needs control of the persisted blob |

No row is `✅ / ✅ / ✅`.

---

## 5. Caveats and assumptions

* "V1 security" is evaluated against **libsignal `a47ba487`**, the checkout alongside this
  repo. Any host that persists the `spqr::recv` result **before** authenticating the envelope,
  or does not use clone‑and‑commit, would turn R‑1/R‑2/R‑3 into `✅ / ✅ / ✅`. SPQR's public
  API does not document that callers must do this — a robustness gap worth closing inside
  SPQR (e.g. accept the `epoch+1` transition only via an authenticated `Hdr` chunk, or gate
  `add_chunk` on a per‑chunk MAC).
* "Network‑only" excludes the legitimate peer. An attacker who *is* the peer (or holds its
  session) is the Level‑4 case: `⚠️`, not `✅`.
* The harness is black‑box and seeded (`0xC0FFEE`); it is evidence of no *found* panic, not a
  proof. Panic‑freedom of the parse path is separately covered by the `hax_lib::ensures`
  contracts on `Message::deserialize` / `decode_varint` / `decode_chunk`.

---

## 6. Conclusion

| Query | Result |
|---|---|
| ∃ bug with `SPQR bug ✅ ∧ V1 security ✅ ∧ Remote ✅` | **No — not found** |
| Reachable‑but‑harmless SPQR bugs for a network‑only attacker | R‑1, R‑2, R‑3, R‑4 (`✅ / ❌ / ✅`) |
| Why criterion 2 fails | libsignal runs `spqr::recv` on a **clone** and commits only after `verify_mac` succeeds (`session_cipher.rs:455, 475, 657`) |
| Nearest security‑relevant match | Level 4 (authenticated peer): `✅ / ✅ / ⚠️` |

---
---

# Part II — Same question, different angles

Part I asked "can a *forging* network attacker hurt SPQR?" and found the answer is no because
libsignal discards unauthenticated results. Part II re‑asks the question from angles where the
attacker **does not need to forge anything**, so libsignal's commit‑after‑MAC defence is
irrelevant by construction. Each angle was probed with a fresh executable harness
(`docs/dolev_yao_harness.rs.txt`, 6 tests, all pass).

| Angle | Re‑phrased question | Attacker capability |
|---|---|---|
| A | Can an attacker who can only **delay** one honest message make it permanently undecryptable? | Dolev‑Yao (delay) |
| B | Can **replay** of an honest message re‑derive a key or mutate state? | Dolev‑Yao (replay) |
| C | Can adversarial **reordering** (LIFO delivery) cause sender/receiver key disagreement or unbounded state growth? | Dolev‑Yao (reorder) |
| D | Is SPQR's epoch retention **shorter than the Double Ratchet's** chain retention, so a message DR would accept is refused by SPQR? | Dolev‑Yao (delay) |
| E | Can dropping **all replies** (monologue) exhaust a counter or blow up sender state? | Dolev‑Yao (drop) |

## 7. Results per angle

### A / D — Delay ⇒ permanent message loss  **(initially assessed `✅/✅/✅`; downgraded — see §8)**

`spqr::Chain` retains only `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1` epoch behind its
`send_epoch` (`chain.rs:125`, evicted in `send_key`, `chain.rs:391‑395`). libsignal's Double
Ratchet retains `MAX_RECEIVER_CHAINS = 5` receiver chains (`consts.rs:10`, `session.rs:346`).
Both windows are measured in direction changes, but SPQR's is shorter.

`spqr_epoch_retention_vs_dr_receiver_chain_retention` (k honest msgs/turn; one B→A message
held back; delivery retried after every direction change):

```
k=  5 msgs/turn: SPQR rejects delayed msg after 27 direction changes  EpochOutOfRange
k= 10 msgs/turn: SPQR rejects delayed msg after 21 direction changes  EpochOutOfRange
k= 20..80      : SPQR rejects delayed msg after  9 direction changes  EpochOutOfRange
```

`delay_across_epochs_loses_honest_message` / `reorder_transient_vs_permanent_loss`:

```
deliver at A epoch 2 : Ok(true)                       ← still decryptable
deliver at A epoch 3+: Err(EpochOutOfRange) forever
after catch‑up: recovered=0 permanent={"EpochOutOfRange": 108}
```

In libsignal (`session_cipher.rs:633‑647`) `EpochOutOfRange` → `InvalidMessage("post-quantum
ratchet error")`: the honest, correctly‑MACed message is **unrecoverably dropped**, although DR
alone would have decrypted it (receiver chain within the 5‑chain window, counter within
`MAX_MESSAGE_KEYS`). Not retried; indistinguishable from a forgery to the caller.

| Criterion | Verdict | Why |
|---|---|---|
| SPQR bug | ✅ (minor) | Retention hard‑coded to 1 epoch behind `send_epoch`, not aligned with the host's DR window; "future epoch" and "evicted epoch" share one `EpochOutOfRange`. |
| V1 security | ❌ | A delaying attacker can already drop the message; DR's own 5‑chain window evicts at ≈ the 10th direction change vs SPQR's 9th (heavy traffic) or later (light traffic). No confidentiality/authenticity/FS/PCS impact. See §8. |
| Remote | ✅ | Pure Dolev‑Yao delay; no keys, no storage, no forgery. |

Caveat: honest long delivery delays (offline devices) trigger the same loss without an
attacker — and equally trigger DR's own eviction, which is why this is not security‑relevant.
### B — Replay: **no bug**

`replay_is_idempotent_or_errors`: 300 replays → `bad_key=0 state_changed=0`, all
`KeyAlreadyRequested`. Chain‑level dedup (`chain.rs:257‑259`) is sound; libsignal's DR
duplicate check (`session_cipher.rs:742‑747`) fires first anyway.

### C — Adversarial reorder: **no key‑agreement bug; growth bounded**

`adversarial_reorder_key_agreement_and_state_growth`: 6 000 ticks of LIFO delivery →
`disagreements=0`, `max_state=7 733 B`. The only errors were 121 × `EpochOutOfRange` — the same
class as Angle A, confirming that eviction is the *only* reorder‑induced failure mode.

### E — Monologue / counter exhaustion: **no bug**

`monologue_chunk_index_exhaustion`: 70 000 consecutive `send`s with all replies dropped →
state flat at 3 892 B, ~4 µs/send, chunk index wraps `u16` at 65 536 without panic
(`wrapping_add`, `polynomial.rs:736`; `decode_chunk` still bounds it). The receiver rejects the
post‑wrap message with `KeyJump(0, 70000)` — expected, since `max_jump = 25 000` equals DR's
`MAX_FORWARD_JUMPS`; no DR/SPQR mismatch here.

## 8. Updated conclusion

| Query | Part I (forging attacker) | Part II (Dolev‑Yao attacker) |
|---|---|---|
| ∃ bug with `SPQR bug ✅ ∧ V1 security ✅ ∧ Remote ✅` | No | **No.** Angle A/D is `✅ (minor) / ❌ / ✅` |

**Is Angle A/D a Signal security bug? No**, for three reasons:

1. **No new attacker capability.** A network attacker able to *delay* a message can *drop*
   it. Signal gives no delivery guarantee against the network; confidentiality, authenticity,
   forward secrecy and PCS are untouched (the lost message is decrypted by nobody, both
   ratchets keep advancing).
2. **The window is not materially shorter than DR's.** libsignal evicts a receiver chain when
   `receiver_chains.len() > 5` (`session.rs:346`), i.e. after 5 further peer turns ≈ the 10th
   direction change. SPQR rejects at the 9th under heavy traffic (k ≥ 20) and *later* than DR
   under light traffic (27 at k=5, 21 at k=10, never at k=1). A device offline for 9–10
   turns loses the message to DR anyway.
3. **The remaining defect is ergonomic.** `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1` is a
   hard‑coded constant not aligned with the host's `MAX_RECEIVER_CHAINS`, and
   `EpochOutOfRange` conflates "future epoch" with "evicted epoch". Worth fixing (make the
   retention a `ChainParams` field; split the error) but not security‑relevant.

Net: across both the forging and non‑forging network‑attacker models, **no bug in this
repository is simultaneously an SPQR bug, a V1 security problem, and remotely exploitable.**

## References (Part II)

* `docs/dolev_yao_harness.rs.txt` — Part II harness (6 tests)
* `src/chain.rs:125, 384‑407` — `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`, eviction in `send_key`
* `src/chain.rs:371‑382` — `epoch_idx` → `EpochOutOfRange` for both future and evicted epochs
* libsignal `a47ba487`: `rust/protocol/src/consts.rs:8‑11`, `state/session.rs:332‑352`
  (receiver‑chain retention), `session_cipher.rs:633‑647` (error mapping), `742‑760` (DR dedup/jump)

## References (Part I)

* `src/lib.rs:356‑455` — `spqr::recv`; `src/lib.rs:1180‑1376` — `q16c_probe_*`


* `src/v1/chunked/states.rs:275‑533` — state‑machine `recv`
* `src/v1/chunked/send_ct.rs:82‑107, 294‑298`; `src/v1/chunked/send_ek.rs:129‑148, 193‑223`
* `src/v1/unchunked/send_ct.rs:100‑113, 201‑205`; `src/v1/unchunked/send_ek.rs:139‑172`
* `src/encoding/polynomial.rs:879‑904` — `PolyDecoder::add_chunk`
* `src/chain.rs:247‑296` — `ChainEpochDirection::key` (`max_jump` bound)
* `Spqr/Specs/Bugs/ProtocolDoS.lean:156` — `recv_hdr_chunk_persists_unauthenticated_state`
* libsignal `a47ba487`: `rust/protocol/src/session_cipher.rs:424‑694`,
  `rust/protocol/src/state/session.rs:601‑621`, `rust/protocol/src/protocol.rs:86‑175`,
  `rust/protocol/src/ratchet.rs:41‑51, 101‑109`
* `docs/remote_attacker_harness.rs.txt` — reproducible harness for §2

