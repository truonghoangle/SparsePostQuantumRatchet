# Do the Per-Function Lean Specs Compose to Preserve the Global SPQR State Invariants?

**Scope**: `Spqr/Specs/Chain/**`, `Spqr/Specs/Authenticator/**`, the top-level drivers in
`src/lib.rs` (`send`/`recv`), and the persistence layer (`*::from_pb`/`into_pb`).
**Method**: (1) extract the state invariants that the Rust code relies on (struct comments,
`assert!`s, `hax_lib::requires/assume!`); (2) read the hypotheses and postconditions of every
spec theorem that touches that state; (3) *mechanically* check inductiveness by proving, in a
scratch file that imports only the existing spec definitions, that each postcondition predicate
maps the invariant to itself; (4) check whether the invariant discharges the hypotheses of the
next call. The scratch file is
[`docs/invariants_composition_check.lean.txt`](./invariants_composition_check.lean.txt)
(0 errors, 0 `sorry`; run with
`cp docs/invariants_composition_check.lean.txt .tmp/X.lean && lake env lean .tmp/X.lean`).
**Date**: 2026‑09‑27.

---

## 0. Short answer

| Question | Answer |
|---|---|
| Do the **postconditions** of `new`, `add_epoch`, `send_key`, `recv_key` (and, one level down, `ChainEpochDirection.key`, `next_key`, `clear_next`, `KeyHistory.{add,get,gc}`) preserve a global chain invariant? | **Yes.** A global invariant `ChainInv` (§2) is established by `new_spec` and preserved by the postcondition predicates of `add_epoch_spec`, `sendKeyPost`, `recvKeyPost` — proved in the scratch file from the *postconditions alone*, without re-unfolding any Rust code. |
| Does that invariant **discharge the hypotheses** of the next call, closing the loop? | **Partly.** All *structural* hypotheses (`next.len = 32`, `prev.len % 36 = 0`, `prev.len ≤ 36·ctr`, deque well-formedness, index in range) are consequences of `ChainInv`. The *arithmetic* hypotheses (`ctr ≤ u32::MAX − 390 451 572`, `index + max_ooo ≤ u32::MAX`, `max_ooo < 390 451 572`, `ctr < u32::MAX`, `epoch_secret.epoch = current_epoch + 1`) are **not** state invariants and cannot be: they are fuel/parameter bounds that a peer can push the state out of. So the specs compose into an *inductive* argument only under a standing "counter has not approached 2³²" side condition. |
| Do they compose **across the persistence boundary** used by every public call (`decode_state → from_pb → op → into_pb → encode`)? | **No.** `ChainEpochDirection.from_pb_spec`/`Authenticator.from_pb` are proved to copy fields verbatim with no validation; `Chain.{from_pb,into_pb}` have no spec at all (blocked by the `sorryAx` map/collect bridge and the unsound `VecDeque::into_iter` model, `defects.md` §15/§20). The invariant is therefore preserved *inside* one `send`/`recv` call but is **not re‑established** on entry; `CorruptedBlobs.lean` proves that every violated conjunct is reachable and leads to a `fail .panic`. |
| Are there invariants the Rust code *claims* that the specs correctly **refuse** to compose? | **Yes** (§5): `prev.len ≤ 36·trim_size` (`hax_lib::requires` on `add`/`remove`) is false at run time and no spec assumes it; the specs use the honest weaker bound `prev.len ≤ 36·ctr`. Conversely, some *true* invariants (tag uniqueness in `prev`, tags `< ctr`, the at‑rest bound `prev.len < 36·trim_size`) are **not expressible** from the current postconditions and therefore do not compose. |

---

## 1. Inventory: what the Rust code assumes about its own state

Collected from `src/chain.rs`, `src/authenticator.rs`, `src/lib.rs`.

| # | Invariant | Where stated in Rust | Where consumed |
|---|---|---|---|
| I1 | `ChainEpochDirection.next.len() == 32` (except for send directions of epochs *before* the send epoch, where it is `0` after `clear_next`) | comment L101; `assume!` L273, L291, L403 | `next_key_internal` (`assert!(!next.is_empty())`, `copy_from_slice` panics if `≠ 32`) |
| I2 | `KeyHistory.data.len() % 36 == 0` | `assert_eq!` in `get` L191 | `get`, `gc`, `remove` |
| I3 | `KeyHistory.data.len() ≤ 36 · trim_size()` | comment L94; `requires` on `add` L138 / `remove` L174; `assume!` L281 | **false** (§5) |
| I3′ | *Honest replacement*: `prev.data.len() ≤ 36 · ctr` | nowhere in Rust — introduced by `Key.lean` (`h_prev_ctr`) to discharge `gc`'s `assert!(current_key ≥ max_ooo)` L149 | `gc` |
| I4 | `ctr ≤ u32::MAX − 390 451 572`, `max_ooo < 390 451 572` | `assume!` L262‑263, L275‑276 | overflow guard for `ctr + max_ooo` L265/L279 |
| I5 | `Chain.next_root.len() == 32` | comment L118 | `add_epoch` HKDF salt |
| I6 | `links.len() ≥ 1`, `send_epoch ≤ current_epoch`, `current_epoch − send_epoch < links.len()` | implicit in `new`, `epoch_idx`, `send_key` | `epoch_idx` (`links − 1 − back`), `send_key` indexing |
| I7 | Deque well-formedness: `head + length ≤ buf.len()` (growing-list model) | `FunsExternal.lean` VecDeque model | every `index_mut`/`pop_front` |
| I8 | `epoch_secret.epoch == current_epoch + 1` on `add_epoch` | `assume!` + `assert!` L352‑355 | `add_epoch` |
| I9 | `Authenticator.{root_key,mac_key}.len() == 32` | `new`/`update` construction | `mac_hdr`/`mac_ct` (HMAC key) |
| I10 | (cross-component) `msg.epoch − 1` used by `send`/`recv` in `lib.rs` is `≤ chain.current_epoch` and the chain was advanced exactly when the v1 state machine emitted an `EpochSecret` | none | `send_key`/`recv_key` error paths |

---

## 2. The candidate global invariant and the mechanised composition result

The scratch file defines (all names live in `spqr.chain`, built only on
`Spqr/Specs/Chain/Chain/Defs.lean`):

```lean
def CedInv (ced : ChainEpochDirection) : Prop :=
  ced.next.length = 32 ∧ ced.prev.data.length % 36 = 0 ∧ ced.prev.data.length ≤ 36 * ced.ctr.val

def sendIdx (c : Chain) : Nat := c.links.length - 1 - (c.current_epoch - c.send_epoch)

/-- `hs` = physical index of the send epoch; slots before it may have a cleared `send.next`. -/
def SlotInv (hs j : Nat) (ce : ChainEpoch) : Prop :=
  CedInv ce.recv ∧
  ce.send.prev.data.length % 36 = 0 ∧ ce.send.prev.data.length ≤ 36 * ce.send.ctr.val ∧
  (hs ≤ j → ce.send.next.length = 32)

def ChainInv (c : Chain) : Prop :=
  c.next_root.length = 32 ∧ 1 ≤ c.links.length ∧
  c.send_epoch ≤ c.current_epoch ∧ c.current_epoch - c.send_epoch < c.links.length ∧
  c.links.head + c.links.length = c.links.buf.length ∧
  ∀ j, head ≤ j → j < head + length → ∀ ce, buf[j]? = some ce → SlotInv (head + sendIdx c) j ce
```

This is I1 + I2 + I3′ + I5 + I6 + I7 with the *correct* refinement of I1 (send secrets before
the send epoch are legitimately empty — an invariant the Rust comment "next.len() == 32" gets
wrong and which `send_key_loop1_spec`'s `clearedAt` makes explicit).

### 2.1 Results (all machine-checked, 0 `sorry`)

| Theorem in scratch file | Statement | Uses only |
|---|---|---|
| `cedKeyPost_preserves_CedInv` | `CedInv self → cedKeyPost self ats params r self' → CedInv self'` | `cedKeyPost`, `cedKeyLessPost`, `cedKeyAdvancePost` (Defs.lean) |
| `recvKeyPost_preserves_ChainInv` | `ChainInv self → recvKeyPost self epoch index r self' → ChainInv self'` | `recvKeyPost`, `chainFrame`, `recvKeyEpochPost` + the lemma above |
| `sendKeyPost_preserves_ChainInv` | `ChainInv self → sendKeyPost self epoch r self' → ChainInv self'` | `sendKeyPost`, `sendKeyDequePost`, `sendKeySlotPost`, `clearedAt` |
| `addEpochPost_preserves_ChainInv` | `ChainInv self → ⟨postcondition of add_epoch_spec⟩ → ChainInv result` | the conjuncts of `add_epoch_spec` |
| `newPost_establishes_ChainInv` | `⟨postcondition of new_spec⟩ → ChainInv c` | the conjuncts of `new_spec` |
| `ChainInv_gives_send_key_structural` | `ChainInv self → h_wf ∧ (target slot has send.next.length = 32)` | — |
| `ChainInv_gives_recv_key_structural` | `ChainInv self → CedInv (target slot).recv` | — |

Observations from the proofs:

* **`send_key` is the only operation whose preservation argument is non-trivial**, because the
  send-epoch move both *pops* the front of the deque (shifting `head`) and *clears* `send.next`
  of the surviving earlier slots. The postcondition `sendKeyDequePost` is exactly strong enough:
  it gives (a) `head' = head + (idx − ei)`, `length' = length − (idx − ei)`; (b) `clearedAt` for
  `[head + (idx−ei), phys)` when the send epoch moved; (c) frame equality outside. The proof
  needs the fact `sendIdx self' = ei`, i.e. that after the move the new send epoch sits at
  logical index `ei = min idx 1`. That falls out of `sendKeyEi`/
  `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1`. If the postcondition had only said "some slots were
  cleared" (without the exact window), `SlotInv`'s `hs ≤ j → next.length = 32` conjunct would
  **not** have been re-establishable.
* **`recv_key` preserves the invariant on every path**, including the error paths, because
  `cedKeyPost` states `self' = self` for `KeyAlreadyRequested`/`KeyJump`, states `prev`
  unchanged for `KeyTrimmed`/`KeyAlreadyRequested`-from-`get`, and gives
  `length' = length − 36 ∧ % 36 = 0` on the `get` success path. The `≤ 36·ctr` conjunct survives
  `get` because `ctr` is unchanged and the length decreases; it survives advancement because
  `self'.ctr = ats` and `self'.prev.len ≤ khPreGc.len ≤ kh0.len + 36·(ats − ctr)` with
  `kh0.len ≤ prev.len ≤ 36·ctr`.
* **`add_epoch` is trivially inductive** provided I8 holds (the new slot has `ctr = 0`,
  `prev = []`, both `next`s of length 32). Note `add_epoch_spec` requires
  `h_buf : buf.length < Usize.max`; because the growing-list VecDeque model never shrinks `buf`
  (pop only moves `head`), `buf.length` grows monotonically over the run. This is a model
  artefact, not a Rust property, and is therefore *not* part of `ChainInv`; it is discharged per
  call as a fuel bound.
* The deque well-formedness conjunct had to be strengthened from `≤` (as in `chainFrame`) to `=`
  to make `add_epoch` inductive (the `push_back` model appends to `buf` and increments `length`
  by one, so `head + length = buf.length` is the actual invariant of the model). The weaker `≤`
  form is still what the top-level specs *consume*, so no spec needs restating.

### 2.2 What the composition therefore proves

For an **in-memory `Chain` value** produced by `Chain::new` and thereafter mutated only by
`add_epoch`/`send_key`/`recv_key` whose *arithmetic* side conditions hold (§3), every reachable
state satisfies `ChainInv`, and consequently no call in that sequence hits the `fail .panic`
paths of `next_key_internal` (`next.len ≠ 32`), `get` (`% 36`), `gc` (`current_key < max_ooo`),
`index_mut`/`pop_front` (deque bounds), or `epoch_idx` (`0 − 1`). This is a genuine *global*
safety result, and the fact that it can be proved **without unfolding any Rust code** — only
from `sendKeyPost`, `recvKeyPost`, `cedKeyPost`, `add_epoch_spec`, `new_spec` — is the strongest
evidence that the specs are stated at the right level of abstraction.

---

## 3. Hypotheses that do **not** compose (and cannot be turned into state invariants)

| Hypothesis (theorem) | Why it is not derivable from any state invariant | Consequence for composition |
|---|---|---|
| `h_at_bound : ats ≤ u32::MAX − 390 451 572`, `h_ctr_bound : self.ctr ≤ u32::MAX − 390 451 572` (`key_spec`) | `cedKeyAdvancePost` gives `self'.ctr = ats`; `ats` is the peer-chosen `index`. A malicious authenticated peer can raise `ctr` by ≤ `max_jump` per message until the bound fails. `CorruptedBlobs.lean` §16 (`ctr_steering_breaks_recvKeyPre`, `recvKeyPre_unsatisfiable_ctr_zone_z1/z3`) mechanises this. | Composition is valid only along traces with `ctr ∈ [0, u32::MAX − 390 451 572]`; beyond it no spec applies. The Rust threshold for actual misbehaviour is higher (`ctr + max_ooo > u32::MAX`, `q16b_*` probes) — the Lean bound is conservative slack, not a bug in the specs, but it is a **fuel** hypothesis, not an invariant. |
| `h_ooo_no_overflow : ats + max_ooo ≤ u32::MAX`, `h_maxooo_bound : max_ooo < 390 451 572` | `params` is user-configured and immutable; nothing in the state establishes it. `Chain.from_pb` copies `params` verbatim. | Must be a *precondition of the whole protocol run* (a well-formed-config assumption). The specs treat it uniformly, so it does compose as a standing assumption; it is "assumed once", not "preserved". |
| `h_ctr : ce.send.ctr < u32::MAX` (`send_key_spec`, `next_key_spec`) | `send_key` increments `ctr` unconditionally; after 2³² sends in one epoch the Rust `*ctr += 1` overflows (panic in debug, wrap in release). | Fuel bound. Derivable from `h_ctr_bound` when that holds. |
| `h_kh_cap : prev.len + 36·(ats − ctr) ≤ Usize.max` (`key_spec`) | **Is** derivable on 64‑bit from `CedInv`: `prev.len ≤ 36·ctr` so the sum is `≤ 36·ats ≤ 36·2³² ≪ 2⁶⁴`. On 32‑bit it is not. | Composes on the 64‑bit variants (`recvKeyPre` fixes `numBits = 64`); a genuine gap on 32‑bit, consistent with `defects.md` §3/§8. |
| `h_epoch : epoch_secret.epoch = current_epoch + 1` (`add_epoch_spec`) | This is I8/I10: a *cross-component* coupling between the v1 `States` machine's epoch counter and `Chain.current_epoch`. There is no Lean model of `States::send/recv` emitting an `EpochSecret`, and the driver `lib.rs::send/recv` has no spec. | The chain specs compose *given* I8; whether the protocol supplies it is unverified. The Rust `assert!` at L355 means a violation is a panic, not silent corruption. |
| `h_diff_fits : current_epoch − epoch ≤ Usize.max` | Trivial on 64‑bit (`SendKey64.lean`, `RecvKey32`/`64` split); a truncation hazard on 32‑bit (`defects.md` §3). | Composes on 64‑bit only. |

**Assessment.** None of these is a design flaw in the specs: they are exactly the
`hax_lib::assume!`s in the Rust code, made explicit. But the honest conclusion is that the
composed statement is
*"`ChainInv` is inductive for all traces in which every requested counter stays below
`u32::MAX − 390 451 572` and the configuration satisfies `max_ooo < 390 451 572`"*, not an
unconditional invariant.

---

## 4. The persistence boundary breaks the inductive chain

Every public entry point (`lib.rs::send`, `lib.rs::recv`) is
`decode_state → Chain::from_pb → {add_epoch; send_key | recv_key} → Chain::into_pb → encode`.
So the *real* composition is not `op ∘ op ∘ …` on one `Chain` value but
`into_pb ∘ op ∘ from_pb` repeated, with the invariant having to survive a round trip through
`pqrpb::Chain` each time.

| Function | Lean status | Effect on composition |
|---|---|---|
| `ChainEpochDirection::from_pb` | `from_pb_spec`: `Ok` with fields copied verbatim, never `Err`. `CorruptedBlobs.lean` Phase 1: `from_pb_admits_{wrong_next_length, misaligned_prev, large_prev_small_ctr, triple_violation}` | **Does not re-establish** I1, I2, I3′. Phases 3–4 (`key_never_ok_of_*`, `restore_then_recv_panics_*`, `recv_key_never_ok_*`) prove the composition `from_pb ; recv_key` has *no* successful execution on such inputs. |
| `ChainEpochDirection::into_pb` | `into_pb_spec` copies verbatim; `corrupted_state_roundtrips` (Phase 5) proves `into_pb ∘ from_pb = id` | Corruption is **persistent**: once an invalid blob exists it is faithfully re-emitted, so the inductive argument can never restart. |
| `Chain::from_pb` | **no spec** (uses the `sorryAx`-based `MapCollectBridge`); `chain_from_pb_admits_wrong_next_root` (Phase 7) proves the `next_root` case by hand | I5, I6 (`links ≥ 1`, `send_epoch ≤ current_epoch`) are not re-established; `defects.md` §21. |
| `Chain::into_pb` | **no spec**, and its `VecDeque::into_iter` model is unsound whenever `head ≠ 0` (`defects.md` §20) — which is exactly the state after any `send_key` that moved the send epoch | Even if `Chain::from_pb` were specified, the round trip cannot currently be proved to preserve *anything*, because the serialisation model emits already-popped epochs and drops the newest one. This is the single biggest obstacle to a whole-protocol invariant proof. |
| `Authenticator::from_pb` | `authenticator_from_pb_no_validation`, `*_admits_empty_mac_key/root_key/wrong_key_lengths` (Phase 6) | I9 not re-established; `new_spec`/`update_spec` do establish it (`root_key.length = 32 ∧ mac_key.length = 32`) and `mac_hdr_spec`/`verify_hdr_spec` only need `mac_key.length ≤ u32::MAX`, so in-memory composition holds; only the boundary is unguarded. |
| `PolyDecoder::from_pb` | `from_pb_spec` checks `pts.len = 16` and `% 4`; `poly_decoder_from_pb_admits_premature_is_complete/stalled_decoder` (Phase 8) | Decoder invariants (`is_complete` consistency, per-slot point bound) not re-established; `ProtocolDoS.lean` shows a poisoned decoder survives persistence. |

**Verdict for this question**: the specs compose into a global invariant for the *in-memory*
API, and the *same specs* prove — in the negative — that the global invariant is **not**
preserved across the persistence boundary, because the deserialisers' postconditions are
strictly weaker than the invariant (they say nothing about lengths, alignment, or ordering) and
nothing downstream re-checks. The gap is in the Rust code (missing validation), not in the
specs, but it means the answer to "do the specs compose to preserve global SPQR state
invariants" for the real protocol loop is **no** until `from_pb` validates or the driver is
proved to be the only writer of the blob.

---

## 5. Invariants claimed but *correctly not* composed, and true invariants that are *not expressible*

### 5.1 Claimed by Rust, refuted, and rightly absent from the specs

* **I3, `prev.len ≤ 36·trim_size`.** `defects.md` §10 and `key_history_bound_counterexample.py`
  show the history can reach `36·((trim_size − 1) + (max_ooo − 1))` before `gc` runs (≈ 2× the
  claim). No spec assumes it; `add_spec` needs only `len + 36 ≤ Usize.max`, `remove_spec` only
  `idx + 36 ≤ len`, `key_spec` uses `h_prev_ctr : prev.len ≤ 36·ctr`. Had a spec author taken the
  `hax_lib::requires` at face value, the composed invariant would have been *unsound* (vacuous
  on reachable states). This is a case where refusing to compose was the right call.
* **I1 as literally stated** ("`next.len() == 32`") is false for send directions of epochs
  before the send epoch after `send_key` moves it. `clear_next_spec` and `send_key_loop1_spec`
  make the correct refinement explicit; `ChainInv` encodes it via `hs ≤ j → …`. Composition
  with the literal I1 would fail at `sendKeyPost_preserves_ChainInv`.

### 5.2 True invariants the current postconditions cannot express (so they do not compose)

| Invariant | Why it is true in Rust | Why it does not compose today |
|---|---|---|
| At-rest bound `prev.len < 36·trim_size` (after every `key` call) | `gc` runs whenever `≥`; afterwards only records with tag `≥ ctr − max_ooo` survive, and there are at most `max_ooo` distinct such tags | `GcPost` gives liveness/completeness/injective provenance but **no cardinality bound**; deriving one needs *tag uniqueness* in `prev`, which no postcondition states. |
| Tag uniqueness: all 4-byte tags in `prev` are distinct | `add` is only called with fresh `ctr` values; `get` removes on first match | Not stated by `add_spec`/`cedKeyAdvancePost`; would need to be added to `CedInv` and threaded through `iterKeyHistoryData`. Without it, `get`'s "first match wins" semantics could return the wrong key for a duplicated tag — which `from_pb` can inject. |
| All tags in `prev` are `< ctr` (and `≥ ctr − max_ooo` after gc) | Same construction | Not stated; would let `KeyTrimmed`-vs-`KeyAlreadyRequested` be characterised semantically rather than by the raw `lexCmp` test, and would expose the off-by-one between `gc` (`>`) and `get` (`<` with post-increment ctr) noted in `defects.md` §10. |
| Slots strictly before the send epoch have `send.next = []` exactly (not merely "not required to be 32") | `send_key_loop1` clears exactly `[0, ei)` | `ChainInv` only needs the implication direction, so the weaker form was chosen; the stronger equality *is* derivable from `clearedAt` and would compose. |
| Cross-component I10 (`States` epoch ↔ `Chain.current_epoch`) | `send`/`recv` in `lib.rs` add an epoch exactly when the KEM state machine yields a secret | No Lean spec exists for `lib.rs::send/recv` or for `v1::chunked::States::{send,recv}` (only their `from_pb`/`into_pb`/`serialize` helpers). This is the largest *unmodelled* piece of global state. |

---

## 6. Answer, by component

| Component | Establishes | Preserves (in memory) | Preserves across `from_pb` | Composes? |
|---|---|---|---|---|
| `KeyHistory` (`add`/`remove`/`get`/`gc`) | `new` (`len = 0`) | I2 ✔ (all four specs), I3′ ✔ (`get`/`gc` shrink, `add` +36 only when `ctr` advanced) | n/a (never deserialised directly) | ✔ |
| `ChainEpochDirection` (`new`/`next_key`/`key`/`clear_next`) | `new` (`ctr = 0`, `prev = []`, `next = k`) | `CedInv` ✔ (`cedKeyPost_preserves_CedInv`); `next_key_spec` keeps `next.length`, `prev`; `clear_next_spec` keeps `ctr`, `prev` | ✘ (`from_pb_spec` = verbatim copy) | ✔ in memory, ✘ at boundary |
| `Chain` (`new`/`add_epoch`/`send_key`/`recv_key`/`epoch_idx`) | `new_spec` ⇒ `ChainInv` ✔ | `ChainInv` ✔ (three preservation theorems) | ✘ (no spec; `next_root`, `links ≥ 1`, epoch ordering unchecked) | ✔ in memory under §3 side conditions, ✘ at boundary |
| `Authenticator` | `new_spec` (32/32) | `update_spec` (32/32) ✔; `mac_*`/`verify_*` read-only | ✘ (no validation) | ✔ / ✘ |
| `PolyDecoder`/`Decoder` | `new` | `add_chunk` specs are per-call; poison persists (`ProtocolDoS.lean`) | ✘ | partial |
| `lib.rs::send/recv`, `States::send/recv` | — | **no specs** | — | unmodelled |

---

## 7. What would close the gaps

1. **Promote `ChainInv`/`CedInv` from the scratch file into `Spqr/Specs/Chain/Chain/Defs.lean`**
   and restate `send_key_spec`/`recv_key_spec` with `h_inv : ChainInv self` in place of `h_wf` +
   the structural half of `h_target`, keeping only the arithmetic hypotheses of §3 explicit. The
   preservation theorems then become reusable corollaries and any future driver spec can thread
   a single hypothesis.
2. **Give `Chain::from_pb` a spec** of the form "either `Err StateDecode` or `Ok c` with `c`
   equal to the field-wise decode" and then prove `¬ChainInv c` is *reachable* (the
   `CorruptedBlobs` style) — the formal statement that composition fails there — or, after the
   Rust fix in `CorruptedBlobs.md` §16, prove `Ok c → ChainInv c`.
3. **Fix the `VecDeque::into_iter` model** (`defects.md` §20) before attempting any
   `into_pb ∘ from_pb` round-trip theorem; without it the composed statement would be about the
   wrong list of epochs.
4. **Add tag uniqueness / tag-window conjuncts** to `cedKeyAdvancePost` (via a strengthened
   `iterKeyHistoryData` characterisation) so the at-rest bound and the `gc`/`get` window
   semantics can be composed.
5. **Model I8/I10**: a spec for `v1::chunked::States::{send,recv}` stating
   `epoch_secret.epoch = last_emitted_epoch + 1` together with a spec for `lib.rs::send/recv`
   is required for `add_epoch_spec`'s `h_epoch` to be discharged rather than assumed.

---

## Appendix A. Rust invariant → composition status

| Rust invariant | Lean conjunct | Established by | Preserved by | Discharges hypothesis of | Boundary |
|---|---|---|---|---|---|
| I1 (refined) | `SlotInv.4`, `CedInv.1` | `new_spec`, `add_epoch_spec` | `sendKeyPost` (`sendKeySlotPost.next.length`, `clearedAt`), `recvKeyPost` (`cedKeyPost.next`) | `next_key_spec.h_next_len`, `key_spec.h_next_len`, `send_key_spec.h_target` | ✘ `from_pb` |
| I2 | `CedInv.2`, `SlotInv.2` | `new`, `add_epoch` (`len = 0`) | `cedKeyLessPost` (`−36`, `% 36`), `cedKeyAdvancePost` (`% 36`) | `key_spec.h_prev_aligned`, `get_spec.h_data_aligned`, `gc_spec.h_data_aligned` | ✘ |
| I3′ | `CedInv.3`, `SlotInv.3` | `new`, `add_epoch` | `cedKeyLessPost` (ctr fixed, len ↓), `cedKeyAdvancePost` (`len' ≤ kh0 + 36·(ats−ctr)`, `ctr' = ats`) | `key_spec.h_prev_ctr` (⇒ `gc_spec.h_key_ge`) | ✘ |
| I4 | — | — | — (fuel) | `key_spec.h_ctr_bound/h_at_bound` | — |
| I5 | `ChainInv.1` | `new_spec` | `add_epoch_spec` (`next_root.length = 32`), frames | (HKDF salt; no Lean hypothesis) | ✘ |
| I6 | `ChainInv.2–4` | `new_spec` | `add_epoch` (both +1), `sendKeyPost` (`send_epoch' = epoch ≤ current`, `sendIdx' = ei < length'`), frames | `epoch_idx_spec` in-range branch | ✘ |
| I7 | `ChainInv.5` | `new_spec` | `push_back`/`pop_front`/`index_mut` models via the three chain posts | `h_wf` of `send_key_spec`/`recv_key_spec` | ✘ (not even modelled) |
| I8 | — | — | — | `add_epoch_spec.h_epoch` | unmodelled |
| I9 | (32/32) | `Authenticator.new_spec` | `update_spec` | `mac_hdr_spec.h_key` | ✘ |

## Appendix B. Library modules (`Spqr/Specs/Invariants/`)

The scratch results have been promoted into the library (all `@[step]`-free, 0 `sorry`, built
as part of `lake build Spqr`):

| Module | Contents |
|---|---|
| `Invariants/Defs.lean` | `CedInv`, `sendIdx`, `SlotInv`, `ChainInv`, `CedCtrBound`, `ParamsBound`, `ChainInv.wf`, `recvKeyPre_of_cedInv` |
| `Invariants/ChainEpochDirection/Key.lean` | `cedKeyPost_preserves_cedInv`, `key_spec_cedInv` |
| `Invariants/ChainEpochDirection/FromPb.lean` | `PbCedInv`, `cedInv_from_pb_iff`, `from_pb_not_cedInv`, `into_pb_preserves_pbCedInv`, `into_pb_not_pbCedInv` (the persistence-boundary **negative** result) |
| `Invariants/Chain/New.lean` | `chainInv_of_newPost`, `new_spec_chainInv` |
| `Invariants/Chain/AddEpoch.lean` | `chainInv_of_addEpochPost`, `add_epoch_spec_chainInv` |
| `Invariants/Chain/SendKey.lean` | `sendKeyPost_preserves_chainInv`, `sendNext_of_chainInv`, `send_key_spec_chainInv` |
| `Invariants/Chain/RecvKey.lean` | `recvKeyPost_preserves_chainInv`, `cedInv_recv_of_chainInv`, `recv_key_spec_chainInv` |
| `Invariants/Chain/Composition.lean` | `sendStep`/`recvStep` (the chain-side effect of `lib.rs::send`/`recv`), `AddEpochPre`, `sendStep_chainInv`, `recvStep_chainInv`, the trace relation `ChainStep`/`Reachable`, and the soundness theorem `chainInv_of_reachable` |

## Appendix C. How to re-run the original scratch check

```sh
cp docs/invariants_composition_check.lean.txt .tmp/InvCheck.lean
lake env lean .tmp/InvCheck.lean        # expected: no output (0 errors, 0 sorry)
```

The file imports only `Spqr.Specs.Chain.Chain.Defs` (which transitively brings in the
`KeyHistory`/`ChainEpochDirection` definitions); none of the spec theorems themselves are
needed, because the argument is carried entirely by the postcondition *predicates*
`cedKeyPost`, `recvKeyPost`, `sendKeyPost` and the stated conjuncts of `new_spec`/`add_epoch_spec`.
