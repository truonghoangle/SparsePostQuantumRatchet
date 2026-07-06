/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
-- send_ek sub-state serialisation specs
import Spqr.Specs.V1.Chunked.SendEk.Serialize.KeysUnsampled.IntoPb
import Spqr.Specs.V1.Chunked.SendEk.Serialize.KeysSampled.IntoPb
import Spqr.Specs.V1.Chunked.SendEk.Serialize.Ct1Received.IntoPb
import Spqr.Specs.V1.Chunked.SendEk.EkSentCt1Received.IntoPb
-- send_ct sub-state serialisation specs
import Spqr.Specs.V1.Chunked.SendCt.Serialize.NoHeaderReceived.IntoPb
import Spqr.Specs.V1.Chunked.SendCt.Serialize.HeaderReceived.IntoPb
import Spqr.Specs.V1.Chunked.SendCt.Serialize.Ct1Sampled.IntoPb
import Spqr.Specs.V1.Chunked.SendCt.Serialize.EkReceivedCt1Sampled.IntoPb
import Spqr.Specs.V1.Chunked.SendCt.Serialize.Ct1Acknowledged.IntoPb
import Spqr.Specs.V1.Chunked.SendCt.Serialize.Ct2Sampled.IntoPb
-- unchunked EkSent spec (used by the chunked HeaderSent.into_pb branch)
import Spqr.Specs.V1.Unchunked.SendEk.Serialize.EkSent.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb
/-!
# Spec theorem for `spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::States}::into_pb`

`States.into_pb` converts a `States` — the top-level V1 chunked protocol state machine enum — from
the in-memory Rust form (`v1.chunked.states.States`) into the protobuf form
(`proto.pq_ratchet.V1State`) used for network serialization or persistent storage.

The `States` enum has eleven variants, five belonging to the **send_ek** (encapsulation-key-sending)
side and six belonging to the **send_ct** (ciphertext-sending) side:

  **send_ek variants:**
  `KeysUnsampled`, `KeysSampled`, `HeaderSent`, `Ct1Received`, `EkSentCt1Received`

  **send_ct variants:**
  `NoHeaderReceived`, `HeaderReceived`, `Ct1Sampled`, `EkReceivedCt1Sampled`,
  `Ct1Acknowledged`, `Ct2Sampled`

The conversion performs a match on the `States` variant and delegates to the corresponding
sub-state's `into_pb` function:

- `KeysUnsampled`         → `v1.chunked.send_ek.serialize.KeysUnsampled.into_pb`
- `KeysSampled`           → `v1.chunked.send_ek.serialize.KeysSampled.into_pb`
- `HeaderSent`            → `v1.chunked.send_ek.serialize.HeaderSent.into_pb`
- `Ct1Received`           → `v1.chunked.send_ek.serialize.Ct1Received.into_pb`
- `EkSentCt1Received`     → `v1.chunked.send_ek.serialize.EkSentCt1Received.into_pb`
- `NoHeaderReceived`      → `v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb`
- `HeaderReceived`        → `v1.chunked.send_ct.serialize.HeaderReceived.into_pb`
- `Ct1Sampled`            → `v1.chunked.send_ct.serialize.Ct1Sampled.into_pb`
- `EkReceivedCt1Sampled`  → `v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb`
- `Ct1Acknowledged`       → `v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb`
- `Ct2Sampled`            → `v1.chunked.send_ct.serialize.Ct2Sampled.into_pb`

Each sub-state's `into_pb` serialises the variant's fields into its corresponding protobuf
type under the `proto.pq_ratchet.v1_state.InnerState` enum, and the result is wrapped in a
`proto.pq_ratchet.V1State` with `inner_state = some (InnerState.X ...)`.

The by-value `into_pb` introduces no additional logic beyond the dispatch and wrapping, so
the postconditions for each branch are inherited from the corresponding sub-state
specifications.  The reverse direction is `from_pb`; together the two functions let a value
round-trip between the in-memory and protobuf forms without losing information.

**Source**: spqr/src/v1/chunked/states/serialize.rs (lines 12:4-47:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize.States

/--
**Spec theorem for `v1.chunked.states.serialize.States.into_pb`**:

• Takes a `self : v1.chunked.states.States` — the top-level chunked V1 protocol state, which
  is one of the eleven variants spanning both the send_ek and send_ct sides.
• Pattern-matches on `self` and delegates to the appropriate sub-state's `into_pb`:
    - `KeysUnsampled state`       → `send_ek.serialize.KeysUnsampled.into_pb state`
    - `KeysSampled state`         → `send_ek.serialize.KeysSampled.into_pb state`
    - `HeaderSent state`          → `send_ek.serialize.HeaderSent.into_pb state`
    - `Ct1Received state`         → `send_ek.serialize.Ct1Received.into_pb state`
    - `EkSentCt1Received state`   → `send_ek.serialize.EkSentCt1Received.into_pb state`
    - `NoHeaderReceived state`    → `send_ct.serialize.NoHeaderReceived.into_pb state`
    - `HeaderReceived state`      → `send_ct.serialize.HeaderReceived.into_pb state`
    - `Ct1Sampled state`          → `send_ct.serialize.Ct1Sampled.into_pb state`
    - `EkReceivedCt1Sampled state`→ `send_ct.serialize.EkReceivedCt1Sampled.into_pb state`
    - `Ct1Acknowledged state`     → `send_ct.serialize.Ct1Acknowledged.into_pb state`
    - `Ct2Sampled state`          → `send_ct.serialize.Ct2Sampled.into_pb state`
• Each branch wraps the converted sub-state in the corresponding
  `proto.pq_ratchet.v1_state.InnerState` constructor and returns a `proto.pq_ratchet.V1State`
  with `inner_state = some (InnerState.X result)`.

• The function succeeds (no panic) when all sub-state `into_pb` calls succeed, i.e. when the
  serialization preconditions (polynomial encoder/decoder overflow bounds and cast bounds)
  hold for the specific variant. This is captured by the precondition
  `h_ok : ∃ r, into_pb self = ok r`.

The result satisfies the following postconditions:

  For each variant `V state` of `self`, there exists a protobuf sub-state `pb` such that
  the corresponding sub-state `into_pb` produced `pb` (`V.into_pb state = ok pb`), and
  `result.inner_state = some (InnerState.V pb)`.

  Additionally, for each variant, **structural completeness** is guaranteed: every `Option`
  field in the produced protobuf sub-state value is populated (`some`). Concretely:
  - The unchunked core field (`uc`) is always `some`.
  - For variants with a polynomial encoder field (`sending_hdr`, `sending_ek`, `sending_ct1`,
    `sending_ct2`), that field is `some`.
  - For variants with a polynomial decoder field (`receiving_ct1`, `receiving_ct2`,
    `receiving_hdr`, `receiving_ek`), that field is `some`.

This establishes a direct relation between the input `self` and the output `result`:
  1. **Variant preservation**: the `InnerState` tag in the result matches the `States` tag
     of the input.
  2. **Sub-state traceability**: the wrapped protobuf value was produced by the corresponding
     sub-state's `into_pb`, so the caller can apply the sub-state `into_pb_spec` theorem
     (e.g. `KeysUnsampled.into_pb_spec`, `Ct1Sampled.into_pb_spec`, etc.) to obtain
     detailed field-preservation properties (epoch, authenticator keys, polynomial
     encoder/decoder metadata).
  3. **Structural completeness**: all `Option` fields in the sub-state protobuf value are
     populated, ensuring that the serialized message is structurally complete.

The proof uses `h_ok` to rewrite the goal via `spec_ok`, reducing it to the postcondition
applied to the result. It then unfolds `into_pb` in the success hypothesis, case-splits
on the eleven variants, and in each branch decomposes the `bind` to extract both the
sub-state success witness and the `inner_state` equality.  For the structural completeness
properties, the sub-state's `into_pb` is further unfolded to expose that all `Option` fields
are constructed with `some`.

**Source**: spqr/src/v1/chunked/states/serialize.rs (lines 12:4-47:5)
-/
private theorem bind_eq_ok {α β : Type} {m : Result α} {f : α → Result β} {r : β}
    (h : (do let x ← m; f x) = ok r) : ∃ v, m = ok v ∧ f v = ok r := by
  cases m with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])
  | div => exact absurd h (by simp [Bind.bind, Aeneas.Std.bind])

@[step]
theorem into_pb_spec (self : v1.chunked.states.States)
    (h_ok : ∃ r, into_pb self = ok r) :
    into_pb self ⦃ (result : proto.pq_ratchet.V1State) =>
      match self with
      | .KeysUnsampled state =>
          ∃ ku, v1.chunked.send_ek.serialize.KeysUnsampled.into_pb state = ok ku ∧
                result.inner_state = some (.KeysUnsampled ku) ∧
                ∃ uc_inner, ku.uc = some uc_inner
      | .KeysSampled state =>
          ∃ ks, v1.chunked.send_ek.serialize.KeysSampled.into_pb state = ok ks ∧
                result.inner_state = some (.KeysSampled ks) ∧
                (∃ uc_inner, ks.uc = some uc_inner) ∧
                (∃ pe, ks.sending_hdr = some pe)
      | .HeaderSent state =>
          ∃ hs, v1.chunked.send_ek.serialize.HeaderSent.into_pb state = ok hs ∧
                result.inner_state = some (.HeaderSent hs) ∧
                (∃ uc_inner, hs.uc = some uc_inner) ∧
                (∃ pe, hs.sending_ek = some pe) ∧
                (∃ pd, hs.receiving_ct1 = some pd)
      | .Ct1Received state =>
          ∃ cr, v1.chunked.send_ek.serialize.Ct1Received.into_pb state = ok cr ∧
                result.inner_state = some (.Ct1Received cr) ∧
                (∃ uc_inner, cr.uc = some uc_inner) ∧
                (∃ pe, cr.sending_ek = some pe)
      | .EkSentCt1Received state =>
          ∃ escr, v1.chunked.send_ek.serialize.EkSentCt1Received.into_pb state = ok escr ∧
                  result.inner_state = some (.EkSentCt1Received escr) ∧
                  (∃ uc_inner, escr.uc = some uc_inner) ∧
                  (∃ pd, escr.receiving_ct2 = some pd)
      | .NoHeaderReceived state =>
          ∃ nhr, v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb state = ok nhr ∧
                 result.inner_state = some (.NoHeaderReceived nhr) ∧
                 (∃ uc_inner, nhr.uc = some uc_inner) ∧
                 (∃ pd, nhr.receiving_hdr = some pd)
      | .HeaderReceived state =>
          ∃ hr, v1.chunked.send_ct.serialize.HeaderReceived.into_pb state = ok hr ∧
                result.inner_state = some (.HeaderReceived hr) ∧
                (∃ uc_inner, hr.uc = some uc_inner) ∧
                (∃ pd, hr.receiving_ek = some pd)
      | .Ct1Sampled state =>
          ∃ cs, v1.chunked.send_ct.serialize.Ct1Sampled.into_pb state = ok cs ∧
                result.inner_state = some (.Ct1Sampled cs) ∧
                (∃ uc_inner, cs.uc = some uc_inner) ∧
                (∃ pe, cs.sending_ct1 = some pe) ∧
                (∃ pd, cs.receiving_ek = some pd)
      | .EkReceivedCt1Sampled state =>
          ∃ ercs, v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb state = ok ercs ∧
                  result.inner_state = some (.EkReceivedCt1Sampled ercs) ∧
                  (∃ uc_inner, ercs.uc = some uc_inner) ∧
                  (∃ pe, ercs.sending_ct1 = some pe)
      | .Ct1Acknowledged state =>
          ∃ ca, v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb state = ok ca ∧
                result.inner_state = some (.Ct1Acknowledged ca) ∧
                (∃ uc_inner, ca.uc = some uc_inner) ∧
                (∃ pd, ca.receiving_ek = some pd)
      | .Ct2Sampled state =>
          ∃ cs, v1.chunked.send_ct.serialize.Ct2Sampled.into_pb state = ok cs ∧
                result.inner_state = some (.Ct2Sampled cs) ∧
                (∃ uc_inner, cs.uc = some uc_inner) ∧
                (∃ pe, cs.sending_ct2 = some pe) ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  simp only [show into_pb self = ok r from hr, Aeneas.Std.WP.spec_ok]
  unfold into_pb at hr
  cases self with
  | KeysUnsampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.KeysUnsampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, ha⟩ := bind_eq_ok h
    simp only [ok.injEq] at ha
    rw [← ha]; exact ⟨a, rfl⟩
  | KeysSampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.KeysSampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  | HeaderSent state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.HeaderSent.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    obtain ⟨c, _, h4⟩ := bind_eq_ok h3
    simp only [ok.injEq] at h4
    rw [← h4]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩
  | Ct1Received state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.Ct1Received.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  | EkSentCt1Received state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.EkSentCt1Received.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  | NoHeaderReceived state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  | HeaderReceived state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.HeaderReceived.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  | Ct1Sampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct1Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    obtain ⟨c, _, h4⟩ := bind_eq_ok h3
    simp only [ok.injEq] at h4
    rw [← h4]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩
  | EkReceivedCt1Sampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  | Ct1Acknowledged state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  | Ct2Sampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct2Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, _, h2⟩ := bind_eq_ok h
    obtain ⟨b, _, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩

/--
**Universality spec theorem for `v1.chunked.states.serialize.States.into_pb`**:

Strengthens `into_pb_spec` by composing the sub-state `into_pb_spec` theorems from
each variant's serialize module to propagate the following **universality properties**
through the full `States.into_pb` pipeline:

### Universality Property 1 — Epoch Preservation
  For every variant, the epoch field in the serialized unchunked core equals the epoch
  in the input state: `uc_inner.epoch = state.uc.epoch`.

### Universality Property 2 — Authenticator Key Preservation
  For every variant, the authenticator's `root_key` and `mac_key` are faithfully preserved:
  `uc_inner.auth = some a ∧ a.root_key = state.uc.auth.root_key ∧ a.mac_key = state.uc.auth.mac_key`.

### Universality Property 3 — Variant Preservation (inherited from `into_pb_spec`)
  The `InnerState` tag in the result matches the `States` tag of the input.

### Universality Property 4 — Structural Completeness (inherited from `into_pb_spec`)
  All `Option` fields in the sub-state protobuf value are populated (`some`).

These properties establish that the serialization is **faithful**: no protocol-critical
fields (epoch, authentication keys) are lost or modified during the in-memory to protobuf
conversion.

**Source**: spqr/src/v1/chunked/states/serialize.rs (lines 12:4-47:5)
-/
@[step]
theorem into_pb_university_spec (self : v1.chunked.states.States)
    (h_ok : ∃ r, into_pb self = ok r) :
    into_pb self ⦃ (result : proto.pq_ratchet.V1State) =>
      match self with
      | .KeysUnsampled state =>
          ∃ ku, v1.chunked.send_ek.serialize.KeysUnsampled.into_pb state = ok ku ∧
                result.inner_state = some (.KeysUnsampled ku) ∧
                (∃ uc_inner, ku.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key)
      | .KeysSampled state =>
          ∃ ks, v1.chunked.send_ek.serialize.KeysSampled.into_pb state = ok ks ∧
                result.inner_state = some (.KeysSampled ks) ∧
                (∃ uc_inner, ks.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key) ∧
                (∃ pe, ks.sending_hdr = some pe)
      | .HeaderSent state =>
          ∃ hs, v1.chunked.send_ek.serialize.HeaderSent.into_pb state = ok hs ∧
                result.inner_state = some (.HeaderSent hs) ∧
                (∃ uc_inner, hs.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key) ∧
                (∃ pe, hs.sending_ek = some pe) ∧
                (∃ pd, hs.receiving_ct1 = some pd)
      | .Ct1Received state =>
          ∃ cr, v1.chunked.send_ek.serialize.Ct1Received.into_pb state = ok cr ∧
                result.inner_state = some (.Ct1Received cr) ∧
                (∃ uc_inner, cr.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key) ∧
                (∃ pe, cr.sending_ek = some pe)
      | .EkSentCt1Received state =>
          ∃ escr, v1.chunked.send_ek.serialize.EkSentCt1Received.into_pb state = ok escr ∧
                  result.inner_state = some (.EkSentCt1Received escr) ∧
                  (∃ uc_inner, escr.uc = some uc_inner ∧
                    uc_inner.epoch = state.uc.epoch ∧
                    ∃ a, uc_inner.auth = some a ∧
                      a.root_key = state.uc.auth.root_key ∧
                      a.mac_key = state.uc.auth.mac_key) ∧
                  (∃ pd, escr.receiving_ct2 = some pd)
      | .NoHeaderReceived state =>
          ∃ nhr, v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb state = ok nhr ∧
                 result.inner_state = some (.NoHeaderReceived nhr) ∧
                 (∃ uc_inner, nhr.uc = some uc_inner ∧
                   uc_inner.epoch = state.uc.epoch ∧
                   ∃ a, uc_inner.auth = some a ∧
                     a.root_key = state.uc.auth.root_key ∧
                     a.mac_key = state.uc.auth.mac_key) ∧
                 (∃ pd, nhr.receiving_hdr = some pd)
      | .HeaderReceived state =>
          ∃ hr, v1.chunked.send_ct.serialize.HeaderReceived.into_pb state = ok hr ∧
                result.inner_state = some (.HeaderReceived hr) ∧
                (∃ uc_inner, hr.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key) ∧
                (∃ pd, hr.receiving_ek = some pd)
      | .Ct1Sampled state =>
          ∃ cs, v1.chunked.send_ct.serialize.Ct1Sampled.into_pb state = ok cs ∧
                result.inner_state = some (.Ct1Sampled cs) ∧
                (∃ uc_inner, cs.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key) ∧
                (∃ pe, cs.sending_ct1 = some pe) ∧
                (∃ pd, cs.receiving_ek = some pd)
      | .EkReceivedCt1Sampled state =>
          ∃ ercs, v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb state = ok ercs ∧
                  result.inner_state = some (.EkReceivedCt1Sampled ercs) ∧
                  (∃ uc_inner, ercs.uc = some uc_inner ∧
                    uc_inner.epoch = state.uc.epoch ∧
                    ∃ a, uc_inner.auth = some a ∧
                      a.root_key = state.uc.auth.root_key ∧
                      a.mac_key = state.uc.auth.mac_key) ∧
                  (∃ pe, ercs.sending_ct1 = some pe)
      | .Ct1Acknowledged state =>
          ∃ ca, v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb state = ok ca ∧
                result.inner_state = some (.Ct1Acknowledged ca) ∧
                (∃ uc_inner, ca.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key) ∧
                (∃ pd, ca.receiving_ek = some pd)
      | .Ct2Sampled state =>
          ∃ cs, v1.chunked.send_ct.serialize.Ct2Sampled.into_pb state = ok cs ∧
                result.inner_state = some (.Ct2Sampled cs) ∧
                (∃ uc_inner, cs.uc = some uc_inner ∧
                  uc_inner.epoch = state.uc.epoch ∧
                  ∃ a, uc_inner.auth = some a ∧
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key) ∧
                (∃ pe, cs.sending_ct2 = some pe) ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  simp only [show into_pb self = ok r from hr, Aeneas.Std.WP.spec_ok]
  unfold into_pb at hr
  cases self with
  | KeysUnsampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.KeysUnsampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, huc_eq⟩ := bind_eq_ok h
    simp only [ok.injEq] at huc_eq
    unfold v1.unchunked.send_ek.serialize.KeysUnsampled.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst huc_eq
    exact ⟨_, rfl, rfl, _, rfl, rfl, rfl⟩
  | KeysSampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.KeysSampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pe, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ek.serialize.HeaderSent.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩
  | HeaderSent state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.HeaderSent.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pe, _, h3⟩ := bind_eq_ok h2
    obtain ⟨pd, _, h_eq⟩ := bind_eq_ok h3
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ek.serialize.EkSent.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  | Ct1Received state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.Ct1Received.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pe, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ek.serialize.EkSentCt1Received.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩
  | EkSentCt1Received state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.EkSentCt1Received.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pd, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ek.serialize.EkSentCt1Received.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩
  | NoHeaderReceived state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pd, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ct.serialize.NoHeaderReceived.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩
  | HeaderReceived state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.HeaderReceived.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pd, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ct.serialize.HeaderReceived.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩
  | Ct1Sampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct1Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pe, _, h3⟩ := bind_eq_ok h2
    obtain ⟨pd, _, h_eq⟩ := bind_eq_ok h3
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ct.serialize.Ct1Sent.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_rest⟩ := bind_eq_ok huc_ok
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok
    try simp only [Aeneas.Std.bind] at huc_rest
    obtain ⟨ct_vec, _, huc_fin⟩ := bind_eq_ok huc_rest
    simp only [ok.injEq] at huc_fin
    subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  | EkReceivedCt1Sampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pe, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ct.serialize.Ct1SentEkReceived.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_rest⟩ := bind_eq_ok huc_ok
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok
    try simp only [Aeneas.Std.bind] at huc_rest
    obtain ⟨ct_vec, _, huc_fin⟩ := bind_eq_ok huc_rest
    simp only [ok.injEq] at huc_fin
    subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩
  | Ct1Acknowledged state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pd, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ct.serialize.Ct1Sent.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_rest⟩ := bind_eq_ok huc_ok
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok
    try simp only [Aeneas.Std.bind] at huc_rest
    obtain ⟨ct_vec, _, huc_fin⟩ := bind_eq_ok huc_rest
    simp only [ok.injEq] at huc_fin
    subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩
  | Ct2Sampled state =>
    simp only [Aeneas.Std.bind] at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct2Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pe, _, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    unfold v1.unchunked.send_ct.serialize.Ct2Sent.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [Bind.bind, Aeneas.Std.bind, ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨_, rfl, rfl, _, rfl, rfl, rfl⟩, ⟨_, rfl⟩⟩

end spqr.v1.chunked.states.serialize.States
