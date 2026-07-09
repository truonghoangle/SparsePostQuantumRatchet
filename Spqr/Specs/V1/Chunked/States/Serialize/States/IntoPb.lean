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
                match ku.uc with
                | some uc_inner =>
                  uc_inner.epoch = state.uc.epoch ∧
                  match uc_inner.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False
      | .KeysSampled state =>
          ∃ ks, v1.chunked.send_ek.serialize.KeysSampled.into_pb state = ok ks ∧
                result.inner_state = some (.KeysSampled ks) ∧
                (match ks.uc with
                | some hs =>
                  hs.epoch = state.uc.epoch ∧
                  hs.ek = state.uc.ek ∧
                  hs.dk = state.uc.dk ∧
                  match hs.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False) ∧
                match ks.sending_hdr with
                | some pe => pe.idx = state.sending_hdr.idx
                | none => False
      | .HeaderSent state =>
          ∃ hs, v1.chunked.send_ek.serialize.HeaderSent.into_pb state = ok hs ∧
                result.inner_state = some (.HeaderSent hs) ∧
                (match hs.uc with
                | some es =>
                  es.epoch = state.uc.epoch ∧
                  es.dk = state.uc.dk ∧
                  match es.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False) ∧
                (match hs.sending_ek with
                | some pe => pe.idx = state.sending_ek.idx
                | none => False) ∧
                match hs.receiving_ct1 with
                | some pd =>
                  pd.polys = 16#u32 ∧
                  pd.is_complete = state.receiving_ct1.is_complete
                | none => False
      | .Ct1Received state =>
          ∃ cr, v1.chunked.send_ek.serialize.Ct1Received.into_pb state = ok cr ∧
                result.inner_state = some (.Ct1Received cr) ∧
                (match cr.uc with
                | some escr =>
                  escr.epoch = state.uc.epoch ∧
                  escr.dk = state.uc.dk ∧
                  escr.ct1 = state.uc.ct1 ∧
                  match escr.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False) ∧
                match cr.sending_ek with
                | some pe => pe.idx = state.sending_ek.idx
                | none => False
      | .EkSentCt1Received state =>
          ∃ escr, v1.chunked.send_ek.serialize.EkSentCt1Received.into_pb state = ok escr ∧
                  result.inner_state = some (.EkSentCt1Received escr) ∧
                  (match escr.uc with
                  | some escr_inner =>
                    escr_inner.epoch = state.uc.epoch ∧
                    escr_inner.dk = state.uc.dk ∧
                    escr_inner.ct1 = state.uc.ct1 ∧
                    match escr_inner.auth with
                    | some a =>
                      a.root_key = state.uc.auth.root_key ∧
                      a.mac_key = state.uc.auth.mac_key
                    | none => False
                  | none => False) ∧
                  match escr.receiving_ct2 with
                  | some pd =>
                    pd.polys = 16#u32 ∧
                    pd.is_complete = state.receiving_ct2.is_complete
                  | none => False
      | .NoHeaderReceived state =>
          ∃ nhr, v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb state = ok nhr ∧
                 result.inner_state = some (.NoHeaderReceived nhr) ∧
                 (match nhr.uc with
                 | some nhr_inner =>
                   nhr_inner.epoch = state.uc.epoch ∧
                   match nhr_inner.auth with
                   | some a =>
                     a.root_key = state.uc.auth.root_key ∧
                     a.mac_key = state.uc.auth.mac_key
                   | none => False
                 | none => False) ∧
                 match nhr.receiving_hdr with
                 | some pd =>
                   pd.polys = 16#u32 ∧
                   pd.is_complete = state.receiving_hdr.is_complete
                 | none => False
      | .HeaderReceived state =>
          ∃ hr, v1.chunked.send_ct.serialize.HeaderReceived.into_pb state = ok hr ∧
                result.inner_state = some (.HeaderReceived hr) ∧
                (match hr.uc with
                | some hr_inner =>
                  hr_inner.epoch = state.uc.epoch ∧
                  hr_inner.hdr = state.uc.hdr ∧
                  match hr_inner.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False) ∧
                match hr.receiving_ek with
                | some pd =>
                  pd.polys = 16#u32 ∧
                  pd.is_complete = state.receiving_ek.is_complete
                | none => False
      | .Ct1Sampled state =>
          ∃ cs, v1.chunked.send_ct.serialize.Ct1Sampled.into_pb state = ok cs ∧
                result.inner_state = some (.Ct1Sampled cs) ∧
                (match cs.uc with
                | some cs_inner =>
                  cs_inner.epoch = state.uc.epoch ∧
                  cs_inner.hdr = state.uc.hdr ∧
                  cs_inner.es = state.uc.es ∧
                  cs_inner.ct1 = state.uc.ct1 ∧
                  match cs_inner.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False) ∧
                (match cs.sending_ct1 with
                | some pe => pe.idx = state.sending_ct1.idx
                | none => False) ∧
                match cs.receiving_ek with
                | some pd =>
                  pd.polys = 16#u32 ∧
                  pd.is_complete = state.receiving_ek.is_complete
                | none => False
      | .EkReceivedCt1Sampled state =>
          ∃ ercs, v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb state = ok ercs ∧
                  result.inner_state = some (.EkReceivedCt1Sampled ercs) ∧
                  (match ercs.uc with
                  | some cser =>
                    cser.epoch = state.uc.epoch ∧
                    cser.es = state.uc.es ∧
                    cser.ek = state.uc.ek ∧
                    cser.ct1 = state.uc.ct1 ∧
                    match cser.auth with
                    | some a =>
                      a.root_key = state.uc.auth.root_key ∧
                      a.mac_key = state.uc.auth.mac_key
                    | none => False
                  | none => False) ∧
                  match ercs.sending_ct1 with
                  | some pe => pe.idx = state.sending_ct1.idx
                  | none => False
      | .Ct1Acknowledged state =>
          ∃ ca, v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb state = ok ca ∧
                result.inner_state = some (.Ct1Acknowledged ca) ∧
                (match ca.uc with
                | some cs_inner =>
                  cs_inner.epoch = state.uc.epoch ∧
                  cs_inner.hdr = state.uc.hdr ∧
                  cs_inner.es = state.uc.es ∧
                  cs_inner.ct1 = state.uc.ct1 ∧
                  match cs_inner.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False) ∧
                match ca.receiving_ek with
                | some pd =>
                  pd.polys = 16#u32 ∧
                  pd.is_complete = state.receiving_ek.is_complete
                | none => False
      | .Ct2Sampled state =>
          ∃ cs, v1.chunked.send_ct.serialize.Ct2Sampled.into_pb state = ok cs ∧
                result.inner_state = some (.Ct2Sampled cs) ∧
                (match cs.uc with
                | some cs_inner =>
                  cs_inner.epoch = state.uc.epoch ∧
                  match cs_inner.auth with
                  | some a =>
                    a.root_key = state.uc.auth.root_key ∧
                    a.mac_key = state.uc.auth.mac_key
                  | none => False
                | none => False) ∧
                match cs.sending_ct2 with
                | some pe => pe.idx = state.sending_ct2.idx
                | none => False ⦄ := by
  obtain ⟨r, hr⟩ := h_ok
  simp only [show into_pb self = ok r from hr, Aeneas.Std.WP.spec_ok]
  unfold into_pb at hr
  cases self with
  | KeysUnsampled state =>
    simp only at hr
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
    simp only [ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst huc_eq
    exact ⟨rfl, rfl, rfl⟩
  | KeysSampled state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.KeysSampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨uc_val, huc_ok, h2⟩ := bind_eq_ok h
    obtain ⟨pe_val, hpe_ok, h_eq⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h_eq
    have h_idx : pe_val.idx = state.sending_hdr.idx := by
      have hp := hpe_ok
      unfold encoding.polynomial.PolyEncoder.into_pb at hp
      try simp only [alloc.vec.Vec.with_capacity] at hp
      cases hs : state.sending_hdr.s with
      | Points points =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
      | Polys polys =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
    unfold v1.unchunked.send_ek.serialize.HeaderSent.into_pb at huc_ok
    try simp only [Aeneas.Std.bind] at huc_ok
    obtain ⟨auth_val, hauth_ok, huc_fin⟩ := bind_eq_ok huc_ok
    simp only [ok.injEq] at huc_fin
    unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
    simp only [ ok.injEq] at hauth_ok
    subst hauth_ok; subst huc_fin; subst h_eq
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, h_idx⟩
  | HeaderSent state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.HeaderSent.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    obtain ⟨c, hc_ok, h4⟩ := bind_eq_ok h3
    simp only [ok.injEq] at h4
    rw [← h4]
    refine ⟨?_, ?_, ?_⟩
    · unfold v1.unchunked.send_ek.serialize.EkSent.into_pb at ha_ok
      try simp only [Aeneas.Std.bind] at ha_ok
      obtain ⟨auth_val, hauth_ok, ha_fin⟩ := bind_eq_ok ha_ok
      simp only [ok.injEq] at ha_fin
      unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
      simp only [ok.injEq] at hauth_ok
      subst hauth_ok; subst ha_fin
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have hp := hb_ok
      unfold encoding.polynomial.PolyEncoder.into_pb at hp
      try simp only [alloc.vec.Vec.with_capacity] at hp
      cases hs : state.sending_ek.s with
      | Points points =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
      | Polys polys =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
    · -- receiving_ct1: polys and is_complete from PolyDecoder.into_pb
      have hd := hc_ok
      unfold encoding.polynomial.PolyDecoder.into_pb at hd
      try simp only at hd
      obtain ⟨i_val, hi_ok, hd2⟩ := bind_eq_ok hd
      obtain ⟨s_val, _, hd3⟩ := bind_eq_ok hd2
      obtain ⟨s1_val, _, hd4⟩ := bind_eq_ok hd3
      obtain ⟨iter_val, _, hd5⟩ := bind_eq_ok hd4
      obtain ⟨v1_val, _, hd6⟩ := bind_eq_ok hd5
      simp only [ok.injEq] at hd6
      rw [← hd6]
      exact ⟨rfl, rfl⟩
  | Ct1Received state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.Ct1Received.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]
    refine ⟨?_, ?_⟩
    · unfold v1.unchunked.send_ek.serialize.EkSentCt1Received.into_pb at ha_ok
      try simp only [Aeneas.Std.bind] at ha_ok
      obtain ⟨auth_val, hauth_ok, ha_fin⟩ := bind_eq_ok ha_ok
      simp only [ok.injEq] at ha_fin
      unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
      simp only [ok.injEq] at hauth_ok
      subst hauth_ok; subst ha_fin
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · have hp := hb_ok
      unfold encoding.polynomial.PolyEncoder.into_pb at hp
      try simp only [alloc.vec.Vec.with_capacity] at hp
      cases hs : state.sending_ek.s with
      | Points points =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
      | Polys polys =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
  | EkSentCt1Received state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ek.serialize.EkSentCt1Received.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]
    refine ⟨?_, ?_⟩
    · unfold v1.unchunked.send_ek.serialize.EkSentCt1Received.into_pb at ha_ok
      try simp only [Aeneas.Std.bind] at ha_ok
      obtain ⟨auth_val, hauth_ok, ha_fin⟩ := bind_eq_ok ha_ok
      simp only [ok.injEq] at ha_fin
      unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
      simp only [ok.injEq] at hauth_ok
      subst hauth_ok; subst ha_fin
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · -- receiving_ct2: polys and is_complete from PolyDecoder.into_pb
      have hd := hb_ok
      unfold encoding.polynomial.PolyDecoder.into_pb at hd
      try simp only at hd
      obtain ⟨i_val, hi_ok, hd2⟩ := bind_eq_ok hd
      obtain ⟨s_val, _, hd3⟩ := bind_eq_ok hd2
      obtain ⟨s1_val, _, hd4⟩ := bind_eq_ok hd3
      obtain ⟨iter_val, _, hd5⟩ := bind_eq_ok hd4
      obtain ⟨v1_val, _, hd6⟩ := bind_eq_ok hd5
      simp only [ok.injEq] at hd6
      rw [← hd6]
      exact ⟨rfl, rfl⟩
  | NoHeaderReceived state =>
    simp only  at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.NoHeaderReceived.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]
    refine ⟨?_, ?_⟩
    · unfold v1.unchunked.send_ct.serialize.NoHeaderReceived.into_pb at ha_ok
      try simp only [Aeneas.Std.bind] at ha_ok
      obtain ⟨auth_val, hauth_ok, ha_fin⟩ := bind_eq_ok ha_ok
      simp only [ok.injEq] at ha_fin
      unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
      simp only [ok.injEq] at hauth_ok
      subst hauth_ok; subst ha_fin
      exact ⟨rfl, rfl, rfl⟩
    · have hd := hb_ok
      unfold encoding.polynomial.PolyDecoder.into_pb at hd
      try simp only at hd
      obtain ⟨i_val, hi_ok, hd2⟩ := bind_eq_ok hd
      obtain ⟨s_val, _, hd3⟩ := bind_eq_ok hd2
      obtain ⟨s1_val, _, hd4⟩ := bind_eq_ok hd3
      obtain ⟨iter_val, _, hd5⟩ := bind_eq_ok hd4
      obtain ⟨v1_val, _, hd6⟩ := bind_eq_ok hd5
      simp only [ok.injEq] at hd6
      rw [← hd6]
      exact ⟨rfl, rfl⟩
  | HeaderReceived state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.HeaderReceived.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]
    refine ⟨?_, ?_⟩
    · unfold v1.unchunked.send_ct.serialize.HeaderReceived.into_pb at ha_ok
      try simp only [Aeneas.Std.bind] at ha_ok
      obtain ⟨auth_val, hauth_ok, ha_fin⟩ := bind_eq_ok ha_ok
      simp only [ok.injEq] at ha_fin
      unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
      simp only [ok.injEq] at hauth_ok
      subst hauth_ok; subst ha_fin
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have hd := hb_ok
      unfold encoding.polynomial.PolyDecoder.into_pb at hd
      try simp only at hd
      obtain ⟨i_val, hi_ok, hd2⟩ := bind_eq_ok hd
      obtain ⟨s_val, _, hd3⟩ := bind_eq_ok hd2
      obtain ⟨s1_val, _, hd4⟩ := bind_eq_ok hd3
      obtain ⟨iter_val, _, hd5⟩ := bind_eq_ok hd4
      obtain ⟨v1_val, _, hd6⟩ := bind_eq_ok hd5
      simp only [ok.injEq] at hd6
      rw [← hd6]
      exact ⟨rfl, rfl⟩
  | Ct1Sampled state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct1Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    obtain ⟨c, hc_ok, h4⟩ := bind_eq_ok h3
    simp only [ok.injEq] at h4
    rw [← h4]
    refine ⟨?_, ?_, ?_⟩
    · have h_spec := v1.unchunked.send_ct.serialize.Ct1Sent.into_pb_spec state.uc
      rw [ha_ok] at h_spec
      simp only [Aeneas.Std.WP.spec_ok] at h_spec
      exact h_spec
    · have hp := hb_ok
      unfold encoding.polynomial.PolyEncoder.into_pb at hp
      try simp only [alloc.vec.Vec.with_capacity] at hp
      cases hs : state.sending_ct1.s with
      | Points points =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
      | Polys polys =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
    · have hd := hc_ok
      unfold encoding.polynomial.PolyDecoder.into_pb at hd
      try simp only at hd
      obtain ⟨i_val, hi_ok, hd2⟩ := bind_eq_ok hd
      obtain ⟨s_val, _, hd3⟩ := bind_eq_ok hd2
      obtain ⟨s1_val, _, hd4⟩ := bind_eq_ok hd3
      obtain ⟨iter_val, _, hd5⟩ := bind_eq_ok hd4
      obtain ⟨v1_val, _, hd6⟩ := bind_eq_ok hd5
      simp only [ok.injEq] at hd6
      rw [← hd6]
      exact ⟨rfl, rfl⟩
  | EkReceivedCt1Sampled state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.EkReceivedCt1Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]
    refine ⟨?_, ?_⟩
    · have h_spec := v1.unchunked.send_ct.serialize.Ct1SentEkReceived.into_pb_spec state.uc
      rw [ha_ok] at h_spec
      simp only [Aeneas.Std.WP.spec_ok] at h_spec
      exact h_spec
    · have hp := hb_ok
      unfold encoding.polynomial.PolyEncoder.into_pb at hp
      try simp only [alloc.vec.Vec.with_capacity] at hp
      cases hs : state.sending_ct1.s with
      | Points points =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
      | Polys polys =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
  | Ct1Acknowledged state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct1Acknowledged.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]
    refine ⟨?_, ?_⟩
    · have h_spec := v1.unchunked.send_ct.serialize.Ct1Sent.into_pb_spec state.uc
      rw [ha_ok] at h_spec
      simp only [Aeneas.Std.WP.spec_ok] at h_spec
      exact h_spec
    · have hd := hb_ok
      unfold encoding.polynomial.PolyDecoder.into_pb at hd
      try simp only at hd
      obtain ⟨i_val, hi_ok, hd2⟩ := bind_eq_ok hd
      obtain ⟨s_val, _, hd3⟩ := bind_eq_ok hd2
      obtain ⟨s1_val, _, hd4⟩ := bind_eq_ok hd3
      obtain ⟨iter_val, _, hd5⟩ := bind_eq_ok hd4
      obtain ⟨v1_val, _, hd6⟩ := bind_eq_ok hd5
      simp only [ok.injEq] at hd6
      rw [← hd6]
      exact ⟨rfl, rfl⟩
  | Ct2Sampled state =>
    simp only at hr
    obtain ⟨v, hv_ok, hv⟩ := bind_eq_ok hr
    simp only [ok.injEq] at hv; subst hv
    refine ⟨v, hv_ok, rfl, ?_⟩
    have h := hv_ok
    unfold v1.chunked.send_ct.serialize.Ct2Sampled.into_pb at h
    try simp only [Aeneas.Std.bind] at h
    obtain ⟨a, ha_ok, h2⟩ := bind_eq_ok h
    obtain ⟨b, hb_ok, h3⟩ := bind_eq_ok h2
    simp only [ok.injEq] at h3
    rw [← h3]
    refine ⟨?_, ?_⟩
    · unfold v1.unchunked.send_ct.serialize.Ct2Sent.into_pb at ha_ok
      try simp only [Aeneas.Std.bind] at ha_ok
      obtain ⟨auth_val, hauth_ok, ha_fin⟩ := bind_eq_ok ha_ok
      simp only [ok.injEq] at ha_fin
      unfold authenticator.serialize.Authenticator.into_pb at hauth_ok
      simp only [ok.injEq] at hauth_ok
      subst hauth_ok; subst ha_fin
      exact ⟨rfl, rfl, rfl⟩
    · have hp := hb_ok
      unfold encoding.polynomial.PolyEncoder.into_pb at hp
      try simp only [alloc.vec.Vec.with_capacity] at hp
      cases hs : state.sending_ct2.s with
      | Points points =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]
      | Polys polys =>
        simp only [hs] at hp
        try simp only [Aeneas.Std.bind] at hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        obtain ⟨_, _, hp⟩ := bind_eq_ok hp
        simp only [ok.injEq] at hp; rw [← hp]

end spqr.v1.chunked.states.serialize.States
