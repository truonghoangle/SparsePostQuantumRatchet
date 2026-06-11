/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Lib.EmptyState

/-!
# Spec theorem for `spqr::initial_state`

In the Sparse Post-Quantum Ratchet, a *serialized state* is a `Vec<u8>` — a heap-allocated byte
buffer carrying the wire-format representation of a ratchet state. The top-level helper
`initial_state` constructs the very first serialized state for a freshly-started ratchet, branching
on the protocol version carried by its `Params` argument.

The function proceeds in two stages, selected by `params.version`:
  1. `Version.V0` — the "no-state-yet" case. Delegate to `empty_state` to allocate a fresh
     `Vec<u8>` whose backing list is `[]`, and wrap it in `core::result::Result::Ok`.
  2. `Version.V1` — the negotiated case. Convert the caller-supplied `auth_key` slice to a
     `Vec<u8>`, lift `direction` and `min_version` to their on-wire `i32` encodings, lower
     `chain_params` to its protobuf form via `ChainParams.into_pb`, derive the protocol-specific
     `inner` payload via `init_inner`, and finally encode the assembled `PqRatchetState` to a byte
     vector via `prost::Message::encode_to_vec`, wrapping the result in `core::result::Result::Ok`.

In every case the outer `Result` carries `Ok`: `initial_state` has no failure path of its own — it
only forwards the outcomes of pure constructors and serialization helpers. The `V0` branch is the
"empty initial state" canonical witness and is the case fully characterized at the byte level by
the spec below; the `V1` branch is left abstract here, as its byte contents depend on the opaque
protobuf-encoding layer.

**Source**: spqr/src/lib.rs (lines 212:0-236:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr::initial_state` at the list level (V0 branch)**:

When the negotiated protocol version is `V0`, `initial_state` is byte-for-byte equivalent to
`empty_state` wrapped in `core::result::Result::Ok`. The Rust source

```rust
pub fn initial_state(params: Params) -> Result<SerializedState, Error> {
    match params.version {
        Version::V0 => Ok(empty_state()),
        _ => { /* V1 protobuf encoding path */ }
    }
}
```

extracts to a definition that, on the `V0` branch, reduces to
```
do
  let v ← empty_state
  ok (core.result.Result.Ok v)
```

The V0 branch never fails and its result is fully determined: the inner `Ok` carries a vector
whose backing list is the empty list. Formally,
  `result = core.result.Result.Ok v  ∧  v.val = []`.

This follows directly from the `V0` reduction together with the list-level characterization of
`empty_state` (`empty_state_spec_nat`): unfolding `initial_state` exposes the bind to `empty_state`,
whose backing list is `[]`, and the surrounding `core.result.Result.Ok` constructor preserves this
information. It is the strongest possible characterization of the output on the `V0` branch and is
the foundational fact from which all weaker, more "interface-level" properties (e.g. inner
length-`0`, emptiness predicate, outer never-`Err`) follow.

**Source**: spqr/src/lib.rs (lines 212:0-236:1)
-/
theorem initial_state_spec_nat (params : Params)
    (hv : params.version = proto.pq_ratchet.Version.V0) :
    initial_state params ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) Error) =>
      ∃ v, result = core.result.Result.Ok v ∧ v.val = [] ⦄ := by
  unfold initial_state
  rw [hv]
  step with empty_state_spec_nat as ⟨v, hv_val⟩
  exact ⟨v, rfl, hv_val⟩

/--
For any "size measure" `List.length : List Std.U8 → ℕ` that vanishes on the empty list, the
inner `Ok`-carried vector produced by `initial_state` on the `V0` branch corresponds — via
`List.length ∘ alloc.vec.Vec.val` — to `0`.

Specializing the underlying-list characterization of `initial_state_spec_nat` to the length
measure recovers the standard "the returned buffer has size `0`" interpretation on the `V0`
branch, which is the form most commonly consumed by downstream callers (e.g. as the initial
accumulator in state-serialization loops, or as the witness that no bytes are yet pending for a
ratchet whose negotiated version is the disabled placeholder `V0`).

The result is *unconditional* in the sense that no opaque-operation hypotheses are required for
the `V0` branch: every subcomputation is a pure constructor, and the wrapping `core.result.Result.Ok`
is transparent. Specializing further to the `V1` branch (whose byte contents depend on the opaque
protobuf-encoding layer) requires additional hypotheses about `prost::Message::encode_to_vec` and
its dependencies and is out of scope for this lemma.
-/
@[step]
theorem initial_state_spec (params : Params)
    (hv : params.version = proto.pq_ratchet.Version.V0) :
    initial_state params ⦃ (result : core.result.Result (alloc.vec.Vec Std.U8) Error) =>
      ∃ v, result = core.result.Result.Ok v ∧ v.val.length = 0 ⦄ := by
  unfold initial_state
  rw [hv]
  step*

end spqr
