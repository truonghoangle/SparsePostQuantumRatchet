/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Ratchet Definitions — Explicit HKDF Building Blocks

This file provides the **explicit HKDF-level definitions** that underpin the SPQR
ratchet protocol.  These definitions turn the pseudocode:

```
ikm       = prev.root_key ++ k
info      = PROTOCOL_LABEL ++ ep.to_be_bytes()
kdf_out   = HKDF-SHA256(salt = ZERO_SALT, ikm, info, L = 64)
root_key' = kdf_out[0..32]
mac_key'  = kdf_out[32..64]
```

into actual Lean content, using `kdf.hkdf_to_vec` as the opaque HKDF primitive.

## Contents

- `PROTOCOL_LABEL`: the 45-byte domain-separation string (actual bytes)
- `ZERO_SALT`: the 32-byte zero salt used in HKDF
- `ratchet_ikm`: constructs IKM from root_key and shared secret
- `ratchet_info`: constructs info from protocol label and epoch bytes
- `ratchet_step_explicit`: explicit HKDF-based ratchet step predicate
- `initial_ratchet_step`: initialization predicate (from zero state + auth_key)
- `ratchet_step_operational`: link to the Aeneas-extracted `Authenticator.update`
- `ratchet_chain_valid`: chain validity predicate (uses explicit steps)
- `AuthenticatorState`: snapshot record type

This file has **no dependency** on `Authenticator.New` or `Axioms`, so it can be
imported by both `Authenticator/New.lean` and `ForwardSecrecy.lean` without creating
circular imports.

## References
- RFC 5869 — HKDF
- `src/authenticator.rs` lines 44–54
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ### Protocol Constants -/

/--
The HKDF domain-separation label used in authenticator updates (45 bytes).

This is the UTF-8 encoding of `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"`,
matching the byte literal in `src/authenticator.rs` line 47.

**Source**: `b"Signal_PQCKA_V1_MLKEM768:Authenticator Update"`
-/
def PROTOCOL_LABEL : List U8 := [
  83#u8, 105#u8, 103#u8, 110#u8, 97#u8, 108#u8, 95#u8,     -- "Signal_"
  80#u8, 81#u8, 67#u8, 75#u8, 65#u8, 95#u8,                 -- "PQCKA_"
  86#u8, 49#u8, 95#u8,                                       -- "V1_"
  77#u8, 76#u8, 75#u8, 69#u8, 77#u8, 55#u8, 54#u8, 56#u8,   -- "MLKEM768"
  58#u8,                                                      -- ":"
  65#u8, 117#u8, 116#u8, 104#u8, 101#u8, 110#u8, 116#u8,    -- "Authent"
  105#u8, 99#u8, 97#u8, 116#u8, 111#u8, 114#u8,              -- "icator"
  32#u8,                                                      -- " "
  85#u8, 112#u8, 100#u8, 97#u8, 116#u8, 101#u8               -- "Update"
]

/--
The 32-byte zero salt used as the HKDF salt in every ratchet step.

**Source**: `&[0u8; 32]` in `src/authenticator.rs` line 51.
-/
def ZERO_SALT : List U8 := List.replicate 32 (0#u8 : U8)

/-! ### Ratchet Step Building Blocks -/

/--
Construct the **Input Keying Material (IKM)** for a ratchet step:
`ikm = prev.root_key ++ k`

This is the concatenation of the current root key with the fresh shared secret,
as computed in `src/authenticator.rs` line 45:
```rust
let ikm = [self.root_key.as_slice(), k].concat();
```
-/
def ratchet_ikm (root_key_bytes : List U8) (k_bytes : List U8) : List U8 :=
  root_key_bytes ++ k_bytes

/--
Construct the **info string** for a ratchet step:
`info = PROTOCOL_LABEL ++ ep.to_be_bytes()`

This is the concatenation of the fixed protocol label with the epoch's
big-endian 8-byte encoding, as computed in `src/authenticator.rs` lines 46–50:
```rust
let info = [
    b"Signal_PQCKA_V1_MLKEM768:Authenticator Update".as_slice(),
    &ep.to_be_bytes(),
].concat();
```
-/
def ratchet_info (ep_bytes : List U8) : List U8 :=
  PROTOCOL_LABEL ++ ep_bytes

/-! ### Authenticator State Snapshot -/

/--
A snapshot of the authenticator state at a given epoch, capturing the
`root_key`, `mac_key`, and `epoch` fields.  This is used to define the
ratchet chain as a sequence of such snapshots.
-/
structure AuthenticatorState where
  /-- The current root key (32 bytes), used as IKM prefix for the next HKDF step. -/
  root_key : alloc.vec.Vec U8
  /-- The current MAC key (32 bytes), derived alongside `root_key` in each step. -/
  mac_key  : alloc.vec.Vec U8
  /-- The epoch counter at this state. -/
  epoch    : U64

/--
Convert a concrete `authenticator.Authenticator` and epoch to an `AuthenticatorState`
snapshot.
-/
def AuthenticatorState.ofAuthenticator
    (auth : authenticator.Authenticator) (ep : U64) : AuthenticatorState :=
  { root_key := auth.root_key, mac_key := auth.mac_key, epoch := ep }

/-- The key-length invariant: both root_key and mac_key are 32 bytes. -/
def AuthenticatorState.keyLengthInvariant (s : AuthenticatorState) : Prop :=
  s.root_key.length = 32 ∧ s.mac_key.length = 32

/-! ### Ratchet Step Definitions -/

/--
**Explicit ratchet step** via HKDF-SHA256 (§4.6, §8.4).

Given a previous authenticator state `prev`, a shared secret `k`, and a new
epoch `ep`, the ratchet step is defined by the following explicit computation:

1. `ikm  = prev.root_key.val ++ k.val`          (IKM construction)
2. `info = PROTOCOL_LABEL ++ ep_be_bytes`        (info string with epoch)
3. `kdf_out = HKDF-SHA256(ZERO_SALT, ikm, info, 64)` (key derivation)
4. `next.root_key = kdf_out[0..32]`              (first 32 bytes)
5. `next.mac_key  = kdf_out[32..64]`             (last 32 bytes)

This definition turns the pseudocode into actual Lean content, using
`kdf.hkdf_to_vec` as the opaque HKDF primitive.
-/
def ratchet_step_explicit
    (prev : authenticator.Authenticator) (ep : U64) (k : Slice U8)
    (next : authenticator.Authenticator) : Prop :=
  ∃ (ep_be : Array U8 8#usize)
    (salt_s ikm_s info_s : Slice U8)
    (kdf_out : alloc.vec.Vec U8),
    -- Step 0: Epoch → big-endian bytes
    ep_be = core.num.U64.to_be_bytes ep ∧
    -- Step 1: IKM = prev.root_key ++ k
    ikm_s.val = ratchet_ikm prev.root_key.val k.val ∧
    -- Step 2: info = PROTOCOL_LABEL ++ ep.to_be_bytes()
    info_s.val = ratchet_info ep_be.val ∧
    -- Step 3: salt = [0; 32]
    salt_s.val = ZERO_SALT ∧
    -- Step 4: kdf_out = HKDF-SHA256(salt, ikm, info, 64)
    kdf.hkdf_to_vec salt_s ikm_s info_s 64#usize = ok kdf_out ∧
    -- Step 5: next.root_key = kdf_out[0..32]
    next.root_key.val = kdf_out.val.take 32 ∧
    -- Step 6: next.mac_key  = kdf_out[32..64]
    next.mac_key.val = kdf_out.val.drop 32

/-! ### Initial Ratchet Step -/

/--
**Initial ratchet step**: explicit HKDF characterization of `Authenticator.new(auth_key, ep)`.

The authenticator `auth` was initialized from `auth_key_val` at epoch `ep` via:
1. Starting from a zero-initialized authenticator (`root_key = mac_key = ZERO_SALT`)
2. Applying a single HKDF ratchet step with the auth_key as the shared secret
3. Result has 32-byte keys derived by HKDF-SHA256

This replaces the opaque `Authenticator.new auth_key ep = ok auth` postcondition
with an explicit description of the HKDF computation:
```
ikm       = ZERO_SALT ++ auth_key_val
info      = PROTOCOL_LABEL ++ ep.to_be_bytes()
kdf_out   = HKDF-SHA256(salt = ZERO_SALT, ikm, info, L = 64)
root_key  = kdf_out[0..32]
mac_key   = kdf_out[32..64]
```
-/
def initial_ratchet_step
    (auth_key_val : List U8) (ep : U64)
    (auth : authenticator.Authenticator) : Prop :=
  auth.root_key.length = 32 ∧
  auth.mac_key.length = 32 ∧
  ∃ (zeros : authenticator.Authenticator) (k : Slice U8),
    zeros.root_key.val = ZERO_SALT ∧
    zeros.mac_key.val = ZERO_SALT ∧
    k.val = auth_key_val ∧
    ratchet_step_explicit zeros ep k auth

/-! ### Operational Link -/

/--
**Operational ratchet step**: delegates to `Authenticator.update`.

This is the link to the Aeneas-extracted Rust code.  The explicit HKDF
characterization is given by `ratchet_step_explicit` above.
-/
def ratchet_step_operational
    (prev : authenticator.Authenticator) (ep : U64) (k : Slice U8)
    (next : authenticator.Authenticator) : Prop :=
  authenticator.Authenticator.update prev ep k = ok next

/-! ### Ratchet Chain Validity -/

/--
**Ratchet chain validity predicate** (explicit HKDF version).

A list of `(Authenticator, epoch, shared_secret)` triples forms a valid ratchet
chain if each consecutive pair is connected by `ratchet_step_explicit`:

Each step computes:
```
ikm       = prev.root_key ++ k
info      = PROTOCOL_LABEL ++ next_ep.to_be_bytes()
kdf_out   = HKDF-SHA256(ZERO_SALT, ikm, info, 64)
next.root_key = kdf_out[0..32]
next.mac_key  = kdf_out[32..64]
```

**Mathematical formulation** (from §4.6):
```
∀ i, i + 1 < states.length →
  ratchet_step_explicit states[i].auth states[i+1].epoch k[i+1] states[i+1].auth
```
-/
def ratchet_chain_valid :
    List (authenticator.Authenticator × U64 × Slice U8) → Prop
  | [] => True
  | [_] => True
  | (prev_auth, _, _) :: rest@((next_auth, next_ep, k) :: _) =>
    ratchet_step_explicit prev_auth next_ep k next_auth ∧
    ratchet_chain_valid rest

end spqr
