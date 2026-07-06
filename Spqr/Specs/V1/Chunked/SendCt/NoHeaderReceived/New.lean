/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.NoHeaderReceived.New
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Aeneas.ResultExpect
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::NoHeaderReceived::new`

`NoHeaderReceived.new` constructs the initial state for the ciphertext-sending side of the
V1 chunked SPQR protocol.  It is the entry point of the send-CT state machine and places
the sender into the `NoHeaderReceived` state at epoch 1, with an empty polynomial decoder
ready to receive chunked header data.

The constructor performs the following steps:

1. Computes the header-plus-MAC size: `HEADER_SIZE + MACSIZE` (the total byte length of the
   ML-KEM 768 header and its 32-byte authentication tag).
2. Delegates to `PolyDecoder::new(HEADER_SIZE + MACSIZE)` to construct a polynomial decoder
   for the computed size.  This returns a `Result<PolyDecoder, EncodingError>`.
3. Delegates to `v1::unchunked::send_ct::NoHeaderReceived::new(auth_key)` to construct
   the unchunked inner state (epoch = 1, with a freshly initialised authenticator whose
   `root_key` and `mac_key` are derived via HKDF-SHA256).
4. Unwraps the polynomial decoder via `.expect("should be able to decode header size")`,
   which succeeds when the decoder construction returned `Ok`.
5. Returns a `NoHeaderReceived` struct with the unchunked state (`uc`) and the polynomial
   decoder (`receiving_hdr`).

The by-value `new` introduces no additional logic beyond the delegation to the unchunked
constructor and the polynomial decoder, so its postconditions for the authenticator fields
are inherited from the corresponding `unchunked.NoHeaderReceived.new` specification.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 71:4-79:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.send_ct.NoHeaderReceived

/--
**Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.new`**:

• Takes an `auth_key : Slice U8` — a byte-slice representing the initial authentication root key.
• Computes `i ← incremental_mlkem768.HEADER_SIZE` (the ML-KEM 768 header size in bytes),
  then `i1 ← i + authenticator.Authenticator.MACSIZE` (adding the 32-byte MAC tag size).
• Constructs a `PolyDecoder` via `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new i1`,
  yielding a `Result PolyDecoder EncodingError`.
• Delegates to `v1.unchunked.send_ct.NoHeaderReceived.new auth_key`, which clones the key,
  derives a pair of 32-byte keys via HKDF-SHA256, and returns an unchunked `NoHeaderReceived`
  with `epoch = 1`.
• Unwraps the decoder result via `core.result.Result.expect`, which succeeds when the decoder
  returned `Ok`.
• Returns a chunked `NoHeaderReceived` with `uc := nhr` and `receiving_hdr := pd`.

• The function succeeds (no panic) whenever `auth_key.length ≤ U32.max`, ensuring that
  the key material does not overflow the HKDF input construction.

The result satisfies the following postconditions:

  `result.uc.epoch = 1#u64`
  `result.uc.auth.root_key.length = 32`
  `result.uc.auth.mac_key.length  = 32`
  `∃ v, v.val = auth_key.val ∧ authenticator.Authenticator.new v 1#u64 = ok result.uc.auth`

i.e. the inner unchunked state has epoch initialised to 1, both key fields of the embedded
authenticator are exactly 32 bytes, and the authenticator is deterministically derived from
the input `auth_key` via `Authenticator.new(auth_key.to_vec(), 1)`, which feeds `auth_key`
and epoch `1` into HKDF-SHA256 to produce the 32-byte `root_key` and `mac_key`.

The proof unfolds `new` to expose the underlying `unchunked.NoHeaderReceived.new`,
`PolyDecoder.new`, and `Result.expect` calls and discharges the resulting goal with `step*`,
which applies the already-registered specifications.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 71:4-79:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h_key : auth_key.length ≤ U32.max) :
    new auth_key ⦃ (result : v1.chunked.send_ct.NoHeaderReceived) =>
      result.uc.epoch = 1#u64 ∧
      result.uc.auth.root_key.length = 32 ∧
      result.uc.auth.mac_key.length = 32 ∧
      ∃ v, v.val = auth_key.val ∧
        authenticator.Authenticator.new v 1#u64 = ok result.uc.auth ⦄ := by
  unfold new
  simp only [global_simps, libcrux_ml_kem.mlkem768.incremental.pk1_len, bind_tc_ok]
  step*
  simp only [i1_post, Nat.reduceAdd, Nat.reduceMod, ↓reduceIte, List.reduceReplicate,
    UScalarTy.Usize_numBits_eq, Nat.reduceDiv] at decoder_post
  obtain ⟨pts, _, h_decoder_eq⟩ := decoder_post
  rw [h_decoder_eq]
  step*

end spqr.v1.chunked.send_ct.NoHeaderReceived
