/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Trusted Cryptographic and Serialization Axioms

This file declares trusted axioms for opaque external operations used in the SPQR protocol
verification. These axioms cannot be proved within the Lean formalization because they depend
on either:
- Computational security assumptions (e.g., HKDF as a PRF)
- External library implementations (e.g., protobuf encode/decode from prost)

Each axiom is documented with its justification and relevant standards references.

## Axiom Categories

### HKDF Axioms (RFC 5869)
- `hkdf_output_length`: HKDF-SHA256 output is at least as long as requested
- `hkdf_domain_separation`: Distinct info strings yield distinct HKDF outputs (PRF assumption)

### Protobuf Axioms (prost library)
- `protobuf_encode_to_vec_ok`: Protobuf encoding always succeeds
- `protobuf_encode_decode_roundtrip`: Protobuf encode-decode round-trip identity

## References
- RFC 5869 — HMAC-based Extract-and-Expand Key Derivation Function (HKDF)
- RFC 2104 — HMAC: Keyed-Hashing for Message Authentication
- Protocol Buffers Language Guide v3 — deterministic serialization
- `aeneas-config.yml` lines 86–87 (prost `Message` bodies sorry'd)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ### HKDF Axioms -/

section HkdfAxioms

/--
**Axiom: HKDF output length guarantee**.

The HKDF-SHA256 expansion function produces output of at least the requested length.
This is a structural property of the HKDF construction (RFC 5869 §2.3): given valid
inputs, HKDF-Expand produces `L` bytes of output where `L ≤ 255 * HashLen`.

In the SPQR protocol, `L = 64` (two 32-byte keys), which is well within the
`255 * 32 = 8160` byte limit for SHA-256.

**Justification**: This follows from the HKDF specification. The implementation
uses `libcrux_hmac`, a verified HMAC library.

**References**:
- RFC 5869 §2.3: `HKDF-Expand(PRK, info, L) → OKM`
- NIST SP 800-56C Rev. 2 §4
-/
axiom hkdf_output_length :
  ∀ (salt ikm info : Slice U8) (len : Usize) (output : alloc.vec.Vec U8),
    kdf.hkdf_to_vec salt ikm info len = ok output →
    output.length ≥ len.val

/--
**Axiom: HKDF domain separation**.

If two HKDF invocations use the same salt and IKM but distinct info strings, their
outputs are computationally independent. This models the PRF assumption on HMAC-SHA256:
treating HMAC as a pseudorandom function, different inputs yield independent-looking outputs.

This axiom captures the computational security guarantee that cannot be proved
structurally. It complements the symbolic verification in the ProVerif model
(`proofs/proverif/spqr-cka.pv`).

**Mathematical formulation**: For distinct `(info₁, info₂)` pairs:
```
  HKDF(salt, ikm, info₁, L) ≠ HKDF(salt, ikm, info₂, L)
```
under the assumption that `info₁ ≠ info₂` and the output length is non-zero.

**References**:
- Krawczyk, H. "Cryptographic Extraction and Key Derivation: The HKDF Scheme" §3.2
- Signal Protocol specification — domain separation conventions
-/
axiom hkdf_domain_separation :
  ∀ (salt ikm info₁ info₂ : Slice U8) (len : Usize)
    (out₁ out₂ : alloc.vec.Vec U8),
    info₁.val ≠ info₂.val →
    len.val > 0 →
    kdf.hkdf_to_vec salt ikm info₁ len = ok out₁ →
    kdf.hkdf_to_vec salt ikm info₂ len = ok out₂ →
    out₁ ≠ out₂

end HkdfAxioms

/-! ### Protobuf Axioms -/

section ProtobufAxioms

/--
**Axiom: Protobuf encoding always succeeds**.

The `encode_to_vec` method on `PqRatchetState` always produces a valid byte vector.
This is a property of the prost library's code-generated serialization: every
well-formed `PqRatchetState` value can be serialized without error.

**Justification**: The prost library guarantees that `encode_to_vec` is infallible
for any valid protobuf message struct. The Aeneas extraction marks the `Message`
trait body as `sorry`, so we axiomatize this instead.

**References**:
- Protocol Buffers Language Guide v3 — deterministic serialization
- `aeneas-config.yml` (prost `Message` bodies sorry'd)
-/
axiom protobuf_encode_to_vec_ok :
  ∀ (pb : proto.pq_ratchet.PqRatchetState),
    ∃ v, proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec
      pb = ok v

/--
**Axiom: Protobuf encode-decode round-trip identity**.

Encoding a `PqRatchetState` to bytes and decoding back yields the original value.
This is the fundamental correctness property of protobuf serialization.

For a non-empty encoded byte vector, `decode_state` decodes via the prost `Message::decode`
method and the result matches the original protobuf value.

**Justification**: Protocol Buffers v3 guarantees deterministic serialization for
well-formed messages. The prost library's `Message::encode` and `Message::decode`
implement this round-trip correctly for all generated message types.

**References**:
- Protocol Buffers Language Guide v3 — deterministic serialization guarantees
- prost library documentation — `Message` trait contract
-/
axiom protobuf_encode_decode_roundtrip :
  ∀ (pb : proto.pq_ratchet.PqRatchetState) (v : alloc.vec.Vec U8),
    proto.pq_ratchet.PqRatchetState.Insts.ProstMessageMessage.encode_to_vec
      pb = ok v →
    decode_state v = ok (core.result.Result.Ok pb)

end ProtobufAxioms

end spqr
