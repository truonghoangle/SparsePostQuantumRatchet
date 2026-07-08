/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt

/-!
# Spec theorem for `spqr::encoding::polynomial::{Encoder for PolyEncoder}::next_chunk`

The `Encoder` trait method `next_chunk` on `PolyEncoder` produces the next serialized chunk and
advances the encoder's internal chunk counter.  Given a mutable reference to the encoder state,
the function:

  1. Casts the current chunk index `self.idx : U32` to `U16` (the cast succeeds whenever
     `self.idx.val ≤ U16.max`, i.e. the encoder has produced fewer than 2¹⁶ chunks).
  2. Delegates to `self.chunk_at(idx_u16)` to serialize 16 polynomial evaluations into a
     32-byte `Chunk` (see `chunk_at_spec`).
  3. Wrapping-increments the chunk counter: `self.idx ← self.idx.wrapping_add(1)`,
     i.e. `self.idx ← (self.idx + 1) % 2³²`.
  4. Returns the chunk together with the updated encoder state.

The function composes:
  1. `UScalar.cast .U16 self.idx` — checked narrowing of the 32-bit index to 16 bits.
  2. `chunk_at` — serialization of 16 GF(2¹⁶) evaluations into a 32-byte chunk.
  3. `core.num.U32.wrapping_add` — modular increment of the chunk counter (mod 2³²).

**Source**: spqr/src/encoding/polynomial.rs (lines 734:4-738:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk`**
(byte-level):

Produces the next serialized chunk and advances the encoder's chunk counter.  The postcondition
captures the chunk's structural properties, the byte-level encoding invariant, and the index update.

The result satisfies:
  * `chunk.index.val = self.idx.val` — the chunk's U16 index equals the (pre-increment) encoder
    index (which fits in 16 bits by `h_idx_fits`).
  * `chunk.data.val.length = 32` — the data array contains exactly 32 bytes.
  * `self'.idx.val = (self.idx.val + 1) % U32.size` — the encoder's index is wrapping-incremented.
  * If the encoder was initially in the `Polys` state, the encoder state field is unchanged:
      `∀ polys, self.s = .Polys polys → self'.s = self.s`.
  * For every `j ∈ [0, 16)`, the big-endian encoding invariant holds:
      `∃ g hi lo, chunk.data.val[2*j]? = some hi ∧
        chunk.data.val[2*j+1]? = some lo ∧
        hi.val * 256 + lo.val = g.value.val`

This follows from composing:
  1. `UScalar.cast` — succeeds because `self.idx.val ≤ U16.max`.
  2. `chunk_at_spec_nat`: the serialization returns a well-formed chunk with `chunk.index = idx` and
     `chunk.data.val.length = 32`, preserving the encoder state for `Polys`, and satisfying the
     per-byte big-endian encoding invariant.
  3. `core.num.U32.wrapping_add`: the index is incremented modulo 2³².

    This corresponds to the Rust function:
    ```rust
    fn next_chunk(&mut self) -> Chunk {
        let out = self.chunk_at(self.idx as u16);
        self.idx = self.idx.wrapping_add(1);
        out
    }
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 734:4-738:5)
-/
theorem next_chunk_spec_nat
    (self : encoding.polynomial.PolyEncoder)
    (h_idx_fits : self.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ (polys : Array encoding.polynomial.Poly 16#usize),
        ∀ (j : Nat), j < 16 →
          (polys.val[j]!).coefficients.val.length + 1 ≤ Usize.max) :
    next_chunk self ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      chunk.index.val = self.idx.val ∧
      chunk.data.val.length = 32 ∧
      self'.idx.val = (self.idx.val + 1) % U32.size ∧
      (∀ polys, self.s = .Polys polys → self'.s = self.s) ∧
      (∀ (j : Nat), j < 16 →
        ∃ (g : encoding.gf.GF16) (hi lo : Std.U8),
          chunk.data.val[2 * j]? = some hi ∧
          chunk.data.val[2 * j + 1]? = some lo ∧
          hi.val * 256 + lo.val = g.value.val) ⦄ := by
  unfold next_chunk
  step
  step with chunk_at_spec_nat
  step*
  obtain ⟨h_index, h_len, h_idx_preserved, h_stable, h_bytes, _⟩ := out_post
  refine ⟨by simp_all [UScalar.cast_val_eq]; grind, h_len, by simp_all, ?_, ?_⟩
  · intro polys h_polys
    have h_eq := h_stable polys h_polys
    simp_all
  · intro j hj
    obtain ⟨g, hg⟩ := h_bytes j hj
    exact ⟨g, out.data.val[2 * j]'(by omega), out.data.val[2 * j + 1]'(by omega),
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), by grind⟩


/--
For any encoder state whose chunk index fits in 16 bits, `next_chunk self` returns a `Chunk` whose
`index` field records the current chunk index (cast to U16) and whose `data` array contains exactly
32 bytes — the concatenation of the 2-byte big-endian encodings of 16 GF(2¹⁶) polynomial
evaluations.  The encoder's chunk counter is wrapping-incremented modulo 2³², and if the encoder
was in the `Polys` state, the `s` field is unchanged.

This theorem lifts the byte-level postcondition of `next_chunk_spec_nat` to a form suitable for
composition in higher-level proofs (e.g. chunked send paths in `v1::chunked`), dropping the
explicit byte-encoding invariant while retaining the structural and state-preservation properties.
-/
@[step]
theorem next_chunk_spec
    (self : encoding.polynomial.PolyEncoder)
    (h_idx_fits : self.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ (polys : Array encoding.polynomial.Poly 16#usize),
        ∀ (j : Nat), j < 16 →
          (polys.val[j]!).coefficients.val.length + 1 ≤ Usize.max) :
    next_chunk self ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      chunk.index.val = self.idx.val ∧
      chunk.data.val.length = 32 ∧
      self'.idx.val = (self.idx.val + 1) % U32.size ∧
      (∀ polys, self.s = .Polys polys → self'.s = self.s) ⦄ := by
  have h_raw := next_chunk_spec_nat self h_idx_fits h_admissible h_coeff_bound
  apply WP.spec_mono h_raw
  intro (chunk, self') ⟨h_index, h_len, h_idx, h_stable, _⟩
  exact ⟨h_index, h_len, h_idx, h_stable⟩

end spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder
