/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt
public import Spqr.Math.Poly.Lagrange.CompletePoints
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree

/-! # Spec theorem for `spqr::encoding::polynomial::{Encoder for PolyEncoder}::next_chunk`

Casts `self.idx` to U16, calls `chunk_at`, then increments the index via `checked_add(1)`
(panics on overflow instead of silently wrapping).

**D50 fix**: replaced `wrapping_add(1)` with `checked_add(1).expect(...)` in Rust;
the Lean spec now requires `self.idx.val < U32.max` (strictly less) so the increment
cannot overflow, and the postcondition uses plain `self.idx.val + 1` instead of
`(self.idx.val + 1) % U32.size`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk`**:

Postcondition: `chunk.index = self.idx`, `chunk.data.length = 32`,
`self'.idx = self.idx + 1` (no wrapping — `checked_add` panics at `U32.max`), plus polynomial-evaluation (`Polys`) or
Lagrange-interpolation (`Points`) invariants on the chunk data. -/
@[step]
theorem next_chunk_spec
    (self : encoding.polynomial.PolyEncoder)
    (h_idx_fits : self.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    next_chunk self ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      chunk.index.val = self.idx.val ∧
      chunk.data.length = 32 ∧
      self'.idx.val = self.idx.val + 1 ∧
      match self.s with
      | .Polys polys =>
          self'.s = self.s ∧
          ∀ (j : Nat), j < 16 →
            Nat.toGF216 (256 * chunk.data[2 * j]! + chunk.data[2 * j + 1]!) =
              (polys[j]!).toGF216Poly.eval (self.idx.val.toGF216)
      | .Points pts =>
          ∀ polys', self'.s = .Polys polys' →
            ∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k ⦄ := by
  unfold next_chunk
  step
  step with chunk_at_spec
  step*
  obtain ⟨h_idx_eq, h_data_len, h_self_idx, h_match⟩ := out_post
  refine ⟨by simp_all [UScalar.cast_val_eq]; grind, h_data_len, by
  simp_all only [alloc.vec.Vec.length,
    Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
    List.length_eq_zero_iff, Order.add_one_le_iff, List.getElem!_eq_getElem?_getD,
    UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.reducePow, alloc.vec.Vec.getElem!_Nat_eq,
    alloc.vec.Vec.len, core.num.U32.wrapping_add_val_eq, UScalar.size_UScalarTyU32]; scalar_tac, ?_⟩
  cases h_s : self.s with
  | Polys polys =>
    simp only [h_s] at h_match ⊢
    obtain ⟨h_self_eq, h_eval⟩ := h_match
    refine ⟨by simp_all, fun j hj => ?_⟩
    have := h_eval j hj
    simp_all [UScalar.cast_val_eq]
    grind
  | Points pts =>
    simp only [h_s] at h_match ⊢
    intro polys' h_polys' j hj
    exact h_match polys' h_polys' j hj

/-- **D5. `PolyEncoder` index `u32→u16` truncation: the cast is lossy.**

`polynomial.rs` L735: `self.idx as u16`. The `UScalar.cast .U16` produces
`idx.val % 2^16`, which differs from `idx.val` when `idx.val > U16.max = 65535`.
After 65535 chunks the emitted `chunk.index` wraps to 0, making D16 poisoning
permanent.

This theorem proves: `idx % 2^16 ≠ idx` whenever `idx > U16.max`. The spec
`next_chunk_spec` requires `h_idx_fits : self.idx.val ≤ U16.max` precisely to
exclude this truncation; `FromPb.lean` does **not** enforce this bound. -/
theorem idx_cast_u16_lossy (idx : U32) (h_big : idx.val > U16.max) :
    idx.val % (2 ^ U16.numBits) ≠ idx.val := by
  have : idx.val % 2 ^ U16.numBits < 2 ^ U16.numBits := Nat.mod_lt _ (by positivity)
  simp [U16.max, U16.numBits, UScalarTy.numBits] at *
  omega

end spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder
