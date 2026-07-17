/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `core::num::U16::from_be_bytes`

In Rust's standard library, `u16::from_be_bytes([hi, lo])` reconstructs a `u16` value from its
2-byte big-endian representation: `result = hi * 256 + lo`.

The Aeneas-extracted Lean function `core.num.U16.from_be_bytes` mirrors this behavior.

This is used in `Pt::deserialize` and `Poly::deserialize` to decode GF(2¹⁶) field elements
from their byte representation.

**Source**: core/src/num/uint_macros.rs (u16::from_be_bytes)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.num.U16

/--
**Spec theorem for `core.num.U16.from_be_bytes`**:

The big-endian decoding of a 2-byte array `a` satisfies
  `result.val = a[0].val * 256 + a[1].val`.

**Source**: core/src/num/uint_macros.rs (u16::from_be_bytes)
-/
@[step]
theorem from_be_bytes_spec (a : Array Std.U8 2#usize) :
    lift (core.num.U16.from_be_bytes a) ⦃ result =>
      result.val = (a[0]!).val * 256 + (a[1]!).val ⦄ := by
  simp  only [lift, core.num.U16.from_be_bytes, Std.UScalar.val]
  -- Decompose the 2-element array to expose list structure
  rcases a with ⟨_ | ⟨a0, _ | ⟨a1, l⟩⟩, hlen⟩
  · simp at hlen
  · simp at hlen
  · simp only [List.length_cons] at hlen
    have hl : l = [] := by
      rcases l with _ | ⟨_, _⟩
      · rfl
      · simp at hlen
    subst hl
    simp only [UScalarTy.Usize_numBits_eq, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceMul, UScalarTy.U16_numBits_eq, BitVec.fromBEBytes, List.reverse, List.reverseAux_cons,
    List.reverseAux_nil, BitVec.fromLEBytes, BitVec.setWidth_eq,
    Nat.mul_zero, zero_le, pow_zero, zero_lt_one,
    BitVec.setWidth_ofNat_of_le_of_lt, le_refl, BitVec.shiftLeft_eq_zero,
    BitVec.or_zero, BitVec.cast_eq,
    Bvify.U16.UScalar_bv, UScalar.bv_toNat, UScalarTy.U8_numBits_eq,
    Array.getElem!_Nat_eq, zero_add, Nat.ofNat_pos,
    getElem!_pos, List.getElem_cons_zero, Bvify.U8.UScalar_bv,
    Nat.one_lt_ofNat, List.getElem_cons_succ, WP.spec_ok]
    -- Unfold UScalar.val coercion to expose BitVec.toNat
    simp only [Std.UScalar.val]
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq]
    have h0 : a0.bv.toNat < 2 ^ 8 := a0.bv.isLt
    have h1 : a1.bv.toNat < 2 ^ 8 := a1.bv.isLt
    simp only [UScalarTy.U16_numBits_eq,
    BitVec.toNat_setWidth, UScalar.bv_toNat, Nat.reducePow, Nat.mod_mul_mod,
    UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv]
    have h10 : a1.val < 65536 := by grind
    have h11:=Nat.mod_eq_of_lt h10
    rw [h11]
    have h00 : a0.val * 256 < 65536 := by grind
    have h01:=Nat.mod_eq_of_lt h00
    rw [h01]
    symm
    rw[Nat.or_comm, mul_comm, (by grind : 256 = 2 ^ 8)]
    apply Nat.two_pow_add_eq_or_of_lt
    grind

end Aeneas.Std.core.num.U16
