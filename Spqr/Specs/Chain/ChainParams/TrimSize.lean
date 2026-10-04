/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
/-! # Spec theorem for `spqr::chain::{spqr::proto::pq_ratchet::ChainParams}::trim_size`

Computes the GC threshold as `max_ooo * 11 / 10 + 1`, where `max_ooo` comes from
`max_ooo_keys_or_default` (default 2000). The bound `max_ooo < 390451572` ensures no overflow
even on 32-bit targets. Reintroduced here as `h_ooo` since Aeneas erases `hax_lib::assume!`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams

/-- **Spec theorem for `spqr.chain.ChainParams.trim_size`**:

Shows `result.val = max_ooo * 11 / 10 + 1` where `max_ooo` is the defaulted OOO budget.
Two biconditionals capture the verbatim vs default branches:
  • `result.val = self.max_ooo_keys.val * 11 / 10 + 1 ↔ self.max_ooo_keys > 0#u32`
  • `result.val = 2201 ↔ self.max_ooo_keys = 0#u32 ∨ self.max_ooo_keys = 2000#u32`

The `∨ 2000` disjunct covers the case where the caller supplied exactly the default.
No overflow: `h_ooo` bounds `max_ooo` so `max_ooo * 11` fits in 32 bits. -/
@[step]
theorem trim_size_spec (self : proto.pq_ratchet.ChainParams)
    (h_ooo : self.max_ooo_keys.val < 390451572) :
    trim_size self ⦃ (result : Std.Usize) =>
      (result.val = self.max_ooo_keys.val * 11 / 10 + 1 ↔ self.max_ooo_keys > 0#u32) ∧
      (result.val = 2201 ↔
        self.max_ooo_keys = 0#u32 ∨ self.max_ooo_keys = 2000#u32) ⦄ := by
  unfold trim_size max_ooo_keys_or_default
  split <;>
    (step* <;>
      simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq,
        DEFAULT_CHAIN_PARAMS_spec] <;>
      scalar_tac)

/-- **D8. `usize` overflow in `trim_size` on 32-bit.**

`chain.rs` L86: `max_ooo * 11` overflows when `max_ooo_keys ≥ 390451573` on 32-bit
(where `Usize.max = 2^32 - 1`, so `⌊Usize.max / 11⌋ + 1 = 390451573`).
The `h_ooo` precondition of `trim_size_spec` (`max_ooo_keys < 390451572`) exists
precisely to prevent this; but the Rust `assume!` at L86 is erased, so any
`max_ooo_keys` value may reach `trim_size`.

This theorem proves: when `max_ooo_keys ≥ 390451573` and `System.Platform.numBits = 32`,
`trim_size` has no `ok` result — the `Usize` multiplication `max_ooo * 11` overflows. -/
theorem trim_size_overflow_on_32bit (self : proto.pq_ratchet.ChainParams)
    (h_32bit : System.Platform.numBits = 32)
    (h_large : self.max_ooo_keys.val ≥ 390451573) :
    ∀ r, trim_size self ≠ ok r := by
  intro r h
  unfold trim_size at h
  obtain ⟨mo', h_mo', h_mo1, _⟩ :=
    WP.spec_imp_exists (max_ooo_keys_or_default_spec self)
  simp only [h_mo', bind_tc_ok] at h
  have h_mo_ge : mo'.val ≥ 390451573 := by
    by_cases hpos : self.max_ooo_keys > 0#u32
    · have := h_mo1.mpr hpos; subst this; exact h_large
    · simp only [gt_iff_lt, not_lt] at hpos; scalar_tac
  -- The multiplication (UScalar.cast .Usize mo') * 11 must succeed for h to hold
  -- Show it fails: on 32-bit, cast is identity, and mo'.val * 11 > Usize.max
  have h_cast_val : (UScalar.cast UScalarTy.Usize mo').val = mo'.val := by
    simp only [UScalar.cast, UScalar.val, BitVec.toNat_setWidth,
      h_32bit, UScalarTy.numBits]
    have : mo'.val < 2 ^ 32 := by scalar_tac
    exact Nat.mod_eq_of_lt this
  -- Show the mul fails by examining mul_equiv
  have h_mul_equiv := UScalar.mul_equiv (UScalar.cast UScalarTy.Usize mo') 11#usize
  -- The multiplication is `.mul`, which is the same as `*` but spelled differently
  -- If it were ok, we'd have cast.val * 11 ≤ Usize.max
  -- On 32-bit with mo'.val ≥ 390451573: mo'.val * 11 ≥ 4294967303 > 4294967295
  -- So it must be fail
  have h_overflow : Usize.max < (UScalar.cast UScalarTy.Usize mo').val * 11 := by
    rw [h_cast_val]
    simp only [Usize.max, h_32bit, UScalarTy.numBits,
      Usize.numBits]
    omega
  -- mul_equiv on the fail case tells us exactly this
  -- We need to show `h` leads to contradiction: the mul in `trim_size` fails
  -- The function binds on `max_ooo * 11#usize`, so if that fails, the whole thing fails
  -- h : (do let i1 ← cast * 11; let i2 ← i1 / 10; i2 + 1) = ok r
  -- but cast * 11 = fail (since Usize.max < cast.val * 11)
  have : ¬ (∃ z, UScalar.mul (UScalar.cast UScalarTy.Usize mo') 11#usize = ok z) := by
    intro ⟨z, hz⟩
    rw [hz] at h_mul_equiv
    simp only [UScalar.ofNatCore_val_eq] at h_mul_equiv
    rw [h_cast_val] at h_mul_equiv
    simp only [UScalar.max, h_32bit, UScalarTy.numBits] at h_mul_equiv
    omega
  -- The bind in h must fail, contradicting h : ... = ok r
  -- h is: (do let max_ooo ← lift (cast mo'); let i1 ← max_ooo * 11; ...) = ok r
  -- The cast is pure (lift always ok), but the mul fails
  -- Rewrite h to expose the failure
  simp only [lift, bind_tc_ok, HMul.hMul] at h
  -- Now h should have UScalar.mul (cast mo') 11
  -- Show the mul cannot be ok
  cases h_eq : UScalar.mul (UScalar.cast UScalarTy.Usize mo') 11#usize with
  | ok z => exact absurd ⟨z, h_eq⟩ this
  | fail e => simp [h_eq, Bind.bind, Std.bind] at h
  | div => simp [h_eq, Bind.bind, Std.bind] at h

end spqr.chain.ChainParams
