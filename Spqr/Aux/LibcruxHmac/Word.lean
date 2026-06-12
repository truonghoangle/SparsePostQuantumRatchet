/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Aeneas

/-!
# Word-level operations for SHA-1 / SHA-2

FIPS 180-2 §§2–3 defines several word-level operations on 32-bit and 64-bit
unsigned integers that are shared by every SHA variant:

* **Rotations**: `ROTL(n, x)`, `ROTR(n, x)` — circular left/right rotation;
* **Shift**: `SHR(n, x)` — logical right shift;
* **Modular addition**: `(a + b) mod 2^w` — unsigned wrapping addition.

The Aeneas scalar library already provides:
- `UScalar.rotate_left` / `UScalar.rotate_right` (backed by `BitVec.rotateLeft` /
  `BitVec.rotateRight`), with `@[step_pure_def]` attribute;
- `UScalar.wrapping_add` (backed by `BitVec` addition modulo 2^w), with
  `@[step_pure_def]` attribute and simp lemmas
  `wrapping_add_bv_eq` / `wrapping_add_val_eq`;
- AND `&&&`, OR `|||`, XOR `^^^`, NOT `~~~` on `UScalar` types.

Lean 4's `Init.Data.BitVec.Lemmas` provides:
- `BitVec.rotateLeft_def`, `BitVec.rotateRight_def` (shift/or decomposition);
- `BitVec.rotateLeft_mod_eq_rotateLeft`, `BitVec.rotateRight_mod_eq_rotateRight`;
- `BitVec.toNat_rotateLeft`, `BitVec.toNat_rotateRight`;
- `BitVec.getLsbD_rotateLeft`, `BitVec.getLsbD_rotateRight`.

This file introduces thin SHA-specific **abbreviations** (`rotl`, `rotr`,
`wadd`) in the `spec.sha` namespace, together with:

natural language specs:
- `rotl_def` / `rotr_def`: unfolding to shifts and OR (FIPS 180-2 §3.2 eq. (3.3)/(3.4));
- `rotl_rotr_inverse` / `rotr_rotl_inverse`: rotation self-inverse;
- `wadd_val`: `(wadd x y).val = (x.val + y.val) % 2^w` (the FIPS 180-2
  §2 modular-addition equation);
- `wadd_comm`: commutativity of modular addition;
- `wadd_assoc`: associativity of modular addition;
- `wadd_bv_eq`: the underlying `BitVec` of `wadd x y` is `x.bv + y.bv`.

**Source**: FIPS 180-2 §§2–3 (words, operations on words).
-/

open Aeneas Aeneas.Std

namespace spec.sha

/-! ## Abbreviations for SHA word operations -/

/-- SHA rotation left: `ROTL(n, x) = (x <<< n) ||| (x >>> (w − n))`.
    Wraps `UScalar.rotate_left`, which is backed by `BitVec.rotateLeft`.
    FIPS 180-2 §3.2, equation (3.3). -/
abbrev rotl {ty : UScalarTy} (n : U32) (x : UScalar ty) : UScalar ty :=
  UScalar.rotate_left x n

/-- SHA rotation right: `ROTR(n, x) = (x >>> n) ||| (x <<< (w − n))`.
    Wraps `UScalar.rotate_right`, which is backed by `BitVec.rotateRight`.
    FIPS 180-2 §3.2, equation (3.4). -/
abbrev rotr {ty : UScalarTy} (n : U32) (x : UScalar ty) : UScalar ty :=
  UScalar.rotate_right x n

/-- SHA modular (wrapping) addition: `(a + b) mod 2^w`.
    Wraps `UScalar.wrapping_add`.
    FIPS 180-2 §2: "addition modulo 2^w". -/
abbrev wadd {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  UScalar.wrapping_add x y

/-! ## Rotation: structural decomposition -/

/-- **Spec lemma (`rotl_def`)**: `rotl n x` decomposes as
    `(x <<< (n % w)) ||| (x >>> (w − n % w))` at the `BitVec` level.
    Re-exports `BitVec.rotateLeft_def`.
    FIPS 180-2 §3.2, equation (3.3). -/
theorem rotl_def {ty : UScalarTy} (n : U32) (x : UScalar ty) :
    (rotl n x).bv =
      (x.bv <<< (n.val % ty.numBits)) |||
      (x.bv >>> (ty.numBits - n.val % ty.numBits)) := by
  simp only [rotl, UScalar.rotate_left]
  exact BitVec.rotateLeft_def

/-- **Spec lemma (`rotr_def`)**: `rotr n x` decomposes as
    `(x >>> (n % w)) ||| (x <<< (w − n % w))` at the `BitVec` level.
    Re-exports `BitVec.rotateRight_def`.
    FIPS 180-2 §3.2, equation (3.4). -/
theorem rotr_def {ty : UScalarTy} (n : U32) (x : UScalar ty) :
    (rotr n x).bv =
      (x.bv >>> (n.val % ty.numBits)) |||
      (x.bv <<< (ty.numBits - n.val % ty.numBits)) := by
  simp only [rotr, UScalar.rotate_right]
  exact BitVec.rotateRight_def

/-! ## Rotation: self-inverse -/

/-- **Spec lemma (`rotl_rotr_inverse`)**: rotating left by `n` then right by `n`
    is the identity: `rotr n (rotl n x) = x`.

    This is a fundamental algebraic property of circular rotations used when
    normalizing round-function expressions in SHA-1/SHA-2 proofs. -/
@[simp]
theorem rotl_rotr_inverse {ty : UScalarTy} (n : U32) (x : UScalar ty) :
    rotr n (rotl n x) = x := by
  simp only [rotr, rotl, UScalar.rotate_right, UScalar.rotate_left]
  rw [UScalar.eq_equiv_bv_eq]
  ext i
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_rotateLeft]
  split <;> split <;> (first | rfl | (congr 1; omega))

/-- **Spec lemma (`rotr_rotl_inverse`)**: rotating right by `n` then left by `n`
    is the identity: `rotl n (rotr n x) = x`.

    Symmetric companion to `rotl_rotr_inverse`. -/
@[simp]
theorem rotr_rotl_inverse {ty : UScalarTy} (n : U32) (x : UScalar ty) :
    rotl n (rotr n x) = x := by
  simp only [rotr, rotl, UScalar.rotate_right, UScalar.rotate_left]
  rw [UScalar.eq_equiv_bv_eq]
  ext i
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split <;> split <;> (first | rfl | (congr 1; omega))

/-! ## Modular addition -/

/-- **Spec lemma (`wadd_bv_eq`)**: the underlying `BitVec` of `wadd x y` is
    `x.bv + y.bv` (wrapping modular addition at the BitVec level).
    Re-exports `UScalar.wrapping_add_bv_eq`. -/
@[simp]
theorem wadd_bv_eq {ty : UScalarTy} (x y : UScalar ty) :
    (wadd x y).bv = x.bv + y.bv :=
  UScalar.wrapping_add_bv_eq x y

/-- **Spec lemma (`wadd_val`)**: `(wadd x y).val = (x.val + y.val) % 2^w`.
    This is the precise statement of FIPS 180-2 §2 "addition modulo 2^w".
    Re-exports `UScalar.wrapping_add_val_eq`. -/
@[simp]
theorem wadd_val {ty : UScalarTy} (x y : UScalar ty) :
    (wadd x y).val = (x.val + y.val) % (UScalar.size ty) :=
  UScalar.wrapping_add_val_eq x y

/-- **Spec lemma (`wadd_comm`)**: modular addition is commutative:
    `wadd x y = wadd y x`.
    Proof: `x.bv + y.bv = y.bv + x.bv` by commutativity of `BitVec` addition. -/
theorem wadd_comm {ty : UScalarTy} (x y : UScalar ty) :
    wadd x y = wadd y x := by
  rw [UScalar.eq_equiv_bv_eq]
  simp only [wadd_bv_eq]
  ring

/-- **Spec lemma (`wadd_assoc`)**: modular addition is associative:
    `wadd (wadd x y) z = wadd x (wadd y z)`.
    Proof: associativity of `BitVec` addition. -/
theorem wadd_assoc {ty : UScalarTy} (x y z : UScalar ty) :
    wadd (wadd x y) z = wadd x (wadd y z) := by
  rw [UScalar.eq_equiv_bv_eq]
  simp only [wadd_bv_eq]
  ring

end spec.sha
