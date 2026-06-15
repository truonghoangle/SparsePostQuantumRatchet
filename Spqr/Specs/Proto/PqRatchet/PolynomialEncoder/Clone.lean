/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl core::clone::Clone for PolynomialEncoder}::clone`

`PolynomialEncoder` is the protobuf-generated product (record) type

  `PolynomialEncoder ≃ { idx : u32 ; pts : Vec<Vec<u8>> ; polys : Vec<Vec<u8>> }`

representing the serialised form of a polynomial encoder's state.  The three fields are:
  • `idx : u32` — the current index in the encoding sequence.
  • `pts : Vec<Vec<u8>>` — the list of serialised evaluation points (`repeated bytes` in proto3).
  • `polys : Vec<Vec<u8>>` — the list of serialised polynomials (`repeated bytes` in proto3).

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneU32.clone` for `idx` (identity on `u32`).
  2. `CloneVec.clone (CloneallocvecVec CloneU8)` for `pts` (nested identity clone on
     `Vec<Vec<u8>>`).
  3. `CloneVec.clone (CloneallocvecVec CloneU8)` for `polys` (same nested identity clone).

Because `u8` is `Copy` — and its derived `Clone::clone` returns the argument unchanged — the
inner `Vec<u8>` clone is the identity, which in turn makes the outer `Vec<Vec<u8>>` clone the
identity.  Therefore the whole struct-level clone is observationally the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 2:9-2:14)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.PolynomialEncoder

/-- `Vec<u8>` clone is the identity.

Because `u8` is `Copy`, its derived `Clone::clone` returns the argument unchanged.  The list-level
`Slice.clone` with the identity element-clone is therefore the identity, and
`alloc.vec.CloneVec.clone` wraps this in a `Vec`. -/
@[step]
private lemma clone_vec_u8_spec (v : alloc.vec.Vec Std.U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v
      ⦃ (r : alloc.vec.Vec Std.U8) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => by simp))
  intro v' h
  exact h.symm

/-- `Vec<u8>` clone returns its argument unchanged (equality form).

This is the equality-level corollary of `clone_vec_u8_spec`, extracted via `WP.spec_imp_exists` for
use in `Slice.clone_spec` proofs at the `Vec<Vec<u8>>` level. -/
private lemma clone_vec_u8_id (x : alloc.vec.Vec Std.U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 x = ok x := by
  obtain ⟨r, hr, heq⟩ := WP.spec_imp_exists (clone_vec_u8_spec x)
  subst heq; exact hr

/-- `Vec<Vec<u8>>` clone is the identity.

The outer-level `Slice.clone` delegates to the `Vec<u8>` clone (via the
`core.clone.CloneallocvecVec core.clone.CloneU8` trait instance) for each element.  Since each
element-wise clone is the identity (`clone_vec_u8_id`), the outer clone is the identity as well. -/
@[step]
private lemma clone_vec_vec_u8_spec (v : alloc.vec.Vec (alloc.vec.Vec Std.U8)) :
    alloc.vec.CloneVec.clone (core.clone.CloneallocvecVec core.clone.CloneU8) v
      ⦃ (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => clone_vec_u8_id x))
  intro v' h
  exact h.symm

/--
**Spec theorem for `proto.pq_ratchet.PolynomialEncoder.Insts.CoreCloneClone.clone`**:

• Takes a `PolynomialEncoder` value `self` wrapping three fields:
    - `idx : U32` — the encoding index.
    - `pts : Vec (Vec U8)` — serialised evaluation points.
    - `polys : Vec (Vec U8)` — serialised polynomials.
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneU32.clone` for `idx` (identity on `U32`).
    - `alloc.vec.CloneVec.clone (CloneallocvecVec CloneU8)` for `pts` and `polys`
      (nested identity clone on `Vec (Vec U8)` — see `clone_vec_vec_u8_spec`).
• Returns the resulting `PolynomialEncoder` unchanged.

• The function always succeeds (no panic / no error) for any `PolynomialEncoder` input, since
  `CloneU32.clone` is total and each nested `Vec<u8>` clone is total (element-wise `CloneU8.clone`
  is the identity on bounded integers).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `PolynomialEncoder`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneU32.clone` / `lift`, and discharges the
two `Vec<Vec<u8>>` field clones via `step*` using the already-registered `clone_vec_vec_u8_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 2:9-2:14)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.PolynomialEncoder) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneU32.clone]
  simp only [lift]
  step*
  rw [v_post, v1_post]

end spqr.proto.pq_ratchet.PolynomialEncoder
