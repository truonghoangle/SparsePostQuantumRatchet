/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::proto::pq_ratchet::{impl core::clone::Clone for PolynomialDecoder}::clone`

`PolynomialDecoder` is the protobuf-generated product (record) type

  `PolynomialDecoder ≃ { pts_needed : u32 ; polys : u32 ; pts : Vec<Vec<u8>> ; is_complete : bool }`

representing the serialised form of a polynomial decoder's state.  The four fields are:
  • `pts_needed : u32` — the number of evaluation points still needed before decoding can complete.
  • `polys : u32` — the number of polynomials accumulated so far.
  • `pts : Vec<Vec<u8>>` — the list of serialised evaluation points (`repeated bytes` in proto3).
  • `is_complete : bool` — whether enough points have been received for decoding.

The protobuf schema (src/proto/pq_ratchet.proto, lines 18–23):
  ```proto
  message PolynomialDecoder {
    uint32 pts_needed = 1;
    uint32 polys = 2;
    repeated bytes pts = 3;
    bool is_complete = 4;
  }
  ```

The prost-generated Rust struct carries a `#[derive(Clone)]`, producing:
  ```rust
  // Compiler-derived impl from #[derive(Clone)]
  impl Clone for PolynomialDecoder {
      fn clone(&self) -> Self {
          PolynomialDecoder {
              pts_needed: Clone::clone(&self.pts_needed),
              polys: Clone::clone(&self.polys),
              pts: Clone::clone(&self.pts),
              is_complete: Clone::clone(&self.is_complete),
          }
      }
  }
  ```

The compiler-derived `Clone::clone` implementation proceeds field-by-field:
  1. `CloneU32.clone` for `pts_needed` (identity on `u32`).
  2. `CloneU32.clone` for `polys` (identity on `u32`).
  3. `CloneVec.clone (CloneallocvecVec CloneU8)` for `pts` (nested identity clone on
     `Vec<Vec<u8>>`).
  4. `CloneBool.clone` for `is_complete` (identity on `bool`).

Because `u32` is `Copy`, `bool` is `Copy`, and `u8` is `Copy` — and their derived `Clone::clone`
returns the argument unchanged — the inner `Vec<u8>` clone is the identity, which in turn makes the
outer `Vec<Vec<u8>>` clone the identity.  Therefore the whole struct-level clone is observationally
the identity:
  `clone(self) = ok self`

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 14:9-14:14)
-/

open Aeneas Aeneas.Std Result

namespace spqr.proto.pq_ratchet.PolynomialDecoder

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
**Spec theorem for `proto.pq_ratchet.PolynomialDecoder.Insts.CoreCloneClone.clone`**:

• Takes a `PolynomialDecoder` value `self` wrapping four fields:
    - `pts_needed : U32` — the number of evaluation points still needed.
    - `polys : U32` — the number of accumulated polynomials.
    - `pts : Vec (Vec U8)` — serialised evaluation points.
    - `is_complete : Bool` — whether decoding is complete.
• Delegates to field-wise cloning:
    - `core.clone.impls.CloneU32.clone` for `pts_needed` and `polys` (identity on `U32`).
    - `alloc.vec.CloneVec.clone (CloneallocvecVec CloneU8)` for `pts`
      (nested identity clone on `Vec (Vec U8)` — see `clone_vec_vec_u8_spec`).
    - `core.clone.impls.CloneBool.clone` for `is_complete` (identity on `Bool`).
• Returns the resulting `PolynomialDecoder` unchanged.

The Aeneas-extracted Lean definition (SrcTranslated/Funs.lean, lines 326–339):
  ```lean
  def proto.pq_ratchet.PolynomialDecoder.Insts.CoreCloneClone.clone
    (self : proto.pq_ratchet.PolynomialDecoder) :
    Result proto.pq_ratchet.PolynomialDecoder := do
    let i ← lift (core.clone.impls.CloneU32.clone self.pts_needed)
    let i1 ← lift (core.clone.impls.CloneU32.clone self.polys)
    let v ←
      alloc.vec.CloneVec.clone (core.clone.CloneallocvecVec core.clone.CloneU8)
        self.pts
    let b ← lift (core.clone.impls.CloneBool.clone self.is_complete)
    ok { pts_needed := i, polys := i1, pts := v, is_complete := b }
  ```

• The function always succeeds (no panic / no error) for any `PolynomialDecoder` input, since
  `CloneU32.clone` and `CloneBool.clone` are total and each nested `Vec<u8>` clone is total
  (element-wise `CloneU8.clone` is the identity on bounded integers).
• The result is propositionally equal to the input:
    `clone(self) = ok self`
  i.e. the derived `Clone` implementation is observationally the identity on `PolynomialDecoder`.

The result satisfies the value-level specification:

  `result = self`

The proof unfolds `clone`, simplifies the trivial `CloneU32.clone` / `CloneBool.clone` / `lift`,
and discharges the `Vec<Vec<u8>>` field clone via `step*` using the already-registered
`clone_vec_vec_u8_spec`.

**Source**: target/out/signal.proto.pq_ratchet.rs (lines 14:9-14:14)
-/
@[step]
theorem clone_spec (self : proto.pq_ratchet.PolynomialDecoder) :
    Insts.CoreCloneClone.clone self ⦃ (result : proto.pq_ratchet.PolynomialDecoder) =>
      result = self ⦄ := by
  unfold Insts.CoreCloneClone.clone
  simp only [core.clone.impls.CloneU32.clone]
  simp only [core.clone.impls.CloneBool.clone]
  simp only [lift]
  step*
  rw [v_post]

end spqr.proto.pq_ratchet.PolynomialDecoder
