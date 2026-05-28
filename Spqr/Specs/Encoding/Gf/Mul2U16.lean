/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.Unaccelerated.Mul2

/-!
# Spec theorem for `encoding::gf::mul2_u16`

In the Rust source this function performs runtime CPU-feature dispatch: on x86/x86_64/aarch64 it may
delegate to a hardware-accelerated carry-less multiplication kernel (`accelerated::mul2`); otherwise
it falls back to running `unaccelerated::mul` twice with the shared left operand.  After Aeneas
extraction, all branches collapse to the single software definition

  `mul2_u16 a b1 b2 = unaccelerated.mul2 a b1 b2`

so the postcondition is inherited verbatim from `mul2_spec'` / `mul2_spec` in
`Spqr.Specs.Encoding.Gf.Unaccelerated.Mul2`.

**Source**: spqr/src/encoding/gf.rs (lines 581:0-590:1)
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf.unaccelerated
open spqr.math.gf

namespace spqr.encoding.gf

/--
**Polynomial-level postcondition for `encoding.gf.mul2_u16`**:

`mul2_u16 a b1 b2` performs two independent GF(2¹⁶) multiplications that share the left operand `a`.
Each component of the returned pair satisfies the polynomial-level specification of `mul`:

  `natToBinaryPoly result.1.val =
     (natToBinaryPoly a.val * natToBinaryPoly b1.val) %ₘ polyGF2`
  `natToBinaryPoly result.2.val =
     (natToBinaryPoly a.val * natToBinaryPoly b2.val) %ₘ polyGF2`

After extraction, `mul2_u16` reduces definitionally to `unaccelerated.mul2`, so the claim follows
immediately from `mul2_spec'`.

**Source**: spqr/src/encoding/gf.rs (lines 581:0-590:1)
-/
theorem mul2_u16_spec' (a b1 b2 : U16) :
    mul2_u16 a b1 b2 ⦃ result =>
      natToBinaryPoly result.1.val =
        (natToBinaryPoly a.val * natToBinaryPoly b1.val) %ₘ polyGF2 ∧
      natToBinaryPoly result.2.val =
        (natToBinaryPoly a.val * natToBinaryPoly b2.val) %ₘ polyGF2 ⦄ := by
  unfold mul2_u16
  have h := unaccelerated.mul2_spec_poly a b1 b2
  step*

/--
**GF216-level postcondition (provable, parametric)**:

For any ring-homomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` that vanishes on `polyGF2`,
both components of `mul2_u16 a b1 b2` correspond — via `BinaryPoly.toGF216 ∘ natToBinaryPoly` — to
the products `a · b1` and `a · b2` in `GF216`.

Specialising `BinaryPoly.toGF216` to the canonical isomorphism (whose construction requires
irreducibility of `polyGF2` over `ZMod 2`, i.e. a finite- field development we omit here) recovers
the GF(2¹⁶) interpretation of the result.
-/
@[step]
theorem mul2_u16_spec (a b1 b2 : U16) :
    mul2_u16 a b1 b2 ⦃ result =>
      result.1.val.toGF216 = a.val.toGF216 * b1.val.toGF216 ∧
      result.2.val.toGF216 = a.val.toGF216 * b2.val.toGF216 ⦄ := by
  unfold mul2_u16
  have h := unaccelerated.mul2_spec a b1 b2
  step*

end spqr.encoding.gf
