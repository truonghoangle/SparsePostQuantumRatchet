/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf2Poly.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Generic monic-polynomial utilities

A generic lemma `ringHom_modByMonic` that says any ring homomorphism vanishing on a monic polynomial
`P` commutes with reduction modulo `P`.
-/

open Polynomial

namespace spqr.math.gf

lemma ringHom_modByMonic
    {R : Type*} [CommRing R]
    (φ : BinaryPoly →+* R)
<<<<<<< HEAD
    (P : BinaryPoly)
    (hφ : φ P = 0)
    (p : BinaryPoly) :
    φ (p %ₘ P) = φ p := by
  have heq : p %ₘ P + P * (p /ₘ P) = p :=
    Polynomial.modByMonic_add_div p P
=======
    (P : BinaryPoly) (hφ : φ P = 0)
    (p : BinaryPoly) :
    φ (p %ₘ P) = φ p := by
  have heq : p %ₘ P + P * (p /ₘ P) = p := Polynomial.modByMonic_add_div p _
>>>>>>> e4dda3b02fc166a9b012a800b9b2d1b54c6ac089
  have h1 : φ p = φ (p %ₘ P + P * (p /ₘ P)) := by rw [heq]
  have h2 :
      φ (p %ₘ P + P * (p /ₘ P)) = φ (p %ₘ P) + φ P * φ (p /ₘ P) := by
    simp [map_add, map_mul]
  rw [h1, h2, hφ]; ring

end spqr.math.gf
