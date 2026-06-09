/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.Poly.Serialize
import Spqr.Specs.Aeneas.SliceIteratorNext

/-!
# Spec theorem for `PolyEncoder::into_pb`: loop body 2

In the `EncoderState::Polys` branch of `PolyEncoder::into_pb`, a slice iterator is used to
traverse the array of 16 `Poly` values.  Each polynomial's coefficient vector (a list of GF(2¹⁶)
elements stored as `u16` values) is serialized into a byte vector, and the result is pushed onto
the output protobuf vector.

The extracted Lean function `encoding.polynomial.PolyEncoder.into_pb_loop1.body` performs one step
of this polynomial-serialization loop.  Given a slice iterator over `Poly` values and the current
output vector of byte vectors `v`, the body calls `next` on the slice iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the output vector `v` is returned unchanged.
  2. **Continue** (`some poly`): serializes the polynomial's GF(2¹⁶) coefficient vector into a
     byte vector via `Poly::serialize`, and pushes the resulting byte vector onto `v`.

The function proceeds in two stages:
  1. `core.slice.iter.IteratorSliceIter.next iter` — advances the slice iterator, yielding the
     next `Poly` from the underlying slice (at position `iter.i`) or `none` if the iterator is
     exhausted (`iter.i ≥ iter.slice.val.length`).
  2. `encoding.polynomial.Poly.serialize poly` — serializes the polynomial's coefficient vector
     into a big-endian byte vector (each GF(2¹⁶) coefficient encoded as two bytes
     `hi * 256 + lo = value`), followed by `alloc.vec.Vec.push` to append the result.

**Source**: spqr/src/encoding/polynomial.rs (lines 565:16-567:17)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop1

/-! ## Inhabited instance for `Poly` -/

/--
`Poly` wraps a `Vec<GF16>` of coefficients.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on lists of `Poly` has a well-defined default value.  We use the empty
coefficient vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Poly := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Spec theorem for the into_pb polynomial-serialization loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop1.body`**:

One step of the polynomial-serialization loop inside `PolyEncoder::into_pb` (the
`EncoderState::Polys` branch).  Given the slice iterator `iter` over the polynomial array and the
current output vector of serialized byte vectors `v`, the body retrieves the next polynomial from
the iterator and either terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the output vector
  has room for one more entry without exceeding `Usize.max`, and each polynomial's GF(2¹⁶)
  coefficient vector can be serialized without overflow.

• In the **done** case (iterator exhausted):
    the output vector `v` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.i < iter.slice.val.length)`.

• In the **cont** case (received polynomial `poly = iter.slice.val[iter.i]` from the iterator):
    - `iter.i < iter.slice.val.length` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.i = iter.i + 1`,
        `iter1.slice = iter.slice`.
    - The output vector is extended by exactly one entry — the serialized byte vector for the
      polynomial's GF(2¹⁶) coefficients:
        `v1.val = v.val ++ [serialized]`
      where `serialized` is the result of `Poly.serialize` applied to `poly`, satisfying:
        `serialized.val.length = 2 * poly.coefficients.val.length`
      and for every `k < poly.coefficients.val.length`:
        `∃ hi lo, serialized.val[2*k]? = some hi ∧ serialized.val[2*k+1]? = some lo ∧
          hi.val * 256 + lo.val = (poly.coefficients.val[k]!).value.val`

    This corresponds to the Rust body:
    ```rust
    for poly in polys.iter() {
        out.polys.push(poly.serialize());
    }
    ```

The result satisfies the polynomial-level serialization specification:
  `natToBinaryPoly (hi.val * 256 + lo.val)` recovers each coefficient's GF(2¹⁶) representation.

This follows from composing:
  1. `IteratorSliceIter.next` spec: the slice iterator either yields the element at the current
     position and advances the cursor, or signals exhaustion.
  2. `Poly.serialize_spec`:
       `serialize poly` produces a byte vector encoding all coefficients in big-endian format.

**Source**: spqr/src/encoding/polynomial.rs (lines 565:16-567:17)
-/
@[step]
theorem body_spec
    (iter : core.slice.iter.Iter encoding.polynomial.Poly)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (h_out_overflow : v.val.length + 1 ≤ Usize.max)
    (h_ser_overflow : ∀ (j : Nat), j < iter.slice.val.length →
        2 * (iter.slice.val[j]!).coefficients.val.length + 2 ≤ Usize.max) :
    body iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.i < iter.slice.val.length)
      | ControlFlow.cont (iter1, v1) =>
          iter.i < iter.slice.val.length ∧
          iter1.i = iter.i + 1 ∧
          iter1.slice = iter.slice ∧
          ∃ (serialized : alloc.vec.Vec Std.U8),
            v1.val = v.val ++ [serialized] ∧
            serialized.val.length =
              2 * (iter.slice.val[iter.i]!).coefficients.val.length ∧
            ∀ (k : Nat),
              k < (iter.slice.val[iter.i]!).coefficients.val.length →
              ∃ (hi lo : Std.U8),
                serialized.val[2 * k]? = some hi ∧
                serialized.val[2 * k + 1]? = some lo ∧
                hi.val * 256 + lo.val =
                  ((iter.slice.val[iter.i]!).coefficients.val[k]!).value.val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.slice.iter.IteratorSliceIter.next_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.i < iter.slice.val.length
  · obtain ⟨h_opt_eq, h_i1, h_slice1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_ser := h_ser_overflow iter.i h_lt
    have h_getelem : (iter.slice.val[iter.i]! : encoding.polynomial.Poly) =
        iter.slice.val[iter.i]'h_lt := by
      rw [← List.Inhabited_getElem_eq_getElem! (hi := h_lt)]
    rw [h_getelem] at h_ser ⊢
    step*
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop1
