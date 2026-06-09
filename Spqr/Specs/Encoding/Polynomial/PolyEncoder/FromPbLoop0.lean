/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPbLoopBody0

/-!
# Spec theorem for `PolyEncoder::from_pb`: loop 0

The extracted Lean function `encoding.polynomial.PolyEncoder.from_pb_loop0` is the outer
polynomial-deserialization loop inside `PolyEncoder::from_pb`.  Given the protobuf index `i`
(of type `U32`), the vector of serialized byte vectors `v` (corresponding to `pb.polys`), a
`Range<usize>` iterator over `0..NUM_POLYS`, and the current output array of 16 `Poly` values,
the loop repeatedly invokes `encoding.polynomial.PolyEncoder.from_pb_loop0.body`, which at each
step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current index `j`.
  2. Retrieves the `j`-th serialized byte vector from `v`.
  3. Deserializes it into a `Poly` via `Poly::deserialize`.
  4. Updates `out[j]` with the deserialized polynomial.

**Loop invariant**: after processing iterations up to `iter'`, the output array of `Poly` values
satisfies:

  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * `iter'.start.val ≤ iter'.«end».val` — the start never exceeds the end.
  * For every `j ∈ [0, iter'.start.val)`, the `j`-th entry is the deserialized form of the `j`-th
    serialized byte vector from `v`:
      `∃ poly, out'.val[j]! = poly ∧
        poly.coefficients.val.length = (v.val[j]!).val.length / 2 ∧
        ∀ k < (v.val[j]!).val.length / 2,
          ∃ g, poly.coefficients.val[k]? = some g ∧
            g.value.val = (v.val[j]!).val[2*k]!.val * 256 + (v.val[j]!).val[2*k+1]!.val`

At loop termination (`iter'.start.val ≥ iter'.«end».val`), the output array contains the
complete deserialization of all polynomials in `v[0..iter.«end».val]`, and the result is
`Ok(PolyEncoder { idx := i, s := EncoderState::Polys(out) })`.

Each deserialized polynomial satisfies the big-endian byte-decoding invariant: for each
coefficient index `k`, the coefficient's `u16` value equals
  `serialized[2*k] * 256 + serialized[2*k+1]`
where `serialized` is the byte vector `v[j]`.

The body spec (`body_spec` from `FromPbLoopBody0.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`, and the big-endian
decoding satisfies `value = hi * 256 + lo` where `hi` and `lo` are the high and low bytes
respectively.

**Source**: spqr/src/encoding/polynomial.rs (lines 614:12-617:72)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop0

/-! ## Inhabited instance -/

/--
`Poly` wraps a `Vec<GF16>` of coefficients.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on arrays/lists of `Poly` has a well-defined default value.  We use the empty
coefficient vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Poly := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Spec theorem for the from_pb outer deserialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop0`**:

The full outer deserialization loop inside `PolyEncoder::from_pb`.  Given the protobuf index
`i`, the vector of serialized byte vectors `v` (from `pb.polys`), a range iterator `iter` over
indices, and the current output array of 16 `Poly` values, the loop drives the body to
completion and returns the wrapped `PolyEncoder`.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed the vector length or the array size (16), each serialized byte vector is
  non-empty, has even length, and can be deserialized without overflow, and the pre-existing
  entries in the output array already satisfy the deserialization invariant.

• **Loop postcondition**:
  - The result wraps a `PolyEncoder` containing the fully deserialized polynomial array:
      `result = Ok { idx := i, s := Polys out' }`
  - For every `j < iter.«end».val`, the `j`-th polynomial in the output array satisfies the
    big-endian byte-decoding invariant from `v[j]`:
      `∃ poly, out'.val[j]! = poly ∧
        poly.coefficients.val.length = (v.val[j]!).val.length / 2 ∧
        ∀ k < (v.val[j]!).val.length / 2,
          ∃ g, poly.coefficients.val[k]? = some g ∧
            g.value.val = (v.val[j]!).val[2*k]!.val * 256 + (v.val[j]!).val[2*k+1]!.val`

    This corresponds to the Rust loop:
    ```rust
    for i in 0..NUM_POLYS {
        out[i] = Poly::deserialize(&pb.polys[i])?;
    }
    ```

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.«end».val − iter'.start.val`, maintaining the polynomial-deserialization invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 614:12-617:72)
-/
@[step]
theorem loop_spec
    (i : Std.U32)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (iter : core.ops.range.Range Std.Usize)
    (out : Array encoding.polynomial.Poly 16#usize)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_nonempty : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length ≠ 0)
    (h_even : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length % 2 = 0)
    (h_overflow : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length / 2 + 1 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        ∃ (poly : encoding.polynomial.Poly),
          out.val[j]! = poly ∧
          poly.coefficients.val.length =
            (v.val[j]!).val.length / 2 ∧
          ∀ (k : Nat),
            k < (v.val[j]!).val.length / 2 →
            ∃ (g : encoding.gf.GF16),
              poly.coefficients.val[k]? = some g ∧
              g.value.val =
                ((v.val[j]!).val[2 * k]!).val * 256 +
                ((v.val[j]!).val[2 * k + 1]!).val) :
    from_pb_loop0 iter i v out ⦃ (result : core.result.Result
        encoding.polynomial.PolyEncoder encoding.polynomial.PolynomialError) =>
      ∃ (out' : Array encoding.polynomial.Poly 16#usize),
        result = core.result.Result.Ok
          { idx := i, s := encoding.polynomial.EncoderState.Polys out' } ∧
        ∀ (j : Nat), j < iter.«end».val →
          ∃ (poly : encoding.polynomial.Poly),
            out'.val[j]! = poly ∧
            poly.coefficients.val.length =
              (v.val[j]!).val.length / 2 ∧
            ∀ (k : Nat),
              k < (v.val[j]!).val.length / 2 →
              ∃ (g : encoding.gf.GF16),
                poly.coefficients.val[k]? = some g ∧
                g.value.val =
                  ((v.val[j]!).val[2 * k]!).val * 256 +
                  ((v.val[j]!).val[2 * k + 1]!).val ⦄ := by
  unfold from_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                       Array encoding.polynomial.Poly 16#usize) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     Array encoding.polynomial.Poly 16#usize) =>
        let iter' := p.1
        let out' := p.2
        iter'.«end» = iter.«end» ∧
        iter'.start.val ≤ iter'.«end».val ∧
        (∀ (j : Nat), j < iter'.start.val →
          ∃ (poly : encoding.polynomial.Poly),
            out'.val[j]! = poly ∧
            poly.coefficients.val.length =
              (v.val[j]!).val.length / 2 ∧
            ∀ (k : Nat),
              k < (v.val[j]!).val.length / 2 →
              ∃ (g : encoding.gf.GF16),
                poly.coefficients.val[k]? = some g ∧
                g.value.val =
                  ((v.val[j]!).val[2 * k]!).val * 256 +
                  ((v.val[j]!).val[2 * k + 1]!).val))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_pre'⟩
    simp only [] at h_end' h_start_le' h_pre' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_body := body_spec i v iter' out' (by omega) (by omega) h_nonempty h_even h_overflow
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done result =>
      simp only [] at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      exact ⟨out', rfl, fun j hj => h_pre' j (by omega)⟩
    | ControlFlow.cont (iter'', out'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, poly, h_out_eq, h_out_preserve, h_poly_len, h_poly_encode⟩ := h_cf
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_end1]; exact h_end',
               by grind,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · -- Previously processed: j is in the prefix
          obtain ⟨poly', h_eq', h_len', h_enc'⟩ := h_pre' j hj_lt
          exact ⟨poly', (h_out_preserve j (by omega)).trans h_eq', h_len', h_enc'⟩
        · -- Newly processed: j = iter'.start.val
          have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          exact ⟨poly, h_out_eq, h_poly_len, h_poly_encode⟩
      · -- Measure decreases
        grind
  · -- Initial state satisfies the invariant
    exact ⟨rfl, h_start_le, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop0
