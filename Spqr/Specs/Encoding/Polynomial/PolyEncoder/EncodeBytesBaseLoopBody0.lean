/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.New

/-!
# Spec theorem for `PolyEncoder::encode_bytes_base`: loop body 0

In the polynomial encoding scheme, message bytes are distributed round-robin across `NUM_POLYS = 16`
evaluation-data arrays (`Point` values).  Each pair of consecutive message bytes `(c[0], c[1])` is
interpreted as a big-endian 16-bit value and converted to a GF(2¹⁶) element via `GF16::new`.  The
resulting element is appended to `pts[i % 16].value`, where `i` is the enumeration index of the
2-byte chunk in the `chunks_exact(2)` iteration over the message.

The function proceeds in two stages:
  1. Iterator advance — `next` is called on the `Enumerate<ChunksExact<u8>>` iterator, yielding
     either `none` (exhausted) or `some (i, c)` where `c` is a 2-byte slice.
  2. Point update — in the `some` case, the index `poly = i % pts.len()` (= `i % 16`) selects the
     target point, and the big-endian decode
     `g := GF16::new(((c[0] as u16) << 8) + (c[1] as u16))` is pushed onto `pts[poly].value`.

In GF(2¹⁶) (characteristic 2), the 16-bit big-endian value `c[0] * 256 + c[1]` represents a
polynomial of degree < 16 with coefficients in GF(2), and `GF16::new` packages it as the canonical
representative in GF(2¹⁶) ≅ GF(2)[X] / (x¹⁶ + x¹² + x³ + x + 1).

**Source**: spqr/src/encoding/polynomial.rs (lines 679:8-686:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop

/-! ## Inhabited instances -/

/--
`Point` wraps a `Vec<GF16>`.  An `Inhabited` instance is required so that `getElem!` (`[·]!`)
on arrays/lists of `Point` has a well-defined default value.  We use the empty value vector
as the canonical default.
-/
instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩


/-- **Spec theorem for `encode_bytes_base_loop.body`** (nat-level):

Big-endian decoding of a 2-byte chunk into a GF(2¹⁶) element, followed by round-robin distribution
into the `pts` array.  This is the raw numerical version: the postcondition expresses the GF16
element's underlying `u16` value as the big-endian decode of the byte pair.

The result satisfies the nat-level specification:
  • **done**: `pts' = pts` — the point array is returned unchanged when the iterator is exhausted.
  • **cont**: there exist `(i, c)` from the iterator and a `GF16` element `g` such that
      `g.toGF216 = ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216`
    and `pts'` is obtained from `pts` by pushing `g` onto `pts[i % 16].value`.

This follows from composing:
  1. `Enumerate<ChunksExact<u8>>.next` — yielding the enumeration pair `(i, c)`.
  2. `Slice.index_usize c 0`, `Slice.index_usize c 1` — extracting the two bytes.
  3. `UScalar.cast .U16`, `<<< 8`, `+` — big-endian assembly into a `u16`.
  4. `GF16::new` (`new_spec`): the GF(2¹⁶) element wraps the big-endian value.
  5. `Vec::push` — appending `g` to `pts[i % 16].value`.

**Source**: spqr/src/encoding/polynomial.rs (lines 679:8-686:9)
-/
theorem body_spec_nat
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact Std.U8))
    (pts : Array encoding.polynomial.Point 16#usize)
    (h_push_ok : ∀ (j : Nat), j < 16 →
        (pts.val[j]!).value.val.length + 1 ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.val.length ≥ 2) :
    body iter pts ⦃ cf =>
      match cf with
      | ControlFlow.done pts' =>
          pts' = pts
      | ControlFlow.cont (iter', pts') =>
          ∃ (i : Usize) (c : Slice U8) (g : GF16),
            c.val.length ≥ 2 ∧
            g.toGF216 =
              ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216 ∧
            let poly := i.val % 16
            pts'.val[poly]!.value.val =
              (pts.val[poly]!).value.val ++ [g] ∧
            (∀ k, k ≠ poly → pts'.val[k]! = pts.val[k]!) ⦄ := by
  unfold body
  simp only [
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next_spec,
    core.iter.traits.iterator.IteratorChunksExact,
    core.slice.iter.IteratorChunksExact.next]
  split
  · -- nil case: iterator exhausted → done pts = pts
    simp [WP.spec_ok]
  · -- cons case: iterator yields (count, chunk)
    rename_i hd tl rest
    simp only [bind_tc_ok, uncurry_apply_pair]
    have h_c_len : hd.val.length ≥ 2 :=
      h_chunks_len hd (by rw [rest]; exact .head _)
    step*
    · simp_all
      grind
    refine ⟨iter.count, hd, g, ?_, ?_, ?_, ?_⟩
    · exact h_c_len
    · -- toGF216 equation: <<< 8 % U16.size = 256 * for U8 values
      conv_lhs =>
        simp[g_post,i7_post,i4_post1,i6_post, i3_post, i2_post, i5_post]
      congr
      · rw[Nat.shiftLeft_eq]
        simp only [Nat.reducePow]
        have :(↑(hd)[0] * 256) < U16.size := by scalar_tac
        have := Nat.mod_eq_of_lt this
        grind
      · grind
    · -- push equation: set then get at same index
      simp_all
      grind
    · intro k hk
      simp_all

/--
For any big-endian byte pair `(c[0], c[1])` yielded by the enumerate-chunks iterator, the GF(2¹⁶)
element `g` appended to `pts[i % 16].value` in the `cont` case satisfies:

  `g.toGF216 = ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216`

Specializing the canonical isomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` recovers the
GF(2¹⁶) interpretation: the byte pair `(c[0], c[1])` encodes a field element whose binary
polynomial representation has `c[0]` in bits 15–8 and `c[1]` in bits 7–0.

Combining with `body_spec_nat`, this establishes that each loop step correctly inserts the GF(2¹⁶)
interpretation of the big-endian 2-byte chunk into the round-robin–selected evaluation-data array.
-/
@[step]
theorem body_spec
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact Std.U8))
    (pts : Array encoding.polynomial.Point 16#usize)
    (h_push_ok : ∀ (j : Nat), j < 16 →
        (pts.val[j]!).value.val.length + 1 ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.val.length ≥ 2) :
    body iter pts ⦃ cf =>
      match cf with
      | ControlFlow.done pts' =>
          pts' = pts
      | ControlFlow.cont (iter', pts') =>
          ∃ (i : Usize) (c : Slice U8) (g : GF16),
            c.val.length ≥ 2 ∧
            g.toGF216 =
              ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216 ∧
            let poly := i.val % 16
            pts'.val[poly]!.value.val =
              (pts.val[poly]!).value.val ++ [g] ∧
            (∀ k, k ≠ poly → pts'.val[k]! = pts.val[k]!) ⦄ := by
  exact body_spec_nat iter pts h_push_ok h_chunks_len

end spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop
