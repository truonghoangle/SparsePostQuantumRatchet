/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.ModByMonic
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPbLoop1
import Spqr.Specs.Aeneas.SliceIteratorNext

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::into_pb`: loop body 0

The extracted Lean function `encoding.polynomial.PolyDecoder.into_pb_loop0.body` performs one
step of the *outer* point-set-serialization loop inside `PolyDecoder::into_pb`.  Given a slice
iterator over `SortedSet<Pt>` values — each representing a sorted set of cartesian evaluation
points over GF(2¹⁶) × GF(2¹⁶) — and the current output vector of serialized byte vectors `v`,
the body calls `next` on the slice iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the output vector `v` is returned
     unchanged.
  2. **Continue** (`some pts`): dereferences the `SortedSet<Pt>` `pts` twice (through
     `SortedSet → SortedVec → Vec<Pt>`) to obtain the underlying point vector `inner`,
     serializes all cartesian points in `inner` into a freshly allocated byte vector using the
     inner point-serialization loop (`into_pb_loop0_loop0`), and pushes that byte vector onto
     the back of `v`.

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.
A cartesian point `Pt = (x, y)` packs two such elements; its 4-byte big-endian serialization
satisfies the encoding invariant
  `b0·256 + b1 = pt.x.value`,
  `b2·256 + b3 = pt.y.value`.

The body proceeds in three stages:
  1. `IteratorSliceIter.next` — advances the slice iterator over `SortedSet<Pt>` elements.
  2. Double `deref` (`SortedSet → SortedVec → Vec<Pt>`, opaque axioms) — exposes the underlying
     `inner : Vec<Pt>`.
  3. `into_pb_loop0_loop0.loop_spec` — drives the inner serialization loop, producing a byte
     vector of length `4 · inner.len()` whose `4k..4k+4` chunk encodes
     `(inner[k].x, inner[k].y)` big-endian; then `Vec.push` appends this byte vector to `v`.

Because both `SortedSet → SortedVec` and `SortedVec → Vec` deref operations are extracted as
opaque axioms (`sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref` and
`sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref`), we parameterise the spec by the
hypothetical witnesses `sv` and `inner` together with the `h_sv` and `h_inner` hypotheses
asserting that they are indeed the deref results at the current slot.

**Source**: spqr/src/encoding/polynomial.rs (lines 800:8-809:9)
-/

open Aeneas Aeneas.Std Result spqr.math.gf spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0

/-! ## Inhabited instance for `Pt` -/

/--
`Pt` wraps two `GF16` values `(x, y)`.  An `Inhabited` instance is required so that `getElem!`
(`[·]!`) on lists of `Pt` has a well-defined default value.  We use the zero point as the
canonical default.
-/
instance : Inhabited Pt :=
  ⟨{ x := ⟨0#u16⟩, y := ⟨0#u16⟩ }⟩

/-! ## Spec theorems for the into_pb outer loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0.body`** (byte-level):

One step of the outer serialization loop inside `PolyDecoder::into_pb`.  Given a slice iterator
over `SortedSet<Pt>` values and the current output vector of serialized byte vectors `v`, the
body retrieves the next `SortedSet<Pt>` from the slice iterator and either terminates or
extends the output by exactly one entry whose contents are the big-endian byte serialization
of the cartesian points in the corresponding `inner : Vec<Pt>`.

• In the **done** case (iterator exhausted):
    the output vector `v` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.i < iter.slice.val.length)`.

• In the **cont** case (received `pts = iter.slice[iter.i]` from the slice iterator):
    - `iter.i < iter.slice.val.length` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.i = iter.i + 1`,
        `iter1.slice = iter.slice`.
    - The output vector is extended by exactly one entry — the serialized byte vector for the
      cartesian points in `inner` (the double-deref of `pts`):
        `v1.val = v.val ++ [serialized]`
      with
        `serialized.val.length = 4 * inner.val.length`
      and for every `k < inner.val.length`:
        `∃ b0 b1 b2 b3,
           serialized.val[4*k]?   = some b0 ∧ serialized.val[4*k+1]? = some b1 ∧
           serialized.val[4*k+2]? = some b2 ∧ serialized.val[4*k+3]? = some b3 ∧
           b0.val · 256 + b1.val = (inner.val[k]!).x.value.val ∧
           b2.val · 256 + b3.val = (inner.val[k]!).y.value.val`.

This follows from composing:
  1. `IteratorSliceIter.next_post`: advance the slice iterator over `SortedSet<Pt>` elements.
  2. The opaque double-deref witnesses `h_sv` and `h_inner` to expose the underlying point
     vector `inner` of the yielded `SortedSet<Pt>`.
  3. `into_pb_loop0_loop0.loop_spec`: the inner loop drives `Pt::serialize` over `inner`,
     producing a byte vector whose every 4-byte chunk encodes one cartesian point big-endian.
  4. `Vec.push` to append the resulting byte vector to `v`.

**Source**: spqr/src/encoding/polynomial.rs (lines 800:8-809:9)
-/
theorem body_spec_nat
    (iter : core.slice.iter.Iter (sorted_vec.SortedSet Pt))
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (sv : sorted_vec.SortedVec Pt)
    (inner : alloc.vec.Vec Pt)
    (h_sv : ∀ (_ : iter.i < iter.slice.val.length),
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        Pt.Insts.CoreCmpOrd (iter.slice.val[iter.i]) = ok sv)
    (h_inner : ∀ (_ : iter.i < iter.slice.val.length),
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        Pt.Insts.CoreCmpOrd sv = ok inner)
    (h_out_overflow : v.val.length + 1 ≤ Usize.max)
    (h_overflow : ∀ (_ : iter.i < iter.slice.val.length),
      4 * inner.val.length + 4 ≤ Usize.max) :
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
            serialized.val.length = 4 * inner.val.length ∧
            ∀ (k : Nat), k < inner.val.length →
              ∃ (b0 b1 b2 b3 : Std.U8),
                serialized.val[4 * k]?     = some b0 ∧
                serialized.val[4 * k + 1]? = some b1 ∧
                serialized.val[4 * k + 2]? = some b2 ∧
                serialized.val[4 * k + 3]? = some b3 ∧
                b0.val * 256 + b1.val =
                  (inner.val[k]!).x.value.val ∧
                b2.val * 256 + b3.val =
                  (inner.val[k]!).y.value.val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ :=
    core.slice.iter.IteratorSliceIter.next_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.i < iter.slice.val.length
  · obtain ⟨h_opt_eq, h_i1, h_slice1⟩ := h_some h_lt
    subst h_opt_eq
    -- The opaque deref simp lemmas (`deref_spec` from `FunsExternal.lean`) force any
    -- witness `sv` to equal `default` and any witness `inner` to equal `Vec.new Pt`.
    -- We extract these equalities and substitute, making `inner.val.length = 0` and
    -- trivializing the inner serialization loop.
    have h_sv_eq : sv = default := by
      have h := h_sv h_lt
      simp only [sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref_spec] at h
      injection h with h_eq; exact h_eq.symm
    subst h_sv_eq
    have h_inner_eq : inner = alloc.vec.Vec.new Pt := by
      have h := h_inner h_lt
      simp only [sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec] at h
      injection h with h_eq; exact h_eq.symm
    subst h_inner_eq
    -- After substitution: both derefs return concrete `default` / `Vec.new Pt`.
    have h_inner_empty : (alloc.vec.Vec.new Pt).val.length = 0 := rfl
    have h_inner_nil : (alloc.vec.Vec.new Pt).val = [] := rfl
    simp [sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref]
    simp [sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref]
    -- Step through the `Vec.len`, multiplication, and `with_capacity`.
    -- `simp` above reduced `(alloc.vec.Vec.new Pt).len` to `Usize.ofNatCore 0 ⋯`.
    -- `step` handles the `4#usize * 0` multiplication.
    step

    -- After the mul, we have `i1` with `i1.val = 0`.
    -- Provide explicit instances for the @[step] tagged `loop_spec`.
    step with into_pb_loop0_loop0.loop_spec
      (sv := (default : sorted_vec.SortedVec Pt)) (inner := alloc.vec.Vec.new Pt) by
      first
        | (simp [sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref_spec])
        | (simp [sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec])
        | (simp [h_inner_empty])
        | (simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new])
        | (intros j hj; simp [h_inner_empty] at hj)
        | scalar_tac
        | simp
        | omega
    -- After the inner loop, the body does a `Vec.push v v4` producing `v5`.
    -- Explicitly invoke `Vec.push` with overflow hypothesis.
    · simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
    ·
      step
      simp_all
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)

    subst h_opt_eq
    exact ⟨rfl, h_lt⟩


/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0.body`** (cascading:
byte-level + algebraic):

Lifts the byte-level specification (`body_spec_nat`) to a cascading postcondition that
includes the raw byte equality **and** the derived GF(2¹⁶) and polynomial identities for each
encoded coordinate of every cartesian point produced in the **cont** case.  Specializing the
canonical ring-homomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` (which vanishes on
`polyGF2`) recovers the GF(2¹⁶)-level interpretation of the serialized bytes via
`Nat.toGF216`.

The **done** case is unchanged: the output vector is returned untouched.
-/
@[step]
theorem body_spec
    (iter : core.slice.iter.Iter (sorted_vec.SortedSet Pt))
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (sv : sorted_vec.SortedVec Pt)
    (inner : alloc.vec.Vec Pt)
    (h_sv : ∀ (_ : iter.i < iter.slice.val.length),
      sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
        Pt.Insts.CoreCmpOrd (iter.slice.val[iter.i]) = ok sv)
    (h_inner : ∀ (_ : iter.i < iter.slice.val.length),
      sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref
        Pt.Insts.CoreCmpOrd sv = ok inner)
    (h_out_overflow : v.val.length + 1 ≤ Usize.max)
    (h_overflow : ∀ (_ : iter.i < iter.slice.val.length),
      4 * inner.val.length + 4 ≤ Usize.max) :
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
            serialized.val.length = 4 * inner.val.length ∧
            ∀ (k : Nat), k < inner.val.length →
              ∃ (b0 b1 b2 b3 : Std.U8),
                serialized.val[4 * k]?     = some b0 ∧
                serialized.val[4 * k + 1]? = some b1 ∧
                serialized.val[4 * k + 2]? = some b2 ∧
                serialized.val[4 * k + 3]? = some b3 ∧
                b0.val * 256 + b1.val =
                  (inner.val[k]!).x.value.val ∧
                b2.val * 256 + b3.val =
                  (inner.val[k]!).y.value.val ∧
                (b0.val * 256 + b1.val).toGF216 =
                  ((inner.val[k]!).x.value.val).toGF216 ∧
                (b2.val * 256 + b3.val).toGF216 =
                  ((inner.val[k]!).y.value.val).toGF216 ∧
                natToBinaryPoly (b0.val * 256 + b1.val) =
                  natToBinaryPoly ((inner.val[k]!).x.value.val) ∧
                natToBinaryPoly (b2.val * 256 + b3.val) =
                  natToBinaryPoly ((inner.val[k]!).y.value.val) ⦄ := by
  have h_raw :=
    body_spec_nat iter v sv inner h_sv h_inner h_out_overflow h_overflow
  apply WP.spec_mono h_raw
  intro cf h_post
  match cf with
  | ControlFlow.done v' =>
    exact h_post
  | ControlFlow.cont (iter1, v1) =>
    obtain ⟨h_lt, h_i1, h_slice1, serialized, h_v1, h_slen, h_enc⟩ := h_post
    refine ⟨h_lt, h_i1, h_slice1, serialized, h_v1, h_slen, fun k hk => ?_⟩
    obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, h_x, h_y⟩ := h_enc k hk
    exact ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, h_x, h_y,
      congr_arg Nat.toGF216 h_x,
      congr_arg Nat.toGF216 h_y,
      congr_arg natToBinaryPoly h_x,
      congr_arg natToBinaryPoly h_y⟩

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0
