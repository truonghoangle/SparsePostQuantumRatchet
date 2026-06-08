/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.Basic.Defs
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.Coeff.Basic
import Spqr.Math.Poly.Coeff.ListOps
import Spqr.Math.Poly.CharTwo.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval
import Spqr.Math.Poly.LinearFactors.Basic
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Math.Poly.Lagrange.DenomProd
import Spqr.Math.Poly.Lagrange.BasisPoly
import Spqr.Math.Poly.Lagrange.InterpolantSum
import Spqr.Math.Poly.Horner.Defs
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.ExpectedTrailing.Defs
import Spqr.Math.Poly.ExpectedTrailing.Basic
import Spqr.Math.Poly.Identities.Basic
import Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.CallMut
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.CallOne
import Spqr.Specs.Aeneas.Collect
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.SliceIterEnumMapCollect
/-!
# Spec theorem for `PolyEncoder::point_at`: loop body 0

The Rust method `PolyEncoder::point_at` (in `src/encoding/polynomial.rs`, lines 624–667) lazily
converts an array of `Point`s (evaluation-data vectors over GF(2¹⁶)) into an array of interpolating
polynomials the first time a point beyond the stored range is requested.  The conversion loop
(lines 636:12–658:13) iterates over `0..NUM_POLYS` (where `NUM_POLYS = 16`) and, for each index
`i`, constructs the unique Lagrange interpolating polynomial through the points
`{(j, pts[i].value[j]) : 0 ≤ j < pts[i].value.len()}` in GF(2¹⁶).

The extracted Lean function `encoding.polynomial.PolyEncoder.point_at_loop.body` performs one step
of this conversion loop.  Given a fixed-size array `pts` of 16 `Point` values, a `Range<usize>`
iterator, and the current output array of 16 `Poly` values, the body calls `next` on the iterator
and either:

  1. **Done** (`none`): the iterator is exhausted and the current `polys` array is returned
     unchanged.
  2. **Continue** (`some i`): retrieves the `i`-th `Point` from `pts`, constructs evaluation points
     `Pt { x: GF16::new(j as u16), y: pts[i].value[j] }` for each `j < pts[i].value.len()` via
     an enumerate-map-collect pipeline using the closure (lines 641:25–644:21), calls
     `Poly::from_complete_points` on the resulting `Vec<Pt>` to obtain the unique Lagrange
     interpolating polynomial, and stores it in `polys[i]`.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings; multiplication is carry-less polynomial multiplication modulo the irreducible
polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

The body spec composes:
  1. `IteratorRange.next` — to advance the outer range iterator.
  2. `Array.index_usize` — to retrieve the `i`-th point from `pts`.
  3. `alloc.vec.Vec.deref` → `Slice.iter` → `enumerate` → `map` (closure#1) → `collect` — to
     build the `Vec<Pt>` of evaluation points, where each `(j, y)` pair from the enumerated slice
     is mapped to `Pt { x: GF16::new(j as u16), y }`.
  4. `Poly::from_complete_points` (interpolation spec from `FromCompletePoints.lean`) — to compute
     the Lagrange interpolating polynomial from the evaluation points.
  5. `core.result.Result.expect` — to unwrap the `Ok` result (the `hax_lib::assume!` guarantees
     success).
  6. `Array.update` — to store the interpolating polynomial in the output array.

**Source**: spqr/src/encoding/polynomial.rs (lines 636:12-658:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial.PolyEncoder.point_at_loop

/-! ## Inhabited instances -/

/--
`Poly` wraps a `Vec<GF16>` of coefficients.  An `Inhabited` instance is required so that
`getElem!` (`[·]!`) on arrays/lists of `Poly` has a well-defined default value.  We use the empty
coefficient vector as the canonical default.
-/
instance : Inhabited encoding.polynomial.Poly := ⟨⟨alloc.vec.Vec.new _⟩⟩

/--
`Point` wraps a `Vec<GF16>`.  An `Inhabited` instance is required so that `getElem!` (`[·]!`)
on arrays/lists of `Point` has a well-defined default value.  We use the empty value vector
as the canonical default.
-/
instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Helper lemmas for the enumerate-map-collect pipeline -/

/-- Abbreviation for the Map iterator type used in the point_at pipeline. -/
private abbrev PointAtMapT :=
  core.iter.adapters.map.Map
    (core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter GF16))
    PolyEncoder.point_at.closure_1

/-- Inductive characterisation of `iterToList` applied to the enumerate-map-of-slice
iterator used in `PolyEncoder::point_at`. -/
private theorem iterToList_enum_map_acc
    (n : Nat)
    (m : PointAtMapT)
    (acc : List Pt)
    (h_n : n = m.iter.iter.slice.val.length - m.iter.iter.i)
    (h_count : m.iter.count.val = m.iter.iter.i)
    (h_len_le : m.iter.iter.slice.val.length ≤ UScalar.max .U16)
    (mapIterInst : core.iter.traits.iterator.Iterator PointAtMapT Pt)
    (h_next : mapIterInst.next = fun m' => do
      let (opt, iter') ←
        (core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
          (core.iter.traits.iterator.IteratorSliceIter GF16)).next m'.iter
      match opt with
      | none =>
        .ok (none, (core.iter.adapters.map.Map.mk iter' m'.f : PointAtMapT))
      | some item => do
        let (b, f') ←
          PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
            m'.f item
        .ok (some b, (core.iter.adapters.map.Map.mk iter' f' : PointAtMapT))) :
    ∃ (L : List Pt),
      alloc.vec.FromIteratorVec.iterToList mapIterInst m acc =
        .ok (acc.reverse ++ L) ∧
      L.length = m.iter.iter.slice.val.length - m.iter.iter.i ∧
      (∀ j (hj : j < L.length) (hs : j + m.iter.iter.i < m.iter.iter.slice.val.length),
          (L.get ⟨j, hj⟩).x.value.val = j + m.iter.iter.i ∧
          (L.get ⟨j, hj⟩).y =
            m.iter.iter.slice.val.get ⟨j + m.iter.iter.i, hs⟩) := by
  induction n generalizing m acc with
  | zero =>
    have h_ge : ¬ (m.iter.iter.i < m.iter.iter.slice.val.length) := by omega
    refine ⟨[], ?_, by simp; omega, by intro j hj; omega⟩
    conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
    rw [h_next]
    simp  [
      core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item,
      core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
      core.slice.iter.IteratorSliceIter.next, Slice.len, h_ge,
      ↓reduceDIte, bind_tc_ok]

  | succ n ih =>
    have h_lt : m.iter.iter.i < m.iter.iter.slice.val.length := by omega
    -- One step: enumerate.next yields (count, slice[i]), then call_mut produces Pt
    -- call_mut for the current element
    have h_count_lt : m.iter.count.val < 2 ^ 16 := by
      have : m.iter.count.val = m.iter.iter.i := h_count
      have : m.iter.iter.i < m.iter.iter.slice.val.length := h_lt
      have : m.iter.iter.slice.val.length ≤ UScalar.max .U16 := h_len_le
      simp  at h_len_le ⊢
      grind
    have h_count_add : m.iter.count.val + 1 ≤ Usize.max := by
      have := m.iter.count.hBounds; scalar_tac
    -- Compute what call_mut returns
    have h_cm_eq :
      PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
        m.f (m.iter.count, m.iter.iter.slice.val.get ⟨m.iter.iter.i, h_lt⟩) =
        .ok ({ x := { value := UScalar.cast .U16 m.iter.count },
               y := m.iter.iter.slice.val.get ⟨m.iter.iter.i, h_lt⟩ },
              m.f) := by
      unfold PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
      simp only [ uncurry_apply_pair]
      simp only [lift, bind_tc_ok]
      unfold encoding.gf.GF16.new
      simp [bind_tc_ok]
    -- Construct the current Pt
    set pt : Pt := { x := { value := UScalar.cast .U16 m.iter.count },
                     y := m.iter.iter.slice.val.get ⟨m.iter.iter.i, h_lt⟩ }
    have h_pt_x : pt.x.value.val = m.iter.iter.i := by
      simp [pt, UScalar.cast_val_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact h_count
    have h_pt_y : pt.y = m.iter.iter.slice.val.get ⟨m.iter.iter.i, h_lt⟩ := by
      simp [pt]
    -- Construct the new map iterator state for the IH
    set m' : PointAtMapT := core.iter.adapters.map.Map.mk
      { iter := core.slice.iter.Iter.mk m.iter.iter.slice (m.iter.iter.i + 1),
        count := ⟨m.iter.count.val + 1, by scalar_tac⟩ }
      m.f
    have hm'_slice : m'.iter.iter.slice = m.iter.iter.slice := rfl
    have hm'_i : m'.iter.iter.i = m.iter.iter.i + 1 := rfl
    have hm'_count : m'.iter.count.val = m'.iter.iter.i := by
      simp [m', h_count]
      rfl

    -- One-step reduction of iterToList
    have h_step : alloc.vec.FromIteratorVec.iterToList mapIterInst m acc =
        alloc.vec.FromIteratorVec.iterToList mapIterInst m'
          (pt :: acc) := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      rw [h_next]
      simp [
core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
        core.slice.iter.IteratorSliceIter.next, Slice.len, Usize.ofNatCore_val_eq, h_lt,
        ↓reduceDIte, bind_tc_ok, uncurry_apply_pair, bind_assoc]

      erw [h_cm_eq]
      simp [bind_tc_ok]

      congr 1
      · congr 1
        simp
        apply UScalar.eq_of_val_eq
        simp [UScalar.wrapping_add_val_eq]
        grind

    -- Apply IH
    have h_n' : n = m'.iter.iter.slice.val.length - m'.iter.iter.i := by
      rw [hm'_slice, hm'_i]; omega
    obtain ⟨L', hL'_eq, hL'_len, hL'_elts⟩ :=
      ih m' (pt :: acc) h_n' hm'_count (by rwa [hm'_slice])
    refine ⟨pt :: L', ?_, ?_, ?_⟩
    · -- iterToList returns the right value
      rw [h_step, hL'_eq]
      simp [List.reverse_cons, List.append_assoc]
    · -- length
      simp [hL'_len, hm'_slice, hm'_i]; omega
    · -- element-wise properties
      intro j hj hs
      cases j with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨h_pt_x, h_pt_y⟩
      | succ k =>
        have hk : k < L'.length := by
          have : (pt :: L').length = L'.length + 1 := rfl
          omega
        have hks : k + m'.iter.iter.i < m'.iter.iter.slice.val.length := by
          rw [hm'_slice, hm'_i]; omega
        obtain ⟨hx, hy⟩ := hL'_elts k hk hks
        simp only [List.get_eq_getElem, hm'_slice, hm'_i] at hx hy
        refine ⟨?_, ?_⟩
        · show ((pt :: L').get ⟨k + 1, hj⟩).x.value.val = k + 1 + m.iter.iter.i
          have : (pt :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this]
          grind
        · show ((pt :: L').get ⟨k + 1, hj⟩).y = _
          have : (pt :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this]
          rw [show m.iter.iter.slice.val.get ⟨k + 1 + m.iter.iter.i, hs⟩ =
            m.iter.iter.slice.val.get ⟨k + m'.iter.iter.i, hks⟩ from by
              congr 1; ext; simp [hm'_i]; omega]
          exact hy

/-- Spec for the from_iter (collect) call in the point_at pipeline. -/
private theorem from_iter_point_at_spec
    (s : Slice GF16)
    (h_len_le : s.val.length ≤ UScalar.max .U16) :
    alloc.vec.FromIteratorVec.from_iter
      (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.mapIterator
          (core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
            (core.iter.traits.iterator.IteratorSliceIter GF16))
          point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt))
      { iter := { iter := { slice := s, i := 0 }, count := 0#usize }, f := () }
    ⦃ (pt_vec : alloc.vec.Vec Pt) =>
      pt_vec.val.length = s.val.length ∧
      (∀ j (hj : j < pt_vec.val.length) (hs : j < s.val.length),
        (pt_vec.val.get ⟨j, hj⟩).x.value.val = j ∧
        (pt_vec.val.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩) ⦄ := by
  unfold alloc.vec.FromIteratorVec.from_iter
  simp only [core.iter.traits.collect.IntoIterator.Blanket, bind_tc_ok]
  apply WP.spec_bind (Pₘ := fun (L : List Pt) =>
    L.length = s.val.length ∧
    L.length ≤ Usize.max ∧
    (∀ j (hj : j < L.length) (hs : j < s.val.length),
        (L.get ⟨j, hj⟩).x.value.val = j ∧
        (L.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩))
  · obtain ⟨L, hL_eq, hL_len, hL_elts⟩ := iterToList_enum_map_acc
      s.val.length
      { iter := { iter := { slice := s, i := 0 }, count := 0#usize }, f := () }
      [] (by simp) (by simp) h_len_le
      (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.mapIterator
        (core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
          (core.iter.traits.iterator.IteratorSliceIter GF16))
        PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt)
      (by unfold core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.mapIterator; grind)
    simp only [List.reverse_nil, List.nil_append] at hL_eq
    rw [hL_eq]
    simp only [WP.spec, WP.theta, WP.wp_return]
    refine ⟨by simp [hL_len], by simp [hL_len]; grind, ?_⟩
    intro j hj hs
    have hs' : j + 0 < s.val.length := by omega
    obtain ⟨hx, hy⟩ := hL_elts j (by omega) hs'
    simp at hx
    exact ⟨hx, hy⟩
  · intro list ⟨h_len, h_max, h_elts⟩
    split
    · exact ⟨h_len, fun j hj hs => h_elts j hj hs⟩
    · omega

/-! ## Helper lemma: double-set at the same index -/

/-- After setting an array at index `i` with its own element (`arr[i]!`), then overwriting at `i`
    with a new value `y`, both the Array-level and List-level lookups at `i` return `y`.
    This is the key step for showing that the `index_mut_usize` / update pattern in the loop body
    stores the correct polynomial. -/
private lemma array_set_restore_set_val_getElem!
    {α : Type} {n : Usize} [Inhabited α]
    (arr : Array α n) (i : Usize) (y : α) (hi : i.val < n.val) :
    ((arr.set i (arr.val[i.val]!)).set i y).val[i.val]! = y := by
  simp only [Array.set_getElem!_eq, Array.set_val_eq]
  have : i.val < arr.val.length := by rw [arr.property]; exact hi
  grind

/-- Array-level variant: looking up with the Usize index after a double-set gives the new value. -/
private lemma array_set_restore_set_getElem!
    {α : Type} {n : Usize} [Inhabited α]
    (arr : Array α n) (i : Usize) (y : α) (hi : i.val < n.val) :
    ((arr.set i (arr.val[i.val]!)).set i y)[i]! = y := by
  simp only [Array.getElem!_Usize_eq, Array.set_getElem!_eq, Array.set_val_eq]
  have : i.val < arr.val.length := by rw [arr.property]; exact hi
  grind

/-! ## Spec theorem for the point_at loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop.body`**:

One step of the point-to-polynomial conversion loop inside `PolyEncoder::point_at`.  Given the
fixed-size array `pts` of 16 `Point` values (each wrapping a `Vec<GF16>` of evaluation data), a
range iterator over `0..NUM_POLYS`, and the current output array of 16 `Poly` values, the body
retrieves the next index `i` from the iterator and either terminates or extends the output:

• The function always succeeds (no panic) provided the preconditions hold: the iterator range end
  does not exceed the array size (16), each point's value vector has an admissible length
  (one of 0, 1, 3, 5, 30, 34, or 36 — the protocol-V1 sizes for which precomputed Lagrange
  basis arrays are shipped statically).

• In the **done** case (iterator exhausted):
    the polynomial array `polys` is returned unchanged, and the iterator condition is negated:
    `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output array is updated at position `i` with the Lagrange interpolating polynomial:
        there exist a `Poly` `poly` and a Lagrange basis slice `lagrange_polys` such that
        `polys'.val[iter.start.val]! = poly` and
        `poly.toGF216Poly =
           ∑ j ∈ Finset.range n,
             C (((pts.val[i]!).value.val[j]!).toGF216) *
               (lagrange_polys.val[j]!).toGF216Poly`
      where `n = (pts.val[i]!).value.val.length`.
    - All other positions are unchanged:
        `∀ k, k ≠ iter.start.val → polys'.val[k]! = polys.val[k]!`

    This corresponds to the Rust body:
    ```rust
    for i in 0..NUM_POLYS {
        let pt_vec = pts[i].value.iter().enumerate()
            .map(|(x, y)| Pt { x: GF16::new(x as u16), y: *y })
            .collect::<Vec<Pt>>();
        hax_lib::assume!(pt_vec.len() == 0 || ... || pt_vec.len() == 36);
        let res = Poly::from_complete_points(&pt_vec);
        hax_lib::assume!(res.is_ok());
        polys[i] = res.expect("pt_vec should be complete");
    }
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 636:12-658:13)
-/
@[step]
theorem body_spec
    (pts : Array encoding.polynomial.Point 16#usize)
    (iter : core.ops.range.Range Std.Usize)
    (polys : Array encoding.polynomial.Poly 16#usize)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_admissible : ∀ (j : Nat), j < 16 →
        let len := (pts.val[j]!).value.val.length
        len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
        len = 30 ∨ len = 34 ∨ len = 36) :
    body pts iter polys ⦃ cf =>
      match cf with
      | ControlFlow.done polys' =>
          polys' = polys ∧
          ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, polys') =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (poly : encoding.polynomial.Poly),
            polys'.val[iter.start.val]! = poly ∧
            (∀ k, k ≠ iter.start.val →
              polys'.val[k]! = polys.val[k]!) ∧
            ∃ (lagrange_polys : Slice Poly),
              (pts.val[iter.start.val]!).value.val.length ≤
                lagrange_polys.val.length ∧
              (poly.toGF216Poly =
                ∑ j ∈ Finset.range
                    (pts.val[iter.start.val]!).value.val.length,
                  C (((pts.val[iter.start.val]!).value.val[j]!).toGF216) *
                    (lagrange_polys.val[j]!).toGF216Poly) ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · -- cont case: iterator not exhausted
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_adm := h_admissible iter.start.val h_i_lt_16
    simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, uncurry_apply_pair, not_lt, ↓existsAndEq,
      List.getElem!_eq_getElem?_getD, ne_eq, true_and]
    simp only [core.slice.Slice.iter, core.slice.iter.IteratorSliceIter.enumerate, bind_tc_ok]
    step*
    -- After step*, the goal is a WP for:
    --   from_iter >>= from_complete_points >>= expect >>= massert >>= ...
    -- Use spec_bind to split at the from_iter (collect) call
    subst p_post
    have h_len_le : (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)).val.length ≤
        UScalar.max .U16 := by
      simp [alloc.vec.Vec.deref]
      rcases h_adm with h | h | h | h | h | h | h <;> (simp_all [UScalar.max])
      all_goals (grind)
    have h_pts_lt : iter.start.val < pts.val.length := by rw [pts.property]; exact h_i_lt_16
    have h_eq : pts.val[iter.start.val] = pts.val[iter.start.val]! :=
      List.Inhabited_getElem_eq_getElem! pts.val iter.start.val h_pts_lt
    rw [h_eq]; clear h_eq h_pts_lt
    apply WP.spec_bind (from_iter_point_at_spec
      (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)) h_len_le)

    intro pt_vec ⟨h_pt_len, h_pt_elts⟩
    -- Now the goal is the continuation: from_complete_points >>= expect >>= ...
    -- Establish the admissible length for from_complete_points
    have h_deref_len : (alloc.vec.Vec.deref pt_vec).val.length =
        (pts.val[iter.start.val]!).value.val.length := by
      simp [alloc.vec.Vec.deref, h_pt_len]
    have h_adm' : (alloc.vec.Vec.deref pt_vec).val.length = 0 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 1 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 3 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 5 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 30 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 34 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 36 := by
      rw [h_deref_len]; exact h_adm
    -- Apply from_complete_points_spec
    apply WP.spec_bind
      (encoding.polynomial.Poly.from_complete_points_spec (alloc.vec.Vec.deref pt_vec) h_adm')
    intro res h_res
    -- The collected points satisfy validation: pts[j].x.value.val = j
    have h_valid : ∀ (j : Nat) (hj : j < (alloc.vec.Vec.deref pt_vec).val.length),
        ((alloc.vec.Vec.deref pt_vec).val.get ⟨j, hj⟩).x.value.val = j := by
      intro j hj
      simp [alloc.vec.Vec.deref] at hj ⊢
      exact (h_pt_elts j hj (by omega)).1
    -- Case split on Ok / Err
    match res with
    | core.result.Result.Ok poly =>
      -- Ok case: Result.expect succeeds
      obtain ⟨h_all_valid, polys_lp, h_len_le_lp, h_sum, _, _⟩ := h_res
      simp only [core.result.Result.expect, bind_tc_ok]
      -- massert succeeds since iter.start < 16
      simp only [massert, bind_tc_ok]
      have h_massert : (iter.start.val < 16) = True := by grind
      simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, h_massert, ↓reduceIte]
      step*
      constructor
      · grind
      · constructor
        · grind
        · constructor
          · grind
          · constructor
            · intro k hk
              simp_all
            · have h_a_eq : a[iter.start]! = poly := by
                rw [a_post, p2_post1, p2_post2]
                rw [List.Inhabited_getElem_eq_getElem! polys.val iter.start.val
                  (by rw [polys.property]; exact h_i_lt_16)]
                exact array_set_restore_set_getElem! polys iter.start poly (by grind)
              simp_all
              refine ⟨polys_lp, ?_, ?_⟩
              · omega
              · apply Finset.sum_congr rfl
                intro j hj
                have hj_range := Finset.mem_range.mp hj
                have hj_pt : j < pt_vec.val.length := by
                  simp [alloc.vec.Vec.deref] at *; omega
                have hy := (h_pt_elts j
                  (by simp [alloc.vec.Vec.deref]; omega)).2
                simp only [alloc.vec.Vec.deref, List.get_eq_getElem] at hy
                simp only [alloc.vec.Vec.deref,
                  List.getElem?_eq_getElem hj_pt,
                  List.getElem?_eq_getElem hj_range,
                  Option.getD_some]
                rw [hy]


    | core.result.Result.Err () =>
      -- Err case: contradiction since all collected points satisfy validation
      exfalso
      obtain ⟨j, hj, h_neq⟩ := h_res
      exact h_neq (h_valid j hj)
  · -- done case: iterator exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.point_at_loop
