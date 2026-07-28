/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.CallOne
import Spqr.Specs.Aeneas.MapIteratorTransformerNext
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
open PolyEncoder.point_at.closure_1
open core.iter.adapters.map.Map
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

/-- Abbreviation for the Enumerate iterator type used in the point_at pipeline. -/
private abbrev PointAtEnumT :=
  core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter GF16)

/-- Abbreviation for the Map iterator type used in the point_at pipeline. -/
private abbrev PointAtMapT :=
  core.iter.adapters.map.Map
    (core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter GF16))
    PolyEncoder.point_at.closure_1

/-- Inductive characterisation of `iterToList` applied to the enumerate-map-of-slice
iterator used in `PolyEncoder::point_at`.  The state type is the underlying
`Enumerate (Iter GF16)` (matching `mapIteratorTransformer`'s state type). -/
private theorem iterToList_enum_map_acc
    (n : Nat)
    (enum_iter : PointAtEnumT)
    (acc : List Pt)
    (h_n : n = enum_iter.iter.slice.val.length - enum_iter.iter.i)
    (h_count : enum_iter.count.val = enum_iter.iter.i)
    (h_len_le : enum_iter.iter.slice.val.length ≤ UScalar.max .U16)
    (transIterInst : core.iter.traits.iterator.Iterator PointAtEnumT Pt)
    (h_next : transIterInst.next = fun e => do
      let (opt, iter') ←
        (core.iter.traits.iterator.IteratorEnumerate
          (core.iter.traits.iterator.IteratorSliceIter GF16)).next e
      match opt with
      | none =>
        .ok (none, iter')
      | some item => do
        let (b, _) ←
        PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
            () item
        .ok (some b, iter')) :
    ∃ (L : List Pt),
      alloc.vec.FromIteratorVec.iterToList transIterInst enum_iter acc =
        .ok (acc.reverse ++ L) ∧
      L.length = enum_iter.iter.slice.val.length - enum_iter.iter.i ∧
      (∀ j (hj : j < L.length) (hs : j + enum_iter.iter.i < enum_iter.iter.slice.val.length),
          (L.get ⟨j, hj⟩).x.value.val = j + enum_iter.iter.i ∧
          (L.get ⟨j, hj⟩).y =
            enum_iter.iter.slice.val.get ⟨j + enum_iter.iter.i, hs⟩) := by
  induction n generalizing enum_iter acc with
  | zero =>
    have h_ge : ¬ (enum_iter.iter.i < enum_iter.iter.slice.val.length) := by omega
    refine ⟨[], ?_, by simp; omega, by intro j hj; omega⟩
    conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
    rw [h_next]
    simp  [
      core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next, Slice.len, h_ge,
      ↓reduceDIte, bind_tc_ok]
  | succ n ih =>
    have h_lt : enum_iter.iter.i < enum_iter.iter.slice.val.length := by omega
    have h_count_lt : enum_iter.count.val < 2 ^ 16 := by
      have : enum_iter.count.val = enum_iter.iter.i := h_count
      have : enum_iter.iter.i < enum_iter.iter.slice.val.length := h_lt
      have : enum_iter.iter.slice.val.length ≤ UScalar.max .U16 := h_len_le
      simp  at h_len_le ⊢
      grind
    have h_count_add : enum_iter.count.val + 1 ≤ Usize.max := by
      have := enum_iter.count.hBounds; scalar_tac
    -- Compute what call_mut returns
    have h_cm_eq :
      PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
        () (enum_iter.count, enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩) =
        .ok ({ x := { value := UScalar.cast .U16 enum_iter.count },
               y := enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩ },
              ()) := by
      unfold Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
      simp only [ uncurry_apply_pair]
      simp only [lift, bind_tc_ok]
      unfold encoding.gf.GF16.new
      simp [bind_tc_ok]
    -- Construct the current Pt
    set pt : Pt := { x := { value := UScalar.cast .U16 enum_iter.count },
                     y := enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩ }
    have h_pt_x : pt.x.value.val = enum_iter.iter.i := by
      simp only [UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.reducePow, pt]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact h_count
    have h_pt_y : pt.y = enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩ := by
      simp [pt]
    -- Construct the new enumerate iterator state for the IH
    set enum_iter' : PointAtEnumT :=
      { iter := core.slice.iter.Iter.mk enum_iter.iter.slice (enum_iter.iter.i + 1),
        count := ⟨enum_iter.count.val + 1, by scalar_tac⟩ }
    have hei'_slice : enum_iter'.iter.slice = enum_iter.iter.slice := rfl
    have hei'_i : enum_iter'.iter.i = enum_iter.iter.i + 1 := rfl
    have hei'_count : enum_iter'.count.val = enum_iter'.iter.i := by
      simp [enum_iter', h_count]
      rfl
    have h_step : alloc.vec.FromIteratorVec.iterToList transIterInst enum_iter acc =
        alloc.vec.FromIteratorVec.iterToList transIterInst enum_iter'
          (pt :: acc) := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      rw [h_next]
      simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorSliceIter.next, Slice.len, Usize.ofNatCore_val_eq, h_lt,
        ↓reduceDIte, bind_tc_ok, bind_assoc, uncurry_apply_pair]
      erw [h_cm_eq]
      simp only [bind_tc_ok, uncurry_apply_pair]
      have ⟨y, h_add_eq, h_y_val⟩ :
          ∃ y, (enum_iter.count + 1#usize : Result Usize) = ok y
          ∧ y.val = enum_iter.count.val + 1 := by
        have : enum_iter.count.val + (1#usize : Usize).val ≤ Usize.max := by scalar_tac
        have := Usize.add_spec this
        revert this; generalize (enum_iter.count + 1#usize : Result Usize) = res
        match res with
        | .ok z => intro h; exact ⟨z, rfl, by simp_all [WP.spec_ok]⟩
        | .fail _ => simp_all
        | .div => simp_all
      have : y = enum_iter'.count := by apply UScalar.eq_of_val_eq; omega
      subst this
      simp only [h_add_eq, bind_tc_ok, enum_iter']
    have h_n' : n = enum_iter'.iter.slice.val.length - enum_iter'.iter.i := by
      rw [hei'_slice, hei'_i]; omega
    obtain ⟨L', hL'_eq, hL'_len, hL'_elts⟩ :=
      ih enum_iter' (pt :: acc) h_n' hei'_count (by rwa [hei'_slice])
    refine ⟨pt :: L', ?_, ?_, ?_⟩
    · rw [h_step, hL'_eq]
      simp [List.reverse_cons, List.append_assoc]
    · simp [hL'_len, hei'_slice, hei'_i]; omega
    · intro j hj hs
      cases j with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨h_pt_x, h_pt_y⟩
      | succ k =>
        have hk : k < L'.length := by
          have : (pt :: L').length = L'.length + 1 := rfl
          omega
        have hks : k + enum_iter'.iter.i < enum_iter'.iter.slice.val.length := by
          rw [hei'_slice, hei'_i]; omega
        obtain ⟨hx, hy⟩ := hL'_elts k hk hks
        simp only [List.get_eq_getElem, hei'_slice, hei'_i] at hx hy
        refine ⟨?_, ?_⟩
        · show ((pt :: L').get ⟨k + 1, hj⟩).x.value.val = k + 1 + enum_iter.iter.i
          have : (pt :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this]
          grind
        · show ((pt :: L').get ⟨k + 1, hj⟩).y = _
          have : (pt :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this]
          rw [show enum_iter.iter.slice.val.get ⟨k + 1 + enum_iter.iter.i, hs⟩ =
            enum_iter.iter.slice.val.get ⟨k + enum_iter'.iter.i, hks⟩ from by
              congr 1; ext; simp [hei'_i]; omega]
          exact hy

/-- Spec for the from_iter (collect) call in the point_at pipeline. -/
private theorem from_iter_point_at_spec
    (s : Slice GF16)
    (h_len_le : s.val.length ≤ UScalar.max .U16) :
    alloc.vec.FromIteratorVec.from_iter
      (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.adapters.map.mapIteratorTransformer
          ({ iter := { iter := { slice := s, i := 0 }, count := 0#usize }, f := () } : PointAtMapT)
          (core.iter.traits.iterator.IteratorEnumerate
            (core.iter.traits.iterator.IteratorSliceIter GF16))
          point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt))
      { iter := { slice := s, i := 0 }, count := 0#usize }
    ⦃ (pt_vec : alloc.vec.Vec Pt) =>
      pt_vec.val.length = s.val.length ∧
      (∀ j (hj : j < pt_vec.val.length) (hs : j < s.val.length),
        (pt_vec.val.get ⟨j, hj⟩).x.value.val = j ∧
        (pt_vec.val.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩) ⦄ := by
  unfold alloc.vec.FromIteratorVec.from_iter
  simp only
  apply WP.spec_bind (Pₘ := fun (L : List Pt) =>
    L.length = s.val.length ∧
    L.length ≤ Usize.max ∧
    (∀ j (hj : j < L.length) (hs : j < s.val.length),
        (L.get ⟨j, hj⟩).x.value.val = j ∧
        (L.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩))
  · obtain ⟨L, hL_eq, hL_len, hL_elts⟩ := iterToList_enum_map_acc
      s.val.length
      { iter := { slice := s, i := 0 }, count := 0#usize }
      [] (by simp) (by simp) h_len_le
      (core.iter.adapters.map.mapIteratorTransformer
        ({ iter := { iter := { slice := s, i := 0 }, count := 0#usize }, f := () } : PointAtMapT)
        (core.iter.traits.iterator.IteratorEnumerate
          (core.iter.traits.iterator.IteratorSliceIter GF16))
        PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt)
      (by
        ext e
        grind[ Insts.CoreIterTraitsIteratorIterator.mapIteratorTransformer_next_spec _ _ _ e])
    simp only [List.reverse_nil, List.nil_append] at hL_eq
    rw [hL_eq]
    simp only [WP.spec, WP.theta, WP.wp_return]
    refine ⟨by simp [hL_len], by simp [hL_len]; grind, ?_⟩
    intro j hj hs
    have hs' : j + 0 < s.val.length := by omega
    obtain ⟨hx, hy⟩ := hL_elts j (by omega) hs'
    simp only [List.get_eq_getElem, add_zero] at hx
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

/-! ## Axiom for the map+collect pipeline -/

/-- Axiom: `Iterator.collect.default` on a `Map (Enumerate (Iter GF16)) closure_1` value `m`
    is equivalent to `FromIteratorVec.from_iter` with the `mapIteratorTransformer`-constructed
    iterator instance, using `m.iter` as the initial state.

    This bridges the generated Aeneas code (which uses the generic trait-default
    `Iterator.collect.default` after `step*` has already resolved `Iterator.map.default`)
    with the hand-verified `from_iter_point_at_spec` that uses `mapIteratorTransformer`
    (whose `next` is concretely defined).

    The axiom is sound because `Iterator.collect.default` unfolds to
    `FromIterator.from_iter (IntoIterator.Blanket iterInst) self.iter`, and the
    `Map` iterator instance delegates to `mapIteratorTransformer`. -/
private theorem map_collect_eq_point_at
    (m : PointAtMapT) :
    core.iter.traits.iterator.Iterator.collect.default
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          (core.iter.traits.iterator.IteratorEnumerate
            (core.iter.traits.iterator.IteratorSliceIter GF16))
          Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt)
        (core.iter.traits.collect.FromIteratorVec Pt)
        m
    = alloc.vec.FromIteratorVec.from_iter
        (core.iter.traits.collect.IntoIterator.Blanket
          (core.iter.adapters.map.mapIteratorTransformer
            ({ iter := m.iter, f := () } : PointAtMapT)
            (core.iter.traits.iterator.IteratorEnumerate
              (core.iter.traits.iterator.IteratorSliceIter GF16))
            Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt))
        m.iter := by
        sorry

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
    `¬ (iter.start.val < iter.end.val)`.

• In the **cont** case (received index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.end.val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.end = iter.end`.
    - The output array is updated at position `i` with the Lagrange interpolating polynomial:
        there exist a `Poly` `poly` and a `Usize` `len` such that
        `len.val = (pts.val[i]!).value.val.length`,
        `polys'.val[iter.start.val]! = poly`, and
        `poly.toGF216Poly =
           ∑ j ∈ Finset.range n,
             C (((pts.val[i]!).value.val[j]!).toGF216) *
               scaledLagrangeBasis len j`
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
    (pts : Array Point 16#usize)
    (iter : core.ops.range.Range Std.Usize)
    (polys : Array Poly 16#usize)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_admissible : ∀ (j : Nat), j < 16 →
        let len := (pts.val[j]!).value.val.length
        len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
        len = 30 ∨ len = 34 ∨ len = 36) :
    body pts iter polys ⦃ cf =>
      match cf with
      | ControlFlow.done polys' =>
          polys' = polys ∧
          ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, polys') =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          (∀ k, k ≠ iter.start.val →
            polys'.val[k]! = polys.val[k]!) ∧
            (polys'.val[iter.start.val]!.toGF216Poly =
            ∑ j ∈ Finset.range (pts.val[iter.start.val]!).value.val.length,
            C (((pts.val[iter.start.val]!).value.val[j]!).toGF216) *
            scaledLagrangeBasis (alloc.vec.Vec.len ((pts.val[iter.start.val]!).value)) j) ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_adm := h_admissible iter.start.val h_i_lt_16
    simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, uncurry_apply_pair, not_lt,
      List.getElem!_eq_getElem?_getD, ne_eq]
    simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
    step*
    subst p_post
    have h_len_le : (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)).val.length ≤
        UScalar.max .U16 := by
      simp only [alloc.vec.Vec.deref, List.getElem!_eq_getElem?_getD, Subtype.coe_eta,
        UScalar.max_UScalarTy_U16_eq]
      rcases h_adm with h | h | h | h | h | h | h <;> (simp_all only [List.Vector.length_val,
        UScalar.ofNatCore_val_eq, getElem!_pos, List.length_eq_zero_iff, not_true_eq_false,
        reduceCtorEq, false_and, implies_true,  and_self,
        getElem?_pos, Option.getD_some, List.length_nil, zero_le])
      all_goals (grind only [= U16.max_eq])
    have h_pts_lt : iter.start.val < pts.val.length := by rw [pts.property]; exact h_i_lt_16
    have h_eq : pts.val[iter.start.val] = pts.val[iter.start.val]! :=
      List.Inhabited_getElem_eq_getElem! pts.val iter.start.val h_pts_lt
    simp only [alloc.vec.Vec.len]
    -- Apply the collect axiom, substitute m.iter via m_post, normalize with h_eq
    simp only [map_collect_eq_point_at, m_post, h_eq]; clear h_eq h_pts_lt
    apply WP.spec_bind (from_iter_point_at_spec
      (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)) h_len_le)
    intro pt_vec ⟨h_pt_len, h_pt_elts⟩
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
    apply WP.spec_bind
      (encoding.polynomial.Poly.from_complete_points_spec (alloc.vec.Vec.deref pt_vec) h_adm')
    intro res h_res
    have h_valid : ∀ (j : Nat) (hj : j < (alloc.vec.Vec.deref pt_vec).val.length),
        ((alloc.vec.Vec.deref pt_vec).val.get ⟨j, hj⟩).x.value.val = j := by
      intro j hj
      simp only [alloc.vec.Vec.deref, Subtype.coe_eta, List.get_eq_getElem] at hj ⊢
      exact (h_pt_elts j hj (by omega)).1
    match res with
    | core.result.Result.Ok poly =>
      obtain ⟨h_all_valid, h_sum⟩ := h_res
      simp only [core.result.Result.expect, bind_tc_ok]
      simp only [massert]
      have h_massert : (iter.start.val < 16) = True := by grind
      simp only [h_massert, ↓reduceIte]
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
              have h_slicelen_eq : Slice.len (alloc.vec.Vec.deref pt_vec) =
                  alloc.vec.Vec.len ((pts.val[iter.start.val]!).value) := by
                simp only [Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] at h_deref_len ⊢
                grind
              rw [h_slicelen_eq] at h_sum
              simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                  List.length_eq_zero_iff, not_true_eq_false, reduceCtorEq, false_and, implies_true,
                  and_self,  UScalar.max_UScalarTy_U16_eq,
                  List.get_eq_getElem, forall_true_left, List.getElem!_eq_getElem?_getD,
                  eq_iff_iff, iff_true, Array.getElem!_Usize_eq, Array.set_val_eq,
                  List.set_getElem_self, List.length_set, List.getElem_set_self, getElem?_pos,
                  Option.getD_some]
              apply Finset.sum_congr rfl
              intro j hj
              have hj_range := Finset.mem_range.mp hj
              have hj_pt : j < pt_vec.val.length := by
                simp [alloc.vec.Vec.deref] at *; omega
              have hy := (h_pt_elts j
                (by simp [alloc.vec.Vec.deref]; omega)).2
              simp only [alloc.vec.Vec.deref] at hy
              simp only [alloc.vec.Vec.deref,
                List.getElem?_eq_getElem hj_pt,
                List.getElem?_eq_getElem hj_range,
                Option.getD_some]
              rw [hy]
    | core.result.Result.Err () =>
      exfalso
      obtain ⟨j, hj, h_neq⟩ := h_res
      exact h_neq (h_valid j hj)
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyEncoder.point_at_loop
