/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPbLoop1
import Spqr.Specs.Aeneas.RangeIteratorNext

/-!
# Spec theorem for `PolyDecoder::from_pb`: loop body 0

The extracted Lean function `encoding.polynomial.PolyDecoder.from_pb_loop0.body` performs one
step of the *outer* point-set-deserialization loop inside `PolyDecoder::from_pb`.  Given the
vector of serialized byte vectors `v : Vec<Vec<u8>>` (one per protobuf point-set slot), a
`Range<usize>` iterator over slot indices, and the current output array
`out_pts : [SortedSet<Pt>; 16]`, the body calls `next` on the range iterator and either:

  1. **Done** (`none`): the iterator is exhausted and the output array `out_pts` is returned
     unchanged.
  2. **Continue** (`some i`): retrieves the `i`-th serialized byte vector `pts = v[i]`, allocates
     a fresh empty `SortedSet<Pt>` with capacity `pts.len() / 4` (via the opaque
     `sorted_vec.SortedSet.with_capacity` axiom), runs the *inner* 4-byte-chunk
     deserialization loop (`from_pb_loop0_loop0`) to populate it with cartesian points decoded
     from `pts`, and finally stores the resulting sorted set into `out_pts[i]`.

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.
A cartesian point `Pt = (x, y)` packs two such elements; its 4-byte serialization satisfies the
big-endian decoding invariant
  `x.value = serialized[0] · 256 + serialized[1]`,
  `y.value = serialized[2] · 256 + serialized[3]`.

The body spec composes:
  1. `IteratorRange.next` — to advance the outer range iterator over slot indices.
  2. `alloc.vec.Vec.index` (`SliceIndexUsizeSlice`) — to retrieve the `i`-th serialized byte
     vector `pts` from `v`.
  3. `alloc.vec.Vec.len` and `UScalar` division — to compute the capacity `pts.len() / 4`.
  4. `sorted_vec.SortedSet.with_capacity` (opaque axiom) — to allocate the fresh sorted set;
     parameterised by an explicit witness `v_init : Std.Usize → SortedSet Pt`.
  5. `from_pb_loop0_loop0.loop_spec` (inner loop spec from `FromPbLoop1.lean`) — to drive the
     4-byte-chunk deserialization and produce the chain of `SortedSet.push` operations.
  6. `Array.index_mut_usize` and `Array.update` — to store the populated sorted set into the
     fixed-size output array at slot `i`.

Because both `sorted_vec.SortedSet.with_capacity` and `sorted_vec.SortedSet.push` are extracted
as opaque axioms (no provable structural behaviour), the postcondition only asserts the
*existence* of a chain of intermediate sorted-set states linked by valid push equations; it
does not relate the final per-slot `SortedSet<Pt>` structurally to the corresponding
serialized byte vector beyond the per-iteration cartesian-point witnesses.

**Source**: spqr/src/encoding/polynomial.rs (lines 838:8-848:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

/-! ## Inhabited instance for `SortedSet Pt` slots -/

/--
`Array (SortedSet Pt) 16#usize` slots need an `Inhabited` default for `getElem!` (`[·]!`) on
the underlying list of sorted sets.  We borrow the `default` inhabitant provided by the
existing `Inhabited (SortedSet T)` instance.
-/
noncomputable instance : Inhabited (sorted_vec.SortedSet Pt) := ⟨default⟩

/-! ## Spec theorem for the from_pb outer loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0.body`**:

One step of the outer point-set-deserialization loop inside `PolyDecoder::from_pb`.  Given the
vector of serialized byte vectors `v` (from `pb.pts`), a range iterator over slot indices
`0..16`, and the current output array of 16 `SortedSet<Pt>` slots, the body retrieves the next
slot index `i` from the iterator and either terminates or updates `out_pts[i]` with the
4-byte-chunk deserialization of `v[i]`.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed the vector length or the array size (16), each serialized byte vector
  satisfies the overflow guard `(v[j]).len() + 4 ≤ Usize.max`, and the opaque
  `sorted_vec.SortedSet.with_capacity` axiom returns `ok (v_init n)` for every capacity `n`.

• In the **done** case (iterator exhausted):
    the output array is returned unchanged: `out_pts' = out_pts`,
    and the iterator condition is negated: `¬ (iter.start.val < iter.«end».val)`.

• In the **cont** case (received slot index `i = iter.start` from the range iterator):
    - `iter.start.val < iter.«end».val` — the iterator was not exhausted.
    - The iterator has advanced by one position:
        `iter1.start.val = iter.start.val + 1`,
        `iter1.«end» = iter.«end»`.
    - The output array is updated at slot `iter.start.val` with the populated sorted set, and
      every other slot is preserved:
        `out_pts'.val[iter.start.val]! = v_final`,
        `∀ k ≠ iter.start.val, out_pts'.val[k]! = out_pts.val[k]!`.
    - There is a chain of intermediate sorted-set states `vs : Nat → SortedSet Pt`, an
      iteration count `n : Nat`, and a final state `v_final = vs n` such that
      `4 · n ≤ (v[i]).len() < 4 · (n + 1)` and for every iteration `k < n` there exist a
      cartesian point `p : Pt` (over GF(2¹⁶) × GF(2¹⁶)) and `SortedSet.push` outputs
      `(m, o)` with
        `p.x.value.val = v[i][4·k]·256   + v[i][4·k+1]`,
        `p.y.value.val = v[i][4·k+2]·256 + v[i][4·k+3]`,
        `SortedSet.push (vs k) p = ok ((m, o), vs (k+1))`.

    This corresponds to the Rust body:
    ```rust
    for i in 0..16 {
        let pts = &pb.pts[i];
        let mut v = SortedSet::with_capacity(pts.len() / 4);
        let mut j = 0;
        while j + 4 <= pts.len() {
            let chunk: [u8; 4] = [pts[j], pts[j + 1], pts[j + 2], pts[j + 3]];
            v.push(Pt::deserialize(chunk));
            j += 4;
        }
        out_pts[i] = v;
    }
    ```

This establishes that one step of the outer loop faithfully deserializes a single slot of
`pb.pts` into the corresponding `SortedSet<Pt>` entry of the output array via the opaque
`SortedSet::push` axiom.

**Source**: spqr/src/encoding/polynomial.rs (lines 838:8-848:9)
-/
@[step]
theorem body_spec
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (iter : core.ops.range.Range Std.Usize)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_pts_overflow : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length + 4 ≤ Usize.max)
    (v_init : Std.Usize → sorted_vec.SortedSet Pt)
    (h_init : ∀ (n : Std.Usize),
        sorted_vec.SortedSet.with_capacity Pt.Insts.CoreCmpOrd n
          = ok (v_init n)) :
    body v iter out_pts ⦃ cf =>
      match cf with
      | ControlFlow.done out_pts' =>
          out_pts' = out_pts ∧ ¬(iter.start.val < iter.«end».val)
      | ControlFlow.cont (iter1, out_pts') =>
          iter.start.val < iter.«end».val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.«end» = iter.«end» ∧
          ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
            (vs : Nat → sorted_vec.SortedSet Pt),
            out_pts'.val[iter.start.val]! = v_final ∧
            (∀ (k : Nat), k ≠ iter.start.val →
              out_pts'.val[k]! = out_pts.val[k]!) ∧
            vs n = v_final ∧
            4 * n ≤ (v.val[iter.start.val]!).val.length ∧
            (v.val[iter.start.val]!).val.length < 4 * (n + 1) ∧
            ∀ (k : Nat), k < n →
              ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
                p.x.value.val =
                  ((v.val[iter.start.val]!).val[4 * k]!).val * 256 +
                  ((v.val[iter.start.val]!).val[4 * k + 1]!).val ∧
                p.y.value.val =
                  ((v.val[iter.start.val]!).val[4 * k + 2]!).val * 256 +
                  ((v.val[iter.start.val]!).val[4 * k + 3]!).val ∧
                sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
                  ok ((m, o), vs (k + 1)) ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ :=
    core.iter.range.IteratorRange.next_Usize_spec iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.«end».val
  · -- cont case: iterator yields the current slot index
    obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    simp  [bind_tc_ok]
    have h_i_lt_v : iter.start.val < v.val.length := by omega
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_pts_ov := h_pts_overflow iter.start.val h_i_lt_v
    -- Rewrite the opaque `with_capacity` call via the explicit witness
    simp only [h_init]
    -- Drive the body through index/len/division/inner-loop/index_mut/update
    step*
    · -- cont branch: assemble the chain witness from the inner loop spec
      simp_all only [getElem!_pos, true_and]
    · -- done branch (unreachable here: iterator already yielded a `some`)
      simp_all
      rename_i ha hb hc hd he  hf
      use v2
      use ha

  · -- done case: iterator exhausted
    obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0
