/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Math.Poly.General
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPbLoopBody0

/-!
# Spec theorem for `PolyDecoder::from_pb`: loop 0

The extracted Lean function `encoding.polynomial.PolyDecoder.from_pb_loop0` is the outer
point-set-deserialization loop inside `PolyDecoder::from_pb`.  Given a `Range<usize>` iterator
over slot indices `0..16`, the vector of serialized byte vectors `v : Vec<Vec<u8>>` (one per
protobuf point-set slot), and the current output array `out_pts : [SortedSet<Pt>; 16]`, the loop
repeatedly invokes `encoding.polynomial.PolyDecoder.from_pb_loop0.body`, which at each step:

  1. Calls `next` on the range iterator to obtain the current slot index `i`.
  2. Retrieves `pts = v[i]`, the serialized byte vector for that slot.
  3. Allocates a fresh empty `SortedSet<Pt>` with capacity `pts.len() / 4` via the opaque
     `sorted_vec.SortedSet.with_capacity` axiom.
  4. Runs the inner 4-byte-chunk deserialization loop (`from_pb_loop0_loop0`) to populate the
     sorted set with cartesian points decoded from `pts` (big-endian:
     `p.x.value = pts[4·k]·256 + pts[4·k+1]`,
     `p.y.value = pts[4·k+2]·256 + pts[4·k+3]`).
  5. Stores the resulting sorted set into `out_pts[i]`.

**Loop invariant**: after processing iterations up to `iter'`, the output array satisfies, for
every slot index `j < iter'.start.val`, the existence of a chain of sorted-set states linked by
valid `SortedSet.push` operations corresponding to the cartesian points decoded from `v[j]`:

  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * `iter.start.val ≤ iter'.start.val ≤ iter'.«end».val` — the cursor only advances and never
    exceeds the iterator end.
  * For every `j < iter'.start.val`, there exist `v_final`, an iteration count `n`, and a chain
    `vs : Nat → SortedSet Pt` such that
      `out_pts'.val[j]! = v_final`, `vs n = v_final`,
      `4 · n ≤ (v[j]).len() < 4 · (n + 1)`,
      and for every `k < n` a cartesian point `p : Pt` (over GF(2¹⁶) × GF(2¹⁶)) with
        `p.x.value.val = v[j][4·k]·256   + v[j][4·k+1]`,
        `p.y.value.val = v[j][4·k+2]·256 + v[j][4·k+3]`,
        `SortedSet.push (vs k) p = ok ((m, o), vs (k+1))`.

At loop termination (`iter'.start.val ≥ iter'.«end».val`, hence
`iter'.start.val = iter.«end».val`) the output array contains the complete deserialization of
all slots in the iterator range.

The body spec (`body_spec` from `FromPbLoopBody0.lean`) discharges one step of this loop; this
file lifts it through `loop.spec_decr_nat` (with measure `iter'.«end».val − iter'.start.val`)
to give the full loop postcondition.

Because both `sorted_vec.SortedSet.with_capacity` and `sorted_vec.SortedSet.push` are extracted
as opaque axioms (no provable structural behaviour beyond their `ok`-result equations), we
parameterise the spec by an index-dependent witness `v_init : Std.Usize → SortedSet Pt` for the
`with_capacity` axiom, and the postcondition only asserts the existence of a chain of
intermediate sorted-set states linked by valid push equations; it does not relate the final
per-slot `SortedSet<Pt>` structurally to the corresponding serialized byte vector beyond the
per-iteration cartesian-point witnesses.

In GF(2¹⁶) (characteristic 2), each field element is stored as a `u16`; the big-endian two-byte
encoding satisfies `value = hi · 256 + lo`, and a `Pt` packs two such elements `(x, y)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 838:8-848:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

/-! ## Spec theorem for the from_pb outer deserialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0`**:

The full outer point-set-deserialization loop inside `PolyDecoder::from_pb`.  Given a range
iterator `iter` over slot indices, the vector of serialized byte vectors `v` (from `pb.pts`),
the current output array `out_pts` of 16 `SortedSet<Pt>` slots, and the explicit
`with_capacity` witness `v_init`, the loop drives the body to completion and returns the
populated output array.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed the vector length or the array size (`iter.«end».val ≤ v.val.length` and
  `iter.«end».val ≤ 16`), the cursor does not exceed the end (`iter.start.val ≤ iter.«end».val`),
  each serialized byte vector satisfies the overflow guard
  `(v[j]).len() + 4 ≤ Usize.max`, the opaque `sorted_vec.SortedSet.with_capacity` axiom returns
  `ok (v_init n)` for every capacity `n`, and every slot index `j < iter.start.val` already
  satisfies the chain-witness postcondition on the input `out_pts` (vacuously when
  `iter.start.val = 0`).

• **Loop postcondition**:
  For every slot index `j < iter.«end».val`, there exist a final sorted set `v_final`, an
  iteration count `n`, and a chain `vs : Nat → SortedSet Pt` such that
  - `result.val[j]! = v_final` and `vs n = v_final` — the final state of slot `j`;
  - `4 · n ≤ (v[j]).len() < 4 · (n + 1)` — exactly `n` complete 4-byte chunks were consumed
    from `v[j]`, with fewer than 4 bytes remaining;
  - for every iteration index `k < n` there exist a cartesian point `p : Pt` (over GF(2¹⁶)) and
    `push`-axiom outputs `m, o` with
      `p.x.value.val = v[j][4·k]·256   + v[j][4·k+1]`,
      `p.y.value.val = v[j][4·k+2]·256 + v[j][4·k+3]`,
      `SortedSet.push (vs k) p = ok ((m, o), vs (k+1))`.

    This corresponds to the Rust loop:
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

This establishes that the outer loop faithfully deserializes every slot of `pb.pts` in the
iterator range into the corresponding `SortedSet<Pt>` entry of the output array via the opaque
`SortedSet::push` and `SortedSet::with_capacity` axioms.

This follows from composing:
  1. `body_spec`: one step of the outer loop either terminates (iterator exhausted) or
     decodes a single slot of `v` into the corresponding `out_pts` entry, advancing the
     cursor by one.
  2. `loop.spec_decr_nat`: lifts the body spec through the decreasing measure
     `iter'.«end».val − iter'.start.val`.

**Source**: spqr/src/encoding/polynomial.rs (lines 838:8-848:9)
-/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (v_init : Std.Usize → sorted_vec.SortedSet Pt)
    (h_init : ∀ (n : Std.Usize),
        sorted_vec.SortedSet.with_capacity Pt.Insts.CoreCmpOrd n
          = ok (v_init n))
    (h_end_le_v : iter.«end».val ≤ v.val.length)
    (h_end_le_16 : iter.«end».val ≤ 16)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_pts_overflow : ∀ (j : Nat), j < v.val.length →
        (v.val[j]!).val.length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
          (vs : Nat → sorted_vec.SortedSet Pt),
          out_pts.val[j]! = v_final ∧
          vs n = v_final ∧
          4 * n ≤ (v.val[j]!).val.length ∧
          (v.val[j]!).val.length < 4 * (n + 1) ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
              p.x.value.val =
                ((v.val[j]!).val[4 * k]!).val * 256 +
                ((v.val[j]!).val[4 * k + 1]!).val ∧
              p.y.value.val =
                ((v.val[j]!).val[4 * k + 2]!).val * 256 +
                ((v.val[j]!).val[4 * k + 3]!).val ∧
              sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
                ok ((m, o), vs (k + 1))) :
    from_pb_loop0 iter v out_pts ⦃ (result : Array (sorted_vec.SortedSet Pt) 16#usize) =>
      ∀ (j : Nat), j < iter.«end».val →
        ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
          (vs : Nat → sorted_vec.SortedSet Pt),
          result.val[j]! = v_final ∧
          vs n = v_final ∧
          4 * n ≤ (v.val[j]!).val.length ∧
          (v.val[j]!).val.length < 4 * (n + 1) ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
              p.x.value.val =
                ((v.val[j]!).val[4 * k]!).val * 256 +
                ((v.val[j]!).val[4 * k + 1]!).val ∧
              p.y.value.val =
                ((v.val[j]!).val[4 * k + 2]!).val * 256 +
                ((v.val[j]!).val[4 * k + 3]!).val ∧
              sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
                ok ((m, o), vs (k + 1)) ⦄ := by
  unfold from_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                       Array (sorted_vec.SortedSet Pt) 16#usize) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     Array (sorted_vec.SortedSet Pt) 16#usize) =>
        let iter' := p.1
        let out_pts' := p.2
        iter'.«end» = iter.«end» ∧
        iter.start.val ≤ iter'.start.val ∧
        iter'.start.val ≤ iter'.«end».val ∧
        (∀ (j : Nat), j < iter'.start.val →
          ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
            (vs : Nat → sorted_vec.SortedSet Pt),
            out_pts'.val[j]! = v_final ∧
            vs n = v_final ∧
            4 * n ≤ (v.val[j]!).val.length ∧
            (v.val[j]!).val.length < 4 * (n + 1) ∧
            ∀ (k : Nat), k < n →
              ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
                p.x.value.val =
                  ((v.val[j]!).val[4 * k]!).val * 256 +
                  ((v.val[j]!).val[4 * k + 1]!).val ∧
                p.y.value.val =
                  ((v.val[j]!).val[4 * k + 2]!).val * 256 +
                  ((v.val[j]!).val[4 * k + 3]!).val ∧
                sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
                  ok ((m, o), vs (k + 1))))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', out_pts'⟩ ⟨h_end', h_orig_le, h_start_le', h_inv'⟩
    simp only [] at h_end' h_orig_le h_start_le' h_inv' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_end_le_v' : iter'.«end».val ≤ v.val.length := by omega
    have h_end_le_16' : iter'.«end».val ≤ 16 := by omega
    have h_body :=
      body_spec v iter' out_pts' h_end_le_v' h_end_le_16' h_pts_overflow v_init h_init
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out_pts'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      intro j hj
      exact h_inv' j (by omega)
    | ControlFlow.cont (iter'', out_pts'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, v_final, n, vs,
              h_slot, h_other, h_vs_n, h_n_lo, h_n_hi, h_chain⟩ := h_cf
      have h_end1_val : iter''.«end».val = iter'.«end».val := by rw [h_end1]
      refine ⟨⟨by rw [h_end1]; exact h_end',
              by omega,
              by omega,
              fun j hj => ?_⟩,
              by omega⟩
      by_cases hj_lt : j < iter'.start.val
      · -- Previously processed slot: index falls strictly below the current cursor
        obtain ⟨vf, nn, vss, h_slot', h_vs_nn, h_nn_lo, h_nn_hi, h_chain'⟩ :=
          h_inv' j hj_lt
        refine ⟨vf, nn, vss, ?_, h_vs_nn, h_nn_lo, h_nn_hi, h_chain'⟩
        have hj_ne : j ≠ iter'.start.val := by omega
        rw [← h_slot']
        grind
      · -- Newly processed slot: j = iter'.start.val
        have hj_eq : j = iter'.start.val := by omega
        subst hj_eq
        exact ⟨v_final, n, vs, h_slot, h_vs_n, h_n_lo, h_n_hi, h_chain⟩
  · -- Initial state satisfies the invariant
    exact ⟨rfl, le_refl _, h_start_le, h_pre⟩

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0
