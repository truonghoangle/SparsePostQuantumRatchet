/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.List
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPbLoopBody2

/-!
# Spec theorem for `PolyEncoder::from_pb`: loop 2

In GF(2¹⁶) — the Galois field with 65 536 elements — each field element is represented as a
polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned integer.
The big-endian two-byte encoding satisfies `value = hi * 256 + lo` where `hi` and `lo` are the
high and low bytes respectively.

The extracted Lean function `encoding.polynomial.PolyEncoder.from_pb_loop1_loop0` is the inner
byte-deserialization loop inside the `EncoderState::Points` branch of `PolyEncoder::from_pb`.
Given a `Range<usize>` iterator over `0..(pts.len() / 2)`, the serialized byte vector `pts`, and
the current output vector of GF(2¹⁶) values `v`, the loop repeatedly invokes
`encoding.polynomial.PolyEncoder.from_pb_loop1_loop0.body`, which at each step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current index `k`.
  2. Computes `j = k * 2`, reads the two bytes `pts[j]` and `pts[j+1]`.
  3. Converts them from big-endian to a `u16` via `u16::from_be_bytes`.
  4. Wraps the result as a `GF16` via `GF16::new` and pushes it onto `v`.

**Loop invariant**: after processing iterations up to `iter'`, the output vector of GF(2¹⁶)
values satisfies:

  * `v'.val.length = v.val.length + (iter'.start.val - iter.start.val)` — each byte pair
    contributes exactly one GF(2¹⁶) element.
  * `iter'.«end» = iter.«end»` — the iterator end is unchanged across iterations.
  * The original prefix is preserved:
      `∀ j < v.val.length, v'.val[j]? = v.val[j]?`
  * For every new index `j ∈ [iter.start.val, iter'.start.val)`, the deserialized GF(2¹⁶)
    element satisfies:
      `∃ g, v'.val[v.val.length + (j - iter.start.val)]? = some g ∧
        g.value.val = pts.val[2*j]!.val * 256 + pts.val[2*j+1]!.val`

At loop termination (`iter'.start.val ≥ iter'.«end».val`), the output vector contains the
complete deserialization of all byte pairs in `pts[2*iter.start.val .. 2*iter.«end».val]`,
and the result is `ok ()`.

The body spec (`body_spec` from `FromPbLoopBody2.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.«end».val − iter'.start.val`) to give the full loop postcondition.

**Source**: spqr/src/encoding/polynomial.rs (lines 599:16-602:17)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0

/-! ## Spec theorem for the from_pb inner byte-deserialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.from_pb_loop1_loop0`**:

The full inner byte-deserialization loop inside the `EncoderState::Points` branch of
`PolyEncoder::from_pb`.  Given a range iterator `iter` over byte-pair indices, the serialized
byte vector `pts`, and the current output vector of GF(2¹⁶) values `v`, the loop drives the
body to completion and returns successfully.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end satisfies `2 * iter.«end».val ≤ pts.val.length` (ensuring that `pts[2*k]` and `pts[2*k+1]`
  are within bounds for every `k < iter.«end».val`), the iterator start does not exceed the end,
  and the output vector has room for all remaining elements without exceeding `Usize.max`.

• **Loop postcondition**:
  There exists a final accumulated vector `v'` such that:
  - `v'.val.length = v.val.length + (iter.«end».val - iter.start.val)` — the output contains
    exactly one GF(2¹⁶) element per byte pair in the range.
  - The original prefix is preserved:
      `∀ j < v.val.length, v'.val[j]? = v.val[j]?`
  - For every byte-pair index `j` in `[iter.start.val, iter.«end».val)`, the deserialized
    GF(2¹⁶) element is the big-endian reconstruction of `pts[2*j]` and `pts[2*j+1]`:
      `∃ g, v'.val[v.val.length + (j - iter.start.val)]? = some g ∧
        g.value.val = pts.val[2*j]!.val * 256 + pts.val[2*j+1]!.val`

    This corresponds to the Rust loop:
    ```rust
    for k in 0..(pts.len() / 2) {
        let j = k * 2;
        v.push(GF16::new(u16::from_be_bytes([pts[j], pts[j + 1]])));
    }
    ```

This establishes that the inner loop faithfully reconstructs all GF(2¹⁶) elements from their
big-endian two-byte encodings and appends them to the accumulator vector.

This follows from composing:
  1. `body_spec`: one step of the inner byte-deserialization loop either terminates or appends
     a correctly deserialized GF(2¹⁶) element.
  2. `loop.spec_decr_nat`: lifts the body spec through the decreasing measure
     `iter'.«end».val − iter'.start.val`.

**Source**: spqr/src/encoding/polynomial.rs (lines 599:16-602:17)
-/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Std.Usize)
    (pts : alloc.vec.Vec Std.U8)
    (v : alloc.vec.Vec encoding.gf.GF16)
    (h_end_le : 2 * iter.«end».val ≤ pts.val.length)
    (h_start_le : iter.start.val ≤ iter.«end».val)
    (h_overflow : v.val.length + (iter.«end».val - iter.start.val) ≤ Usize.max) :
    from_pb_loop1_loop0 iter pts v ⦃ (v_result : alloc.vec.Vec encoding.gf.GF16) =>
      v_result.val.length = v.val.length + (iter.«end».val - iter.start.val) ∧
      (∀ (j : Nat), j < v.val.length → v_result.val[j]? = v.val[j]?) ∧
      ∀ (j : Nat), iter.start.val ≤ j → j < iter.«end».val →
        ∃ (g : encoding.gf.GF16),
          v_result.val[v.val.length + (j - iter.start.val)]? = some g ∧
          g.value.val =
            ((pts.val[2 * j]!).val * 256 +
             (pts.val[2 * j + 1]!).val) ⦄ := by
  unfold from_pb_loop1_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                       alloc.vec.Vec encoding.gf.GF16) =>
                  p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     alloc.vec.Vec encoding.gf.GF16) =>
        let iter' := p.1
        let v' := p.2
        iter'.«end» = iter.«end» ∧
        iter.start.val ≤ iter'.start.val ∧
        iter'.start.val ≤ iter'.«end».val ∧
        v'.val.length = v.val.length + (iter'.start.val - iter.start.val) ∧
        (∀ (j : Nat), j < v.val.length → v'.val[j]? = v.val[j]?) ∧
        (∀ (j : Nat), iter.start.val ≤ j → j < iter'.start.val →
          ∃ (g : encoding.gf.GF16),
            v'.val[v.val.length + (j - iter.start.val)]? = some g ∧
            g.value.val =
              ((pts.val[2 * j]!).val * 256 +
               (pts.val[2 * j + 1]!).val)))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', v'⟩ ⟨h_end', h_start_ge, h_start_le', h_len', h_prefix', h_pre'⟩
    simp only [] at h_end' h_start_ge h_start_le' h_len' h_prefix' h_pre' ⊢
    have h_end_val : iter'.«end».val = iter.«end».val := by rw [h_end']
    have h_body := body_spec pts iter' v' (by omega) (by omega) (by omega)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done v_final =>
      simp only [] at h_cf ⊢
      obtain ⟨h_not_lt, h_eq⟩ := h_cf
      subst h_eq
      exact ⟨by omega, h_prefix', fun j hj1 hj2 => h_pre' j hj1 (by omega)⟩
    | ControlFlow.cont (iter'', v'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, g, h_v_eq, h_g_val⟩ := h_cf
      have h_end1_val : iter''.«end».val = iter'.«end».val := by rw [h_end1]
      constructor
      · -- Invariant is preserved
        refine ⟨by rw [h_end1]; exact h_end',
               by omega,
               by omega,
               by rw [h_v_eq]; simp [h_len']; omega,
               fun j hj => ?_,
               fun j hj1 hj2 => ?_⟩
        · -- Prefix preservation: previously deserialized elements are unchanged
          rw [h_v_eq, getElem?_append_of_lt _ _ (by omega)]
          exact h_prefix' j hj
        · -- New elements: byte-pair deserialization invariant
          by_cases hj_lt : j < iter'.start.val
          · -- Previously deserialized element: index falls in the prefix v'.val
            obtain ⟨g', hg', hg_val'⟩ := h_pre' j hj1 hj_lt
            refine ⟨g', ?_, hg_val'⟩
            rw [h_v_eq, getElem?_append_of_lt _ _ (by omega)]
            exact hg'
          · -- Newly appended element: j = iter'.start.val
            have hj_eq : j = iter'.start.val := by omega
            subst hj_eq
            refine ⟨g, ?_, h_g_val⟩
            rw [h_v_eq, show v.val.length + (iter'.start.val - iter.start.val) =
                             v'.val.length from by omega,
                List.getElem?_append_right (le_refl _)]
            simp
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    exact ⟨rfl, le_refl _, h_start_le, by simp, fun _ _ => rfl,
           fun _ h1 h2 => absurd h2 (by simp at h2 ⊢; omega)⟩

end spqr.encoding.polynomial.PolyEncoder.from_pb_loop1_loop0
