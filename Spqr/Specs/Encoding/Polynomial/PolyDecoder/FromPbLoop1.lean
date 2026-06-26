/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.List
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPbLoopBody1

/-!
# Spec theorem for `PolyDecoder::from_pb`: loop 1

The extracted Lean function `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0` is the inner
4-byte-chunk deserialization loop inside `PolyDecoder::from_pb`.  Given the serialized byte
vector `pts : Vec<u8>` for one of the 16 protobuf point-sets, the current sorted set
`v : SortedSet<Pt>` of already-decoded cartesian evaluation points, and the current byte cursor
`j : usize`, the loop repeatedly invokes
`encoding.polynomial.PolyDecoder.from_pb_loop0_loop0.body`, which at each step:

  1. Checks whether `pts.len() ≥ j + 4`; if not, the loop terminates and `v` is returned
     unchanged.
  2. Otherwise reads the next 4 bytes `pts[j], pts[j+1], pts[j+2], pts[j+3]`.
  3. Deserializes them into a cartesian point `Pt { x, y }` over GF(2¹⁶) via `Pt::deserialize`
     (big-endian: `x.value = pts[j]·256 + pts[j+1]`,
     `y.value = pts[j+2]·256 + pts[j+3]`).
  4. Pushes the resulting point onto the sorted set via the opaque
     `sorted_vec.SortedSet.push` axiom.
  5. Advances the cursor by 4 and recurses.

**Loop invariant**: after `k` iterations starting from `(v, j)`, there is a chain of
sorted-set states `vs : Nat → SortedSet Pt` with `vs 0 = v` and `vs k` equal to the current
state, such that for every iteration `k' < k`, a cartesian point `p_{k'}` was decoded from the
4-byte chunk at offset `j + 4·k'` of `pts` and pushed onto `vs k'` to produce `vs (k'+1)`:

  * `j'.val = j.val + 4 · k` — the cursor has advanced exactly 4 bytes per iteration.
  * For every `k' < k`, there exist `p, m, o` such that:
      `p.x.value.val = pts[j + 4·k']·256 + pts[j + 4·k' + 1]`,
      `p.y.value.val = pts[j + 4·k' + 2]·256 + pts[j + 4·k' + 3]`,
      `SortedSet.push (vs k') p = ok ((m, o), vs (k'+1))`.

At loop termination (`pts.len() < j + 4·(n+1)` where `n` is the total iteration count) the
final sorted set is `vs n`.

In GF(2¹⁶) each field element is represented as a 16-bit unsigned integer; the big-endian
two-byte encoding satisfies `value = hi · 256 + lo`.  A cartesian point `Pt = (x, y)` packs two
such elements.

The body spec (`body_spec` from `FromPbLoopBody1.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure `pts.val.length + 4 − j'.val`) to
give the full loop postcondition.

Because `sorted_vec.SortedSet.push` is extracted as an opaque axiom (no provable behaviour
beyond what its `ok`-result equation states), the postcondition only asserts the existence of
a chain of states linked by valid push equations; it does not relate `v_result` to `v`
structurally.

**Source**: spqr/src/encoding/polynomial.rs (lines 842:12-846:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

/-! ## Spec theorem for the from_pb inner deserialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0`**:

The full inner 4-byte-chunk deserialization loop inside `PolyDecoder::from_pb`.  Given the
serialized byte vector `pts`, the running sorted set of decoded points `v`, and the current
byte cursor `j`, the loop drives the body to completion and returns the final sorted set.

• The function always succeeds (no panic) provided the preconditions hold: the cursor can
  advance by 4 without overflow (`j.val + 4 ≤ Usize.max`), the source byte vector itself does
  not approach `Usize.max` (`pts.val.length + 4 ≤ Usize.max`), and each opaque
  `SortedSet.push` step returns `ok`.

• **Loop postcondition**:
  There exist a total iteration count `n : Nat` and a chain of intermediate sorted-set states
  `vs : Nat → SortedSet Pt` such that
  - `vs 0 = v` and `vs n = v_result` — the chain starts at the input and ends at the result;
  - `j.val + 4 · n ≤ pts.val.length` — exactly `n` complete 4-byte chunks were consumed;
  - `pts.val.length < j.val + 4 · (n + 1)` — fewer than 4 bytes remain after the last chunk;
  - for every iteration index `k < n` there exist a cartesian point `p` (over GF(2¹⁶)) and
    `push`-axiom outputs `m, o` with
      `p.x.value.val = pts[j + 4·k]·256 + pts[j + 4·k + 1]`,
      `p.y.value.val = pts[j + 4·k + 2]·256 + pts[j + 4·k + 3]`,
      `SortedSet.push (vs k) p = ok ((m, o), vs (k+1))`.

    This corresponds to the Rust loop:
    ```rust
    while j + 4 <= pts.len() {
        let chunk: [u8; 4] = [pts[j], pts[j + 1], pts[j + 2], pts[j + 3]];
        v.push(Pt::deserialize(chunk));
        j += 4;
    }
    ```

This establishes that the inner loop faithfully deserializes a sequence of cartesian points
from their consecutive 4-byte big-endian encodings and inserts them into the sorted set via the
opaque push axiom.

This follows from composing:
  1. `body_spec`: one step of the inner loop either terminates (insufficient bytes left) or
     decodes a single big-endian 4-byte chunk into a cartesian point and pushes it onto the
     sorted set, advancing the cursor by 4.
  2. `loop.spec_decr_nat`: lifts the body spec through the decreasing measure
     `pts.val.length + 4 − j'.val`.

**Source**: spqr/src/encoding/polynomial.rs (lines 842:12-846:13)
-/
@[step]
theorem loop_spec
    (pts : alloc.vec.Vec Std.U8)
    (v : sorted_vec.SortedSet Pt)
    (j : Std.Usize)
    (h_j_overflow : j.val + 4 ≤ Usize.max)
    (h_pts_overflow : pts.val.length + 4 ≤ Usize.max)
    (h_j_le_pts : j.val ≤ pts.val.length)
    (h_v_room : v.val.length + pts.val.length + 1 ≤ Usize.max) :
    from_pb_loop0_loop0 pts v j ⦃ (v_result : sorted_vec.SortedSet Pt) =>
      ∃ (n : Nat) (vs : Nat → sorted_vec.SortedSet Pt),
        vs 0 = v ∧ vs n = v_result ∧
        j.val + 4 * n ≤ pts.val.length ∧
        pts.val.length < j.val + 4 * (n + 1) ∧
        ∀ (k : Nat), k < n →
          ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
            p.x.value.val =
              (pts.val[j.val + 4 * k]!).val * 256 +
              (pts.val[j.val + 4 * k + 1]!).val ∧
            p.y.value.val =
              (pts.val[j.val + 4 * k + 2]!).val * 256 +
              (pts.val[j.val + 4 * k + 3]!).val ∧
            sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
              ok ((m, o), vs (k + 1)) ⦄ := by
  unfold from_pb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : sorted_vec.SortedSet Pt × Std.Usize) =>
                  pts.val.length + 4 - p.2.val)
    (inv := fun (p : sorted_vec.SortedSet Pt × Std.Usize) =>
        let v' := p.1
        let j' := p.2
        j'.val + 4 ≤ Usize.max ∧
        v'.val.length + (pts.val.length - j'.val) + 1 ≤ Usize.max ∧
        (∃ (n : Nat) (vs : Nat → sorted_vec.SortedSet Pt),
          vs 0 = v ∧ vs n = v' ∧
          j'.val = j.val + 4 * n ∧
          j'.val ≤ pts.val.length ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt) (m : Std.Usize) (o : Option Pt),
              p.x.value.val =
                (pts.val[j.val + 4 * k]!).val * 256 +
                (pts.val[j.val + 4 * k + 1]!).val ∧
              p.y.value.val =
                (pts.val[j.val + 4 * k + 2]!).val * 256 +
                (pts.val[j.val + 4 * k + 3]!).val ∧
              sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd (vs k) p =
                ok ((m, o), vs (k + 1))))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨v', j'⟩ ⟨h_overflow', h_v_room', n, vs, h_v0, h_vn, h_jn, h_j_le, h_chain⟩
    simp only [] at h_overflow' h_v_room' h_v0 h_vn h_jn h_j_le h_chain ⊢
    have h_body := body_spec pts v' j' (by omega) (by omega)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done v_final =>
      simp only [] at h_cf ⊢
      obtain ⟨h_v_eq, h_not_enough⟩ := h_cf
      subst h_v_eq
      exact ⟨n, vs, h_v0, h_vn, by omega, by omega, h_chain⟩
    | ControlFlow.cont (v'', j'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_enough, h_j_eq, p, h_px, h_py, m, o, h_push⟩ := h_cf
      refine ⟨⟨by omega, ?_,
              n + 1,
              Function.update vs (n + 1) v'',
              ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · -- v_room invariant: v''.val.length + (pts.val.length - j''.val) + 1 ≤ Usize.max
        have h_ps := sorted_vec.SortedSet.push_spec Pt.Insts.CoreCmpOrd v' p (by omega)
        simp only [h_push, WP.spec_ok] at h_ps
        have h_len : v''.val.length = v'.val.length + 1 := by
          rw [h_ps.2.2]; simp
        omega
      · -- vs 0 = v after update (since 0 ≠ n + 1)
        have h0 : (0 : Nat) ≠ n + 1 := by omega
        simp_all
      · -- updated function at (n + 1) is v''
        simp
      · -- j''.val = j.val + 4 * (n + 1)
        omega
      · -- j''.val ≤ pts.val.length
        omega
      · -- chain extended for all k < n + 1
        intro k hk
        by_cases hk_lt : k < n
        · -- previously processed step: indices k and k + 1 are both ≤ n, hence ≠ n + 1
          obtain ⟨p', m', o', h_px', h_py', h_push'⟩ := h_chain k hk_lt
          refine ⟨p', m', o', h_px', h_py', ?_⟩
          have h1 : k ≠ n + 1 := by omega
          have h2 : k + 1 ≠ n + 1 := by omega
          simp_all
        · -- newly processed step: k = n
          have hk_eq : k = n := by omega
          subst hk_eq
          grind
      · -- Measure decreases
        omega
  · -- Initial state satisfies the invariant
    refine ⟨by omega, by (simp only []; omega), 0, fun _ => v, rfl, rfl, by grind, by omega, ?_⟩
    intro k hk
    omega

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0
