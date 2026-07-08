/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAtLoopBody0

/-!
# Spec theorem for `PolyEncoder::chunk_at`: loop 0

The extracted Lean function `encoding.polynomial.PolyEncoder.chunk_at_loop` is the
chunk-serialization loop inside `PolyEncoder::chunk_at`.  Given a `Range<usize>` iterator over
`0..16`, the encoder state `self`, the chunk index `idx : U16`, and the current output byte
vector `out`, the loop repeatedly invokes
`encoding.polynomial.PolyEncoder.chunk_at_loop.body`, which at each step:

  1. Calls `next` on the `Range<usize>` iterator to obtain the current loop index `i`.
  2. Computes `total_idx = idx * 16 + i`, then derives `poly = total_idx % 16 = i` and
     `poly_idx = total_idx / 16 = idx.val`.
  3. Evaluates `self.point_at(i, idx.val)` to obtain a GF(2¹⁶) value `g`.
  4. Appends the 2-byte big-endian encoding of `g.value` to `out`:
       `out' = out ++ [hi, lo]`  where  `hi * 256 + lo = g.value`.

**Loop invariant**: after processing iterations up to `iter'`, the output byte vector satisfies:

  * `out'.val.length = out.val.length + 2 * (iter'.start.val − iter.start.val)` — each
    polynomial evaluation contributes exactly 2 bytes.
  * `iter'.end = iter.end` — the iterator end is unchanged across iterations.
  * `iter.start.val ≤ iter'.start.val` — the iterator start only advances forward.
  * `self'.idx = self.idx` — the encoder's chunk index field is preserved.
  * If the initial encoder state was `Polys`, the encoder state is unchanged throughout.
  * Points admissibility (admissible point vector lengths for the Points state) is preserved.
  * For every `j ∈ [iter.start.val, iter'.start.val)`, the big-endian encoding holds:
      `∃ g hi lo, out'[offset + 2*(j − start)]? = some hi ∧
        out'[offset + 2*(j − start) + 1]? = some lo ∧
        hi.val * 256 + lo.val = g.value.val`
  * **Polynomial identity** (Polys case): if the initial state was `Polys polys`, each
    serialized GF(2¹⁶) value `g` at position `j` satisfies
    `g.toGF216 = (polys[j]!).toGF216Poly.eval (idx.val.toGF216)`.

At loop termination (`iter'.start.val ≥ iter'.end.val`), the output vector contains the
serialized big-endian encoding of all polynomial evaluations in the range.

In GF(2¹⁶) (characteristic 2), addition coincides with subtraction and is bitwise XOR of the
16-bit encodings; multiplication is carry-less polynomial multiplication modulo the irreducible
polynomial `x¹⁶ + x¹² + x³ + x + 1` (0x1100b).

The body spec (`body_spec` from `ChunkAtLoopBody0.lean`) discharges one step of this loop;
this file lifts it through `loop.spec_decr_nat` (with measure
`iter'.end.val − iter'.start.val`) to give the full loop postcondition.

**Source**: spqr/src/encoding/polynomial.rs (lines 697:8-705:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.chunk_at_loop

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

/-! ## Spec theorem for the chunk_at serialization loop -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.chunk_at_loop`**:

The full chunk serialization loop inside `PolyEncoder::chunk_at`.  Given a range iterator `iter`
over indices `0..16`, the encoder state `self`, the chunk index `idx`, and the current output byte
vector `out`, the loop drives the body to completion and returns the updated encoder state
together with the serialized byte vector.

• The function always succeeds (no panic) provided the preconditions hold: the iterator range
  end does not exceed 16, the total index computation does not overflow Usize, the output vector
  has room for all bytes, the encoder state satisfies the admissibility conditions required by
  `point_at` (admissible point vector lengths for the Points state, bounded coefficient lengths
  for the Polys state), and the coefficient bound holds universally for any reachable Polys state.

• **Loop postcondition**:
  - `result.1.idx = self.idx` — the encoder's chunk index field is preserved.
  - `result.2.val.length = out.val.length + 2 * (iter.end.val − iter.start.val)` — the output
    contains exactly two bytes per polynomial evaluation in the range.
  - If the encoder was initially in the `Polys` state, the encoder state is unchanged:
      `∀ polys, self.s = .Polys polys → result.1 = self`.
  - For every `j ∈ [iter.start.val, iter.end.val)`, the big-endian encoding invariant holds:
      `∃ g, 256 * result.2[offset + 2*(j − start)]! +
        result.2[offset + 2*(j − start) + 1]! = g.value.val`
  - **Polynomial identity** (Polys case): if `self.s = .Polys polys`, then for every
    `j ∈ [iter.start.val, iter.end.val)`:
      `∃ g, 256 * result.2[offset + 2*(j − start)]! +
        result.2[offset + 2*(j − start) + 1]! = g.value.val ∧
        g.toGF216 = (polys[j]!).toGF216Poly.eval (idx.val.toGF216)`

    This corresponds to the Rust loop:
    ```rust
    for i in 0..16 {
        let total_idx = (idx as usize) * 16 + i;
        let poly = total_idx % 16;
        let poly_idx = total_idx / 16;
        let p = self.point_at(poly, poly_idx).value;
        out.push((p >> 8) as u8);
        out.push(p as u8);
    }
    ```

The proof lifts the body spec through `loop.spec_decr_nat` with measure
`iter'.end.val − iter'.start.val`, maintaining the byte-encoding invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 697:8-705:9)
-/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Usize)
    (self : PolyEncoder) (idx : U16)
    (out : alloc.vec.Vec U8)
    (h_end_le : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_idx_overflow : idx * 16 + 16 ≤ Usize.max)
    (h_out_overflow : out.length + 2 * iter.end ≤ Usize.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ (polys : Array Poly 16#usize),
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    chunk_at_loop iter self idx out ⦃ (result : PolyEncoder × (alloc.vec.Vec U8)) =>
      result.1.idx = self.idx ∧
      result.2.length = out.length + 2 * (iter.end - iter.start) ∧
      (∀ polys, self.s = .Polys polys → result.1 = self) ∧
      (∀ (j : Nat), iter.start ≤ j → j < iter.end →
        ∃ (g : GF16),
          256 * result.2[out.length + 2 * (j - iter.start)]!
          + result.2[out.length + 2 * (j - iter.start) + 1]! = g.value.val) ∧
      (∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), iter.start ≤ j → j < iter.end →
          ∃ (g : GF16),
            256 * result.2[out.length + 2 * (j - iter.start)]!
            + result.2[out.length + 2 * (j - iter.start) + 1]! = g.value.val ∧
            g.toGF216 = (polys[j]!).toGF216Poly.eval (idx.val.toGF216)) ⦄ := by
  unfold chunk_at_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × PolyEncoder × alloc.vec.Vec U8) =>
        p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × PolyEncoder × alloc.vec.Vec U8) =>
        p.1.end = iter.end ∧
        iter.start ≤ p.1.start ∧
        p.1.start ≤ p.1.end ∧
        p.2.1.idx = self.idx ∧
        p.2.2.val.length = out.val.length +
          2 * (p.1.start - iter.start) ∧
        (∀ polys, self.s = .Polys polys → p.2.1 = self) ∧
        (∀ pts, p.2.1.s = .Points pts →
          ∀ (j : Nat), j < 16 →
            let len := (pts[j]!).value.length
            len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
            len = 30 ∨ len = 34 ∨ len = 36) ∧
        (∀ (j : Nat), iter.start ≤ j → j < p.1.start →
          ∃ (g : encoding.gf.GF16),
             256 * p.2.2.val[out.length + 2 * (j - iter.start)]! +
             p.2.2.val[out.val.length +
              2 * (j - iter.start) + 1]! = g.value.val) ∧
        (∀ polys, self.s = .Polys polys →
          ∀ (j : Nat), iter.start ≤ j → j < p.1.start →
            ∃ (g : encoding.gf.GF16),
               256 * p.2.2.val[out.length + 2 * (j - iter.start)]! +
               p.2.2.val[out.val.length +
                2 * (j - iter.start) + 1]! = g.value.val ∧
               g.toGF216 = (polys[j]!).toGF216Poly.eval (idx.val.toGF216)))
  · rintro ⟨iter', self', out'⟩ ⟨h_end', h_iter_ge, h_start_le', h_idx', h_out_len',
                                  h_stable', h_adm', h_pre', h_poly_pre'⟩
    simp only [] at h_end' h_iter_ge h_start_le' h_idx' h_out_len' h_stable' h_adm' h_pre' ⊢
    dsimp at h_poly_pre'
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_coeff' : ∀ polys, self'.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max :=
      fun polys _ j hj => h_coeff_bound polys j hj
    by_cases h_iter_lt : iter'.start.val < iter'.end.val
    · have h_body := body_spec idx iter' self' out'
        (by omega) h_idx_overflow (by grind) h_adm' h_coeff'
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done (self'', out'') =>
        simp only [] at h_cf ⊢
        obtain ⟨_, _, h_not_lt⟩ := h_cf
        exact absurd h_iter_lt h_not_lt
      | ControlFlow.cont (iter'', self'', out'') =>
        simp only [] at h_cf ⊢
        obtain ⟨h_lt, h_start1, h_end1, g, hi, lo, h_out_eq, h_encode, h_idx1, h_match⟩ := h_cf
        constructor
        · refine ⟨by rw [h_end1]; exact h_end',
                 by grind,
                 by grind,
                 h_idx1.trans h_idx',
                 by rw [h_out_eq]; simp [h_out_len', h_start1]; grind,
                 ?_, ?_, fun j hj1 hj2 => ?_, fun polys h_polys j hj1 hj2 => ?_⟩
          · intro polys h_polys
            have h_self'_eq := h_stable' polys h_polys
            subst h_self'_eq
            simp only [h_polys] at h_match
            exact h_match.2
          · intro pts h_pts j hj
            cases h_s : self'.s with
            | Points pts' =>
              simp only [h_s] at h_match
              by_cases h_cache :
                  idx < (pts'[iter'.start]!).value.length
              · simp only [if_pos h_cache] at h_match
                rw [h_match.2] at h_pts
                exact h_adm' pts (by rw [h_s] at h_pts; grind) j hj
              · simp only [if_neg h_cache] at h_match
                simp [h_pts] at h_match
            | Polys polys' =>
              simp only [h_s] at h_match
              rw [h_match.2] at h_pts
              simp [h_s] at h_pts
          · by_cases hj_lt : j < iter'.start.val
            · grind
            · have hj_eq : j = iter'.start.val := by omega
              subst hj_eq
              grind
          · by_cases hj_lt : j < iter'.start.val
            · obtain ⟨g', h_enc', h_poly'⟩ := h_poly_pre' polys h_polys j hj1 hj_lt
              exact ⟨g', by grind, h_poly'⟩
            · have hj_eq : j = iter'.start.val := by omega
              subst hj_eq
              have h_self'_eq := h_stable' polys h_polys
              subst h_self'_eq
              simp only [h_polys] at h_match
              exact ⟨g, by grind, h_match.1⟩
        · dsimp; grind
    · unfold body
      obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
        WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter')
      rw [hnext]; simp only [bind_tc_ok]
      obtain ⟨h_opt_eq, _⟩ := h_none h_iter_lt
      subst h_opt_eq
      dsimp
      refine ⟨h_idx', ?_, h_stable', fun j hj1 hj2 => h_pre' j hj1 (by grind),
              fun polys h_polys j hj1 hj2 => h_poly_pre' polys h_polys j hj1 (by grind)⟩
      · simp [h_out_len']; grind
  · dsimp
    exact ⟨rfl, le_refl _, h_start_le, rfl, by simp, fun _ _ => rfl, h_admissible,
           fun j h1 h2 => absurd h2 (by omega),
           fun _ _ j h1 h2 => absurd h2 (by omega)⟩

end spqr.encoding.polynomial.PolyEncoder.chunk_at_loop
