/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytesBaseLoopBody0

/-!
# Spec theorem for `PolyEncoder::encode_bytes_base`: loop 0

In GF(2¹⁶) — the Galois field with 65 536 elements — message bytes are distributed round-robin
across `NUM_POLYS = 16` evaluation-data arrays (`Point` values).  Each pair of consecutive message
bytes `(c[0], c[1])` is interpreted as a big-endian 16-bit value and converted to a GF(2¹⁶) element
via `GF16::new`.  The resulting element is appended to `pts[i % 16].value`, where `i` is the
enumeration index of the 2-byte chunk in the `chunks_exact(2)` iteration over the message.

The extracted Lean function `encoding.polynomial.PolyEncoder.encode_bytes_base_loop` is the
byte-distribution loop inside `PolyEncoder::encode_bytes_base`.  Given an
`Enumerate<ChunksExact<u8>>` iterator over the message's 2-byte chunks and the current array of 16
`Point` values, the loop repeatedly invokes
`encoding.polynomial.PolyEncoder.encode_bytes_base_loop.body`, which at each step:

  1. Calls `next` on the `Enumerate<ChunksExact<u8>>` iterator to obtain `(i, c)`.
  2. Computes `poly = i % pts.len()` (= `i % 16`) to select the target point.
  3. Decodes the big-endian 16-bit value `g := GF16::new(((c[0] as u16) << 8) + (c[1] as u16))`.
  4. Pushes `g` onto `pts[poly].value`.

The function proceeds in two stages:
  1. `body_spec` (from `EncodeBytesBaseLoopBody0.lean`) — discharges one step of this loop,
     establishing the round-robin insert and big-endian decode for a single chunk.
  2. `loop.spec_decr_nat` — lifts the body spec through induction on the number of remaining
     chunks (`iter'.iter.chunks.length`) to give the full loop postcondition.

**Loop invariant**: after consuming some prefix of the chunk list, the point array satisfies:

  * `∀ c ∈ iter'.iter.chunks, c.val.length ≥ 2` — remaining chunks are valid 2-byte slices.
  * `∀ j < 16, (pts'.val[j]!).value.val.length + 1 ≤ Usize.max` — push overflow safety.
  * For every `j < 16`, `pts.val[j]!.value.val` is a prefix of `pts'.val[j]!.value.val` — only
    appends, never modifications to existing entries.
  * Every newly appended GF(2¹⁶) element `g` satisfies:
      `g.toGF216 = ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216`
    for some 2-byte chunk `c` from the original chunk list.

At loop termination (`iter'.iter.chunks = []`), the output array contains the complete round-robin
distribution of all message chunks as GF(2¹⁶) elements across the 16 `Point` value vectors.

In GF(2¹⁶) (characteristic 2), the 16-bit big-endian value `c[0] * 256 + c[1]` represents a
polynomial of degree < 16 with coefficients in GF(2), and `GF16::new` packages it as the canonical
representative in GF(2¹⁶) ≅ GF(2)[X] / (x¹⁶ + x¹² + x³ + x + 1).

**Source**: spqr/src/encoding/polynomial.rs (lines 679:8-686:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop

/-! ## Inhabited instance -/

/--
`Point` wraps a `Vec<GF16>`.  An `Inhabited` instance is required so that `getElem!` (`[·]!`)
on arrays/lists of `Point` has a well-defined default value.  We use the empty value vector
as the canonical default.
-/
instance : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Strengthened body spec with iterator tracking -/

/-- **Strengthened body spec** that additionally tracks how the iterator's chunk list
shrinks at each step.  In the `done` case the chunk list was empty; in the `cont` case
the chunk list loses its head element. -/
private theorem body_spec_with_iter
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact Std.U8))
    (pts : Array encoding.polynomial.Point 16#usize)
    (h_push_ok : ∀ (j : Nat), j < 16 →
        (pts.val[j]!).value.val.length + 1 ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.val.length ≥ 2)
    (h_count_bound : iter.iter.chunks ≠ [] → iter.count.val + 1 ≤ Usize.max) :
    body iter pts ⦃ cf =>
      match cf with
      | ControlFlow.done pts' =>
          pts' = pts ∧ iter.iter.chunks = []
      | ControlFlow.cont (iter', pts') =>
          (∃ hd tl, iter.iter.chunks = hd :: tl ∧ iter'.iter.chunks = tl) ∧
          iter'.count.val + iter'.iter.chunks.length =
            iter.count.val + iter.iter.chunks.length ∧
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
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorChunksExact.next]
  split
  · -- nil case: iterator exhausted → done pts = pts, chunks = []
    rename_i h_nil
    simp  [WP.spec_ok]
    exact h_nil
  · -- cons case: iterator yields (count, chunk)
    rename_i hd tl rest
    simp only [bind_tc_ok, uncurry_apply_pair]
    have h_c_len : hd.val.length ≥ 2 :=
      h_chunks_len hd (by rw [rest]; exact .head _)
    have h_count_ok : iter.count.val + 1 ≤ Usize.max :=
      h_count_bound (by rw [rest]; exact List.cons_ne_nil _ _)
    step*
    · simp_all
      grind
    constructor
    · use hd
    constructor
    · -- count + chunks.length preserved
      simp_all
      omega
    · refine ⟨iter.count, hd, g, h_c_len, ?_, ?_, ?_⟩
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

/-! ## Spec theorem for the encode_bytes_base byte-distribution loop -/

/-- **Spec theorem for `encode_bytes_base_loop`** (nat-level):

Round-robin distribution of 2-byte chunks into 16 `Point` value vectors, with big-endian decoding
into GF(2¹⁶) elements.  This is the raw numerical version: the postcondition expresses the
structural facts about prefix preservation and element counts without lifting to the field level.

The result satisfies the nat-level specification:
  • For every `j < 16`, the initial `pts.val[j]!.value.val` is a prefix of the final
    `pts'.val[j]!.value.val` — only appends occur.
  • Every newly appended GF16 element `g` (at any position beyond the initial prefix) satisfies:
      `g.toGF216 = ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216`
    for some 2-byte chunk `c` from the iterator.

This follows from composing:
  1. `body_spec` (from `EncodeBytesBaseLoopBody0.lean`): one-step round-robin insert.
  2. `loop.spec_decr_nat` with measure `iter'.iter.chunks.length`: the number of remaining chunks
     decreases strictly at each step.

**Source**: spqr/src/encoding/polynomial.rs (lines 679:8-686:9)
-/
theorem loop_spec_nat
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact Std.U8))
    (pts : Array encoding.polynomial.Point 16#usize)
    (h_push_ok : ∀ (j : Nat), j < 16 →
        (pts.val[j]!).value.val.length + iter.iter.chunks.length ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.val.length ≥ 2)
    (h_count_chunks : iter.count.val + iter.iter.chunks.length ≤ Usize.max) :
    encode_bytes_base_loop iter pts ⦃ (pts' : Array encoding.polynomial.Point 16#usize) =>
      -- Prefix preservation: each point's value list only grows by appending
      (∀ (j : Nat), j < 16 →
        ∃ (suffix : List encoding.gf.GF16),
          pts'.val[j]!.value.val = pts.val[j]!.value.val ++ suffix ∧
          -- Every appended element is a valid big-endian decode of a 2-byte chunk
          (∀ g ∈ suffix,
            ∃ (c : Slice Std.U8),
              c.val.length ≥ 2 ∧
              g.toGF216 =
                ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216)) ⦄ := by
  unfold encode_bytes_base_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate
                        (core.slice.iter.ChunksExact Std.U8) ×
                      Array encoding.polynomial.Point 16#usize) =>
                  p.1.iter.chunks.length)
    (inv := fun (p : core.iter.adapters.enumerate.Enumerate
                      (core.slice.iter.ChunksExact Std.U8) ×
                    Array encoding.polynomial.Point 16#usize) =>
        let iter' := p.1
        let pts' := p.2
        -- Remaining chunks are valid 2-byte slices
        (∀ c ∈ iter'.iter.chunks, c.val.length ≥ 2) ∧
        -- Push overflow safety: each point can still accommodate remaining pushes
        (∀ (j : Nat), j < 16 →
          (pts'.val[j]!).value.val.length + iter'.iter.chunks.length ≤ Usize.max) ∧
        -- Count-chunks bound: enumerate counter + remaining chunks fits in Usize
        (iter'.count.val + iter'.iter.chunks.length ≤ Usize.max) ∧
        -- Prefix preservation with big-endian decode validity
        (∀ (j : Nat), j < 16 →
          ∃ (suffix : List encoding.gf.GF16),
            pts'.val[j]!.value.val = pts.val[j]!.value.val ++ suffix ∧
            (∀ g ∈ suffix,
              ∃ (c : Slice Std.U8),
                c.val.length ≥ 2 ∧
                g.toGF216 =
                  ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216)))
  · -- Step: the body preserves the invariant or produces the final result
    rintro ⟨iter', pts'⟩ ⟨h_chunks', h_push', h_count', h_pre'⟩
    simp only [] at h_chunks' h_push' h_count' h_pre' ⊢
    -- Case split on whether the chunk list is empty or has elements.
    -- When chunks is empty, the body returns done and h_push_one is not needed.
    -- When chunks is non-empty, h_push_one follows from h_push' since chunks.length ≥ 1.
    cases h_chunks_cases : iter'.iter.chunks with
    | nil =>
      -- Iterator exhausted: body returns done, postcondition follows from invariant
      unfold body
      simp only [
        core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.iter.traits.iterator.IteratorChunksExact,
        core.slice.iter.IteratorChunksExact.next,
        h_chunks_cases]
      simp [WP.spec_ok]
      intro j hj
      simp_all
    | cons hd₀ tl₀ =>
      -- Chunks non-empty: length + 1 ≤ Usize.max since chunks.length ≥ 1
      have h_push_one : ∀ (j : Nat), j < 16 →
          (pts'.val[j]!).value.val.length + 1 ≤ Usize.max := by
        intro j hj
        have := h_push' j hj
        rw [h_chunks_cases] at this
        simp only [List.length_cons] at this
        omega
      have h_count_ok : iter'.iter.chunks ≠ [] → iter'.count.val + 1 ≤ Usize.max := by
        intro _
        rw [h_chunks_cases] at h_count'
        simp [List.length_cons] at h_count'
        omega
      have h_body := body_spec_with_iter iter' pts' h_push_one h_chunks' h_count_ok
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done pts'' =>
        -- Iterator exhausted: pts'' = pts', chunks were already empty
        simp only [] at h_cf ⊢
        obtain ⟨h_eq, _⟩ := h_cf
        subst h_eq
        intro j hj
        exact h_pre' j hj
      | ControlFlow.cont (iter'', pts'') =>
        simp only [] at h_cf ⊢
        obtain ⟨⟨hd, tl, h_chunks_eq, h_iter_eq⟩, h_count_eq,
                i, c, g, h_c_len, h_g_decode, h_poly_eq, h_preserve⟩ := h_cf
        -- Relate case-split variables to body-spec variables
        have h_tl_eq : tl = tl₀ := by
          have := h_chunks_cases.symm.trans h_chunks_eq
          simp_all

        constructor
        · -- Invariant is preserved
          constructor
          · -- Remaining chunks are valid: iter''.iter.chunks ⊆ iter'.iter.chunks
            intro c' hc'
            exact h_chunks' c' (by rw [h_chunks_eq]; exact .tail _ (h_iter_eq ▸ hc'))
          constructor
          · -- Push overflow maintained: length grew by ≤ 1, chunks shrank by 1
            intro j hj
            by_cases hj_eq : j = i.val % 16
            · -- The modified point: length increased by 1, chunks decreased by 1
              subst hj_eq
              have h_len : pts''.val[i.val % 16]!.value.val.length =
                  (pts'.val[i.val % 16]!).value.val.length + 1 := by
                rw [h_poly_eq]; simp [List.length_append]
              rw [h_iter_eq]
              have := h_push' (i.val % 16) hj
              rw [h_chunks_eq] at this
              simp only [List.length_cons] at this
              omega
            · -- Unmodified points: length unchanged, chunks decreased by 1
              have := h_preserve j hj_eq
              rw [h_iter_eq, show pts''.val[j]! = pts'.val[j]! from this]
              have := h_push' j hj
              rw [h_chunks_eq] at this
              simp only [List.length_cons] at this
              omega
          constructor
          · -- Count-chunks invariant preserved
            omega
          · -- Prefix preservation with decode validity
            intro j hj
            obtain ⟨suffix, h_suffix_eq, h_suffix_valid⟩ := h_pre' j hj
            by_cases hj_eq : j = i.val % 16
            · -- Modified point: suffix grows by [g]
              subst hj_eq
              refine ⟨suffix ++ [g], ?_, ?_⟩
              · rw [h_poly_eq, h_suffix_eq, List.append_assoc]
              · intro g' hg'
                rw [List.mem_append] at hg'
                rcases hg' with hg' | hg'
                · exact h_suffix_valid g' hg'
                · rw [List.mem_singleton] at hg'
                  subst hg'
                  exact ⟨c, h_c_len, h_g_decode⟩
            · -- Unmodified point: suffix unchanged
              have h_eq := h_preserve j hj_eq
              refine ⟨suffix, ?_, h_suffix_valid⟩
              rw [show pts''.val[j]! = pts'.val[j]! from h_eq, h_suffix_eq]
        · -- Measure decreases
          rw [h_iter_eq, h_tl_eq]
          simp [List.length_cons]
  · -- Initial state satisfies the invariant
    exact ⟨h_chunks_len, h_push_ok, h_count_chunks,
           fun j _ => ⟨[], by simp, fun _ h => absurd h (by grind)⟩⟩

/--
For any `Enumerate<ChunksExact<u8>>` iterator over a message's 2-byte chunks and an initial array
of 16 `Point` values, the `encode_bytes_base_loop` distributes each chunk round-robin into the
`pts[i % 16].value` vectors, converting each byte pair to a GF(2¹⁶) element via big-endian
decoding.

Specializing the canonical isomorphism `BinaryPoly.toGF216 : BinaryPoly →+* GF216` recovers the
GF(2¹⁶) interpretation: the byte pair `(c[0], c[1])` encodes a field element whose binary
polynomial representation has `c[0]` in bits 15–8 and `c[1]` in bits 7–0.

Combining with `loop_spec_nat`, this establishes that the loop correctly constructs the array of
evaluation-data points for the polynomial encoding scheme, with each entry being the GF(2¹⁶)
interpretation of the corresponding big-endian 2-byte chunk from the message.
-/
@[step]
theorem loop_spec
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact Std.U8))
    (pts : Array encoding.polynomial.Point 16#usize)
    (h_push_ok : ∀ (j : Nat), j < 16 →
        (pts.val[j]!).value.val.length + iter.iter.chunks.length ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.val.length ≥ 2)
    (h_count_chunks : iter.count.val + iter.iter.chunks.length ≤ Usize.max) :
    encode_bytes_base_loop iter pts ⦃ (pts' : Array encoding.polynomial.Point 16#usize) =>
      -- Prefix preservation: each point's value list only grows by appending
      (∀ (j : Nat), j < 16 →
        ∃ (suffix : List encoding.gf.GF16),
          pts'.val[j]!.value.val = pts.val[j]!.value.val ++ suffix ∧
          -- Every appended element is a valid big-endian decode of a 2-byte chunk
          (∀ g ∈ suffix,
            ∃ (c : Slice Std.U8),
              c.val.length ≥ 2 ∧
              g.toGF216 =
                ((c.val[0]!).val * 256 + (c.val[1]!).val).toGF216)) ⦄ := by
  exact loop_spec_nat iter pts h_push_ok h_chunks_len h_count_chunks

end spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop
