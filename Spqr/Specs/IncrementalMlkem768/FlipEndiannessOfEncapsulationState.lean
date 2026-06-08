/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Specs.IncrementalMlkem768.FlipEndiannessOfEncapsulationStateLoop0

/-!
# Spec theorem for `spqr::incremental_mlkem768::flip_endianness_of_encapsulation_state`

In the incremental ML-KEM-768 encapsulation pipeline, the *encapsulation state* is a byte vector
of length 2080.  Due to an endianness mismatch in libcrux (cryspen/libcrux#1275), the first
`len − 32` bytes of the state may be stored with each consecutive 16-bit word in the wrong byte
order.  The function `flip_endianness_of_encapsulation_state` corrects this by cloning the input
and swapping each pair of bytes at even-indexed positions `(2k, 2k+1)` for `0 ≤ 2k < len − 32`,
leaving the last 32 bytes untouched.

The function proceeds in two stages:
  1. `clone(es)` — clone the input byte vector into a mutable working copy `fixed_es`.
  2. `for i in (0..fixed_es.len() - 32).step_by(2) {`
     `  (fixed_es[i], fixed_es[i+1]) = (fixed_es[i+1], fixed_es[i])`
     `}` — iterate over even-indexed positions in the first `len − 32` bytes, swapping each
     consecutive byte pair.

**Source**: spqr/src/incremental_mlkem768.rs (lines 143:0-151:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/--
Helper lemma: `alloc.vec.CloneVec.clone` specialised to `U8` always succeeds and returns the
vector unchanged, because `core.clone.CloneU8.clone x = ok x` for every `x : U8`.
-/
@[step]
private theorem clone_U8_spec (v : alloc.vec.Vec Std.U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v
      ⦃ (r : alloc.vec.Vec Std.U8) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono
    (Slice.clone_spec (fun x _ => by rfl))
  intro v' h
  exact h.symm

/-- **Spec theorem for `incremental_mlkem768.flip_endianness_of_encapsulation_state`**:

Byte-swap each consecutive 16-bit word in the first `len − 32` positions of an encapsulation
state byte vector, leaving the last 32 bytes (the shared-secret portion) untouched.

The function clones the input, constructs a step-by-2 iterator over `0..(len − 32)`, and
delegates to the byte-swap loop (specified in `FlipEndiannessOfEncapsulationStateLoop0.lean`).

The result satisfies a three-part postcondition:
  - **Length preservation**: `result.length = es.length`.
  - **Byte-swap**: for every even `j` with `j < es.length - 32`:
      `result.val[j]? = es.val[j + 1]?`  and
      `result.val[j + 1]? = es.val[j]?`
  - **Frame (tail)**: for every `j ≥ es.length - 32`:
      `result.val[j]? = es.val[j]?`

This follows from composing:
  1. `clone_U8_spec`: `clone(es) = ok es` — the clone is the identity on the underlying list.
  2. `flip_endianness_of_encapsulation_state_loop.loop_spec`: the byte-swap loop swaps all
     even-indexed pairs in `[0, es.length − 32)` and preserves positions outside the range.

**Source**: spqr/src/incremental_mlkem768.rs (lines 143:0-151:1)
-/
@[step]
theorem flip_endianness_of_encapsulation_state_spec
    (es : alloc.vec.Vec Std.U8)
    (h_even : es.length % 2 = 0)
    (h_gt32 : es.length > 32) :
    incremental_mlkem768.flip_endianness_of_encapsulation_state es
      ⦃ (result : alloc.vec.Vec Std.U8) =>
        result.length = es.length ∧
        (∀ j, j < es.length - 32 → j % 2 = 0 →
          result.val[j]? = es.val[j + 1]? ∧
          result.val[j + 1]? = es.val[j]?) ∧
        (∀ j, j ≥ es.length - 32 →
          result.val[j]? = es.val[j]?) ⦄ := by
  unfold incremental_mlkem768.flip_endianness_of_encapsulation_state
  step*
  rw[core.iter.range.IteratorRange.step_by]
  split
  · simp_all
  · simp only [bind_tc_ok, alloc.vec.Vec.length, ge_iff_le, tsub_le_iff_right]
    step*
    grind  
    
end spqr.incremental_mlkem768
