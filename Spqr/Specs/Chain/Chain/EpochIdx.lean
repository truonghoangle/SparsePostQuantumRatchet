/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::Chain}::epoch_idx`

Computes the deque index for a given epoch as `links.length - 1 - (current_epoch - epoch)`.
Returns `EpochOutOfRange` if the epoch is in the future or already garbage-collected.

**Source**: spqr/src/chain.rs

## D56 audit note (MEDIUM; 32-bit — `as usize` truncation)

`chain.rs` L376: `(self.current_epoch - epoch) as usize`. On 32-bit platforms, if
`current_epoch - epoch > u32::MAX`, the `as usize` cast silently truncates, producing a
wrong deque index → the wrong epoch's keys are returned.

The Lean spec handles this via `h_diff_fits : epoch ≤ self.current_epoch →
self.current_epoch - epoch ≤ Usize.max`. On 64-bit this is trivially discharged (both
are `u64`). On 32-bit (`Usize.max = 2^32 - 1`), large epoch differences violate this
precondition. The Rust code does **not** check this at runtime — the `as usize` cast
silently truncates.

The theorem `epoch_idx_needs_usize_bound` documents this precondition dependency.

**Fix.** `usize::try_from(...).map_err(|_| Error::EpochOutOfRange(epoch))?`.
See `docs/listDefects.md` §D56, D3. -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.epoch_idx`**:

On success returns `Ok (links.length - 1 - (current_epoch - epoch))` with `self` unchanged.
Errors with `EpochOutOfRange` when `epoch > current_epoch` or the epoch was garbage-collected.

**D56 note.** The `h_diff_fits` precondition is erased in Rust (`as usize` truncates
silently on 32-bit). See D56 audit note above. -/
@[step]
theorem epoch_idx_spec (self : chain.Chain) (epoch : U64)
    (h_diff_fits : epoch ≤ self.current_epoch →
      self.current_epoch - epoch ≤ Usize.max) :
    epoch_idx self epoch ⦃ (result : (core.result.Result Usize Error) × chain.Chain) =>
      result.2 = self ∧
      match result.1 with
      | core.result.Result.Ok i =>
          epoch ≤ self.current_epoch ∧
          self.current_epoch - epoch < self.links.length.val ∧
          i = self.links.length - 1 - (self.current_epoch.val - epoch)
      | core.result.Result.Err e =>
          e = Error.EpochOutOfRange epoch ∧
          (epoch > self.current_epoch ∨
           self.current_epoch.val - epoch ≥ self.links.length) ⦄ := by
  unfold epoch_idx
  step* <;> cases System.Platform.numBits_eq <;> scalar_tac

/-- **D56: `epoch_idx_spec` correctness depends on `h_diff_fits`.**

The postcondition `i = links.length - 1 - (current_epoch - epoch)` holds only when
`h_diff_fits` guarantees the `u64 → usize` cast is lossless. On 64-bit this is trivially
true. On 32-bit, `current_epoch - epoch > u32::MAX` violates `h_diff_fits`; the Rust
`as usize` cast silently truncates, returning the wrong epoch's keys.

This theorem restates the dependency: on success, both the index correctness and the
`usize` bound hold together. -/
theorem epoch_idx_needs_usize_bound (self : chain.Chain) (epoch : U64)
    (h_diff_fits : epoch ≤ self.current_epoch →
      self.current_epoch - epoch ≤ Usize.max) :
    epoch_idx self epoch ⦃ (result : (core.result.Result Usize Error) × chain.Chain) =>
      match result.1 with
      | core.result.Result.Ok i =>
          -- D56: correctness requires the usize bound
          i = self.links.length - 1 - (self.current_epoch.val - epoch) ∧
          self.current_epoch.val - epoch ≤ Usize.max
      | core.result.Result.Err _ => True ⦄ := by
  have h := epoch_idx_spec self epoch h_diff_fits
  apply WP.spec_mono h
  intro result ⟨_, h_res⟩
  cases result with
  | mk fst snd =>
    cases fst with
    | Ok i =>
      obtain ⟨h_le, _, h_eq⟩ := h_res
      exact ⟨h_eq, h_diff_fits h_le⟩
    | Err _ => trivial

end spqr.chain.Chain
