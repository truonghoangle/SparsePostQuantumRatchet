/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/

/-! # D10. `RoundRobinEncoder::chunk_at` panics on empty input

**Status.** `#[cfg(test)]`-only code; excluded from Aeneas extraction.
No Lean definitions exist for `RoundRobinEncoder`.

**Rust.** `src/encoding/round_robin.rs` (under `#[cfg(test)]`):
`chunk_at` computes `idx % self.num_chunks()` where `num_chunks() = data.len() / 32`.
When `data` is empty, `num_chunks() = 0` and `idx % 0` is a division-by-zero panic.

**Fix.** Return `Err` or check `num_chunks() > 0` before the modulo.

Since no Lean model exists (test-only code is not extracted), we record the defect
as a pure arithmetic fact: `n % 0` is undefined / panics in Rust. -/

/-- **D10. Division by zero when `num_chunks = 0`.**

`idx % num_chunks` panics (Rust) when `num_chunks = 0`. In Lean, `Nat.mod` is total:
`n % 0 = n` (identity, not a panic).

The Aeneas model of Rust's `%` operator uses `Usize.rem_spec` which requires the
divisor to be nonzero — when the divisor is zero, the monadic operation fails
(models the Rust panic). This theorem documents the underlying arithmetic mismatch:
Lean's `%` silently returns `n` where Rust panics.

Since `RoundRobinEncoder` is `#[cfg(test)]`-only and not extracted by Aeneas,
no monadic Lean definition exists. The defect is documented here as a pure fact. -/
theorem round_robin_div_by_zero_mismatch (idx : Nat) :
    -- In Lean, n % 0 = n (total function, no panic)
    -- In Rust, n % 0 panics (division by zero)
    idx % 0 = idx := Nat.mod_zero idx

/-- **D10. Any nonzero `idx` produces wrong result under Lean `%` semantics.**

If a hypothetical Lean model of `chunk_at` used `idx % 0` (with `num_chunks = 0`),
it would produce `idx` (not 0, not a panic). For `idx > 0`, this is a nonzero
out-of-bounds index — the wrong behaviour under any interpretation. -/
theorem round_robin_empty_wrong_index (idx : Nat) (h : idx > 0) :
    idx % 0 ≠ 0 := by
  simp [Nat.mod_zero]; omega
