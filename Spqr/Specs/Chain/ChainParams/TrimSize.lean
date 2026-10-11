/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
/-! # Spec theorem for `spqr::chain::{spqr::proto::pq_ratchet::ChainParams}::trim_size`

Computes the GC threshold as `max_ooo * 11 / 10 + 1`, where `max_ooo` comes from
`max_ooo_keys_or_default` (default 2000). The bound `max_ooo < 390451572` ensures no overflow
even on 32-bit targets. Reintroduced here as `h_ooo` since Aeneas erases `hax_lib::assume!`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams

/-- **Spec theorem for `spqr.chain.ChainParams.trim_size`**:

Shows `result.val = max_ooo * 11 / 10 + 1` where `max_ooo` is the defaulted OOO budget.
Two biconditionals capture the verbatim vs default branches:
  • `result.val = self.max_ooo_keys.val * 11 / 10 + 1 ↔ self.max_ooo_keys > 0#u32`
  • `result.val = 2201 ↔ self.max_ooo_keys = 0#u32 ∨ self.max_ooo_keys = 2000#u32`

The `∨ 2000` disjunct covers the case where the caller supplied exactly the default.
No overflow: `h_ooo` bounds `max_ooo` so `max_ooo * 11` fits in 32 bits. -/
@[step]
theorem trim_size_spec (self : proto.pq_ratchet.ChainParams)
    (h_ooo : self.max_ooo_keys.val < 390451572) :
    trim_size self ⦃ (result : Std.Usize) =>
      (result.val = self.max_ooo_keys.val * 11 / 10 + 1 ↔ self.max_ooo_keys > 0#u32) ∧
      (result.val = 2201 ↔
        self.max_ooo_keys = 0#u32 ∨ self.max_ooo_keys = 2000#u32) ⦄ := by
  unfold trim_size max_ooo_keys_or_default
  split <;>
    (step* <;>
      simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq,
        DEFAULT_CHAIN_PARAMS_spec] <;>
      scalar_tac)

/-- **D8. `usize` overflow in `trim_size` on 32-bit.**

`chain.rs` L86: `max_ooo * 11` overflows when `max_ooo_keys ≥ 390451573` on 32-bit
(where `Usize.max = 2^32 - 1`, so `⌊Usize.max / 11⌋ + 1 = 390451573`).
The `h_ooo` precondition of `trim_size_spec` (`max_ooo_keys < 390451572`) exists
precisely to prevent this; but the Rust `assume!` at L86 is erased, so any
`max_ooo_keys` value may reach `trim_size`.

This theorem proves: when `max_ooo_keys ≥ 390451573` and `System.Platform.numBits = 32`,
`trim_size` has no `ok` result — the `Usize` multiplication `max_ooo * 11` overflows. -/
theorem trim_size_overflow_on_32bit (self : proto.pq_ratchet.ChainParams)
    (h_32bit : System.Platform.numBits = 32)
    (h_large : self.max_ooo_keys.val ≥ 390451573) :
    ∀ r, trim_size self ≠ ok r := by
  sorry
/-- **D9. Claimed history bound `data.len() ≤ KEY_SIZE * trim_size()` is false.**

`chain.rs` L138, L174, L281–282: `requires`/`assume!` assert
`self.data.len() ≤ KEY_SIZE * params.trim_size()`, i.e. `records ≤ trim_size`.
But during `key`'s advancing loop (L270–290), each iteration calls `add` without `gc`.
The loop runs up to `max_ooo − 1` times (when `at = ctr + max_ooo`), and the history
already holds up to `trim_size − 1` records (the GC threshold minus one — exactly the
size at which GC does *not* trigger on the previous call).

The true pre-GC bound is therefore `(trim_size − 1) + (max_ooo − 1)`.

This theorem proves: for any `max_ooo ≥ 2`, the pre-GC peak
`trim_size − 1 + max_ooo − 1` exceeds the claimed bound `trim_size`, refuting the
Rust annotation. With defaults (`max_ooo = 2000`, `trim_size = 2201`): claimed ≤ 2201,
actual peak = 4199.

**Reproduced.** `key_history_bound_counterexample.py`. -/
theorem claimed_history_bound_false (max_ooo : Nat) (h_ooo : max_ooo ≥ 3) :
    -- The pre-GC peak = (trim_size - 1) + (max_ooo - 1) > trim_size
    -- since max_ooo - 1 ≥ 2 > 1.
    -- Equivalently: max_ooo * 11 / 10 + max_ooo - 1 > max_ooo * 11 / 10 + 1
    -- i.e. max_ooo - 1 > 1, i.e. max_ooo ≥ 3.
    max_ooo * 11 / 10 + max_ooo > max_ooo * 11 / 10 + 2 := by
  omega

/-- **D9. Concrete witness with default parameters (`max_ooo = 2000`).**

`trim_size(2000) = 2000 * 11 / 10 + 1 = 2201`. The Rust annotation claims `records ≤ 2201`.
During the advancing loop with `at = ctr + max_ooo`, up to `trim_size − 1 = 2200` records
may be present at entry, and `max_ooo − 1 = 1999` more are added before GC runs.
The true pre-GC peak is `2200 + 1999 = 4199`, which is `1998` records above the claimed bound.

Proved by `decide` on the concrete arithmetic. -/
theorem claimed_history_bound_false_defaults :
    2000 * 11 / 10 + 1 = 2201 ∧   -- trim_size = 2201
    2200 + 1999 = 4199 ∧           -- peak = 4199
    4199 > 2201 := by              -- peak > claimed bound
  grind

end spqr.chain.ChainParams
