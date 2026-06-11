/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `core.result.Result.expect`

In Rust, `Result::expect(self, msg)` unwraps a `Result<T, E>`:
  - If `Ok(v)`, returns `v`.
  - If `Err(e)`, panics with message `msg`.

The Aeneas model returns `.ok v` for `Ok(v)` and `.fail .panic` for `Err(e)`.

**Source**: core/src/result.rs (Result::expect)
-/

open Aeneas Aeneas.Std Result

/--
**Spec theorem for `core.result.Result.expect` on `Ok` values**:

When the input is `.Ok v`, `expect` always succeeds and returns `v`.
-/
@[step]
theorem core.result.Result.expect_ok_spec {T E : Type}
    (inst : core.fmt.Debug E)
    (v : T) (msg : Str) :
    core.result.Result.expect inst (core.result.Result.Ok v : core.result.Result T E) msg
    ⦃ result => result = v ⦄ := by
  simp [core.result.Result.expect, WP.spec_ok]
