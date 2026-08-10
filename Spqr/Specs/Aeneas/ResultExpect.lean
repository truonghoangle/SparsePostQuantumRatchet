/-
<<<<<<< HEAD
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
=======
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

<<<<<<< HEAD
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
=======
/-! # Spec theorem for `core.result.Result.expect`

`Result::expect` unwraps `Ok(v)` to `v` or panics on `Err`.
Aeneas models this as `.ok v` or `.fail .panic`. -/

open Aeneas Aeneas.Std Result

/-- **Spec theorem for `core.result.Result.expect` on `Ok` values**:
`expect` on `.Ok v` succeeds with `v`. -/
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
@[step]
theorem core.result.Result.expect_ok_spec {T E : Type}
    (inst : core.fmt.Debug E)
    (v : T) (msg : Str) :
    core.result.Result.expect inst (core.result.Result.Ok v : core.result.Result T E) msg
<<<<<<< HEAD
    ⦃ result => result = v ⦄ := by
=======
    ⦃ (result : T) => result = v ⦄ := by
>>>>>>> 323abb23ea297aa116adeb54d44a0ab5037942f5
  simp [core.result.Result.expect, WP.spec_ok]
