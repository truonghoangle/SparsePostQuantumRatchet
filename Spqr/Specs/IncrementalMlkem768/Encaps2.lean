/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Code.FunsExternal
import Spqr.Specs.Aeneas.ResultExpect

/-!
# Spec theorem for `spqr::incremental_mlkem768::encaps2`

`encaps2` is the second half of the *incremental* ML-KEM-768 encapsulation pipeline
(libcrux's `incremental` API). Given the *encapsulation key* (`ek`, i.e. the `pk2` bytes)
and the *encapsulation state* (`es`, produced by `encaps1`), it completes the encapsulation
by running `encapsulate2` and produces the second ciphertext piece `ct2` as a byte vector.
It is exposed in Rust as

  `pub fn encaps2(ek: &EncapsulationKey, es: &EncapsulationState) -> Ciphertext2 {
       let maybe_fix = potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275(es);
       let es = maybe_fix.as_ref().unwrap_or(es);
       let ct2 = incremental::encapsulate2(
           es.as_slice().try_into().expect("size should be correct"),
           ek.as_slice().try_into().expect("size should be correct"),
       );
       ct2.value.to_vec()
   }`,

annotated with
  `#[hax_lib::requires(es.len() == 2080 && ek.len() == 1152)]`
  `#[hax_lib::ensures(|result| result.len() == 128)]`,

i.e. the output byte vector has the fixed length `128 = CIPHERTEXT2_SIZE`, the byte length
of the second ciphertext (`Ciphertext2`) in the ML-KEM-768 parameter set.

The function proceeds in six stages:
  1. `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275(es)` — an opaque
     workaround for a libcrux endianness bug (cryspen/libcrux#1275). The function returns
     `Option<Vec<u8>>`: `Some(fixed_es)` if the state needed byte-swapping, or `None`
     otherwise. In the Aeneas extraction this function is an axiom.
  2. `maybe_fix.as_ref().unwrap_or(es)` — if the fix returned `Some(v)`, use `v`; otherwise
     fall back to the original `es`. In the Aeneas extraction, `Option.as_ref` is also an
     axiom (modelling Rust's borrow semantics); we assume it behaves as the identity on pure
     values. Either way, the resulting `es1` is a `Vec U8` of length `2080`.
  3. `es.as_slice().try_into().expect(…)` — convert the 2080-byte `es1` vector to a
     fixed-size `Array U8 2080#usize` via slice-to-array conversion.
  4. `ek.as_slice().try_into().expect(…)` — convert the 1152-byte `ek` vector to a
     fixed-size `Array U8 1152#usize`.
  5. `incremental::encapsulate2(a, a1)` — the opaque ML-KEM-768 second encapsulation step,
     producing a `Ciphertext2<128>` of fixed byte length `128`. In the Aeneas extraction
     this is modelled as `fun _ _ => ok ⟨default⟩`.
  6. `ct2.value.to_slice()` → `Slice.to_vec` — convert the 128-byte ciphertext array into
     a fresh `Vec U8` of length `128`.

Composing the six stages, the byte-length specification of the result is pinned down at
exactly `128`, matching the Rust `ensures` clause.

**Source**: spqr/src/incremental_mlkem768.rs (lines 71:0-79:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **Functional contract for `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`**.

In upstream Rust, this `#[hax_lib::opaque]` function attempts to fix a libcrux endianness
bug by inspecting and potentially byte-swapping the `error2` portion of the encapsulation
state. The Rust contract specifies
  `#[hax_lib::requires(es.len() == 2080)]`
  `#[hax_lib::ensures(|result| if let Some(es) = result { es.len() == 2080 } else { true })]`,
i.e. the call never panics and any `Some` variant preserves the 2080-byte length.

In the Aeneas extraction the function is an axiom. We capture its contract as a
*definition* of the proposition: the call always succeeds (`ok`), and if it returns
`Some v`, then `v.length = es.length`.

Downstream specs take an instance of this proposition as a hypothesis rather than relying
on an axiom. -/
def potentially_fix_state_ok : Prop :=
  ∀ (es : alloc.vec.Vec Std.U8),
    ∃ (r : Option (alloc.vec.Vec Std.U8)),
      incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
        es = ok r ∧
      ∀ v, r = some v → v.length = es.length

/-- **Functional contract for `core.option.Option.as_ref`**.

In Rust, `Option::as_ref(&self)` borrows the inner value, converting `&Option<T>` to
`Option<&T>`. In the Aeneas extraction — where reference semantics are erased — this
is an axiom of type `Option T → Result (Option T)`. Functionally it is the identity
wrapped in `ok`: the call never panics and returns the same `Option` value it received.

We capture this as a proposition rather than adding a global axiom. -/
def option_as_ref_id : Prop :=
  ∀ {T : Type} (o : Option T), core.option.Option.as_ref o = ok o

/-- **Step-style spec lemma for `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`**.

Under the `potentially_fix_state_ok` hypothesis, the call always succeeds. The
postcondition records that any `Some v` in the result has `v.length = es.length`, which
(together with the input length hypothesis `es.length = 2080`) ensures that `unwrap_or`
produces a vector of length `2080` regardless of which branch is taken. -/
@[step]
private lemma potentially_fix_state_spec
    (h : potentially_fix_state_ok) (es : alloc.vec.Vec Std.U8) :
    incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es
      ⦃ (r : Option (alloc.vec.Vec Std.U8)) =>
        ∀ v, r = some v → v.length = es.length ⦄ := by
  obtain ⟨r, hr, hprop⟩ := h es
  rw [hr]; simp [WP.spec_ok]; exact hprop

/-- **Step-style spec lemma for `core.option.Option.as_ref`**.

Under the `option_as_ref_id` hypothesis, `as_ref` behaves as the identity on
`Option T` values: it always succeeds and returns the input unchanged. -/
@[step]
private lemma option_as_ref_spec
    (h : option_as_ref_id) {T : Type} (o : Option T) :
    core.option.Option.as_ref o ⦃ (r : Option T) => r = o ⦄ := by
  rw [h]; simp [WP.spec_ok]

/--
**Spec and proof concerning `incremental_mlkem768.encaps2`**:

`encaps2 ek es` runs the six-stage second-half encapsulation pipeline of the incremental
ML-KEM-768 KEM — apply the endianness workaround, convert both input byte vectors to
fixed-size arrays, invoke `encapsulate2`, and clone the resulting 128-byte ciphertext
value into a fresh `Vec U8` — and returns the result.

In the Aeneas-extracted model, the underlying cryptographic primitive
`incremental.encapsulate2` is opaque (its `Ciphertext2 128#usize` result is the `default`
inhabitant, i.e. the all-zero 128-byte array), the `potentially_fix_state` workaround is
an axiom (assumed to succeed and preserve the 2080-byte state length), and
`Option.as_ref` is an axiom (assumed to be the identity). The *byte contents* of the
resulting vector are therefore unconstrained by this spec; only the *byte length* is
pinned down, exactly matching the Rust `#[hax_lib::ensures]` annotation
`result.len() == 128`.

Concretely:

  `encaps2 ek es ⦃ (result : Vec U8) => result.length = 128 ⦄`

The proof unfolds the definition of `encaps2`, steps through the opaque
`potentially_fix_state` and `Option.as_ref` calls using the private step lemmas
(`potentially_fix_state_spec` and `option_as_ref_spec`), evaluates the pure
`Option.unwrap_or` (splitting on the `some`/`none` cases), and then dispatches
all remaining monadic steps — `Vec.as_slice`, `TryFromSharedArraySlice.try_from`,
`Result.expect` (×2), `encapsulate2`, `Array.to_slice`, and `Slice.to_vec` — via `step*`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 71:0-79:1)
-/
@[step]
theorem encaps2_spec
    (ek es : alloc.vec.Vec Std.U8)
    (hpfs : potentially_fix_state_ok)
    (har : option_as_ref_id)
    (hes : es.length = 2080) (hek : ek.length = 1152) :
    incremental_mlkem768.encaps2 ek es
      ⦃ (result : alloc.vec.Vec Std.U8) => result.length = 128 ⦄ := by
  unfold incremental_mlkem768.encaps2
  step  -- potentially_fix_state (private @[step] lemma, found by auto-search)
  step  -- Option.as_ref (private @[step] lemma, found by auto-search)
  simp only [lift, bind_tc_ok, core.option.Option.unwrap_or]
  split <;> simp <;> step*


end spqr.incremental_mlkem768
