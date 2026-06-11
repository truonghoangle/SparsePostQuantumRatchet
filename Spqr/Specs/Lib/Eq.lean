/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::SecretOutput::eq`

The `SecretOutput` enum has three variants:
```rust
#[derive(PartialEq, Debug)]
pub enum SecretOutput {
    None,
    Send(Secret),
    Recv(Secret),
}
```
where `Secret = Vec<u8>`. The `#[derive(PartialEq)]` attribute auto-generates structural equality:
two `SecretOutput` values are equal iff they are the same variant and, for `Send`/`Recv`, the inner
`Vec<u8>` payloads are pointwise equal.

After extraction the Lean definition is:
```
def SecretOutput.Insts.CoreCmpPartialEqSecretOutput.eq
  (self : SecretOutput) (other : SecretOutput) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  if self1 = other1
  then
    match self with
    | SecretOutput.None => ok true
    | SecretOutput.Send __self_0 =>
      match other with
      | SecretOutput.None => ok true
      | SecretOutput.Send __arg1_0 =>
        alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 __self_0 __arg1_0
      | SecretOutput.Recv _ => ok true
    | SecretOutput.Recv __self_0 =>
      match other with
      | SecretOutput.None => ok true
      | SecretOutput.Send _ => ok true
      | SecretOutput.Recv __arg1_0 =>
        alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU8 __self_0 __arg1_0
  else ok false
```

The function first compares discriminants; when they differ the result is `false`. When they agree
the nested matches dispatch to:
  • `None` vs `None` → `true`
  • `Send(a)` vs `Send(b)` → `PartialEqVec.eq` on the payloads
  • `Recv(a)` vs `Recv(b)` → `PartialEqVec.eq` on the payloads
(The other inner branches are dead code since the discriminants already match.)

The function is total: it never panics and always succeeds.

**Source**: spqr/src/lib.rs (line 73, `#[derive(PartialEq, Debug)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.SecretOutput

/-- `core.cmp.PartialEqU8.eq x y` reduces to `ok (decide (x = y))`. -/
private lemma PartialEqU8_eq_unfold (x y : Std.U8) :
    core.cmp.PartialEqU8.eq x y = ok (decide (x = y)) := by
  simp [core.cmp.PartialEqU8, liftFun2]

private lemma allM_zip_U8_post
    (xs ys : List Std.U8) (h_len : xs.length = ys.length) :
    ∃ b : Bool,
      List.allM
          (fun (p : Std.U8 × Std.U8) =>
            core.cmp.PartialEqU8.eq p.1 p.2)
          (List.zip xs ys) = ok b ∧
      (b = true ↔ xs = ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨true, ?_, ?_⟩
      · rfl
      · simp
    | cons y ys =>
      simp at h_len
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp at h_len
    | cons y ys =>
      have h_len' : xs.length = ys.length := by
        simpa [List.length_cons] using h_len
      obtain ⟨b, hb_eq, hb_iff⟩ := ih ys h_len'
      simp only [PartialEqU8_eq_unfold] at hb_eq
      simp only [List.zip_cons_cons, List.allM,
        PartialEqU8_eq_unfold, bind_tc_ok]
      by_cases hxy : x = y
      · subst hxy
        simp only [decide_true, hb_eq]
        refine ⟨b, by grind, ?_⟩
        rw [hb_iff]
        constructor
        · intro h_tails; rw [h_tails]
        · intro h_cons; exact (List.cons.inj h_cons).2
      · simp only [decide_eq_false_iff_not.mpr hxy]
        refine ⟨false, rfl, ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        intro h_cons
        exact hxy (List.cons.inj h_cons).1

/--
Two `SecretOutput` elements are equal (as inductive values) if and only if they are the same
variant and, for `Send`/`Recv`, the inner `Vec U8` payloads have the same backing list. This
connects propositional equality of `SecretOutput` to the observable data it carries.
-/
theorem secretOutput_eq_iff (a b : spqr.SecretOutput) :
    a = b ↔
      match a, b with
      | .None, .None => True
      | .Send va, .Send vb => va.val = vb.val
      | .Recv va, .Recv vb => va.val = vb.val
      | _, _ => False := by
  constructor
  · intro h; subst h; cases a <;> simp
  · intro h
    cases a <;> cases b <;> simp_all only [Send.injEq, Recv.injEq]
    all_goals (rename_i h; exact Subtype.ext h)

/--
**Spec theorem for `SecretOutput.Insts.CoreCmpPartialEqSecretOutput.eq`**:

• The function always succeeds (no panic / no error) for any pair of `SecretOutput` inputs. When
  the discriminants differ it short-circuits to `ok false`; when they agree it either returns
  `ok true` (for `None`–`None`) or delegates to `alloc.vec.partial_eq.PartialEqVec.eq` on the
  inner `Vec U8` payloads (for `Send`–`Send` and `Recv`–`Recv`), which is itself total.
• The result is `true` if and only if the two values are propositionally equal:
    `eq(self, other) = ok (self = other)`.
  This follows from the fact that the discriminant comparison exactly distinguishes the three
  variants, and `PartialEqVec.eq core.cmp.PartialEqU8` decides list equality for `Vec U8`.
• The relation is reflexive, symmetric, and transitive — i.e. it is a total equivalence relation,
  consistent with the `PartialEq` (and structurally derived `Eq`) trait in Rust.

**Source**: spqr/src/lib.rs (line 73, `#[derive(PartialEq, Debug)]`)
-/
@[step]
theorem eq_spec (self other : spqr.SecretOutput) :
    spqr.SecretOutput.Insts.CoreCmpPartialEqSecretOutput.eq self other
      ⦃ (result : Bool) =>
        result = true ↔ self = other ⦄ := by
  -- Use rcases (not cases) to avoid dependent elimination issues with the WP/theta
  -- match on the Result. This follows the pattern from EncodingError/Eq.lean.
  rcases self with _ | ⟨a⟩ | ⟨a⟩
  -- self = None
  · rcases other with _ | ⟨b⟩ | ⟨b⟩ <;>
      simp [Insts.CoreCmpPartialEqSecretOutput.eq, read_discriminant, WP.spec_ok]
  -- self = Send a
  · rcases other with _ | ⟨b⟩ | ⟨b⟩
    -- other = None
    · simp [Insts.CoreCmpPartialEqSecretOutput.eq, read_discriminant, WP.spec_ok]
    -- other = Send b
    · simp only [Insts.CoreCmpPartialEqSecretOutput.eq, read_discriminant,
        alloc.vec.partial_eq.PartialEqVec.eq, ite_true]
      split
      · rename_i h_len
        have h_len' : a.val.length = b.val.length := h_len
        obtain ⟨r, hr_eq, hr_iff⟩ := allM_zip_U8_post a.val b.val h_len'
        rw [hr_eq]
        simp only [WP.spec_ok]
        rw [hr_iff]
        exact (secretOutput_eq_iff (.Send a) (.Send b)).symm
      · rename_i h_len
        simp only [WP.spec_ok]
        have h_len' : ¬ a.val.length = b.val.length := h_len
        constructor
        · intro h_eq; cases h_eq
        · intro h_eq
          have := (secretOutput_eq_iff (.Send a) (.Send b)).mp h_eq
          exact absurd (congrArg List.length this) h_len'
    -- other = Recv b
    · simp [Insts.CoreCmpPartialEqSecretOutput.eq, read_discriminant, WP.spec_ok]
  -- self = Recv a
  · rcases other with _ | ⟨b⟩ | ⟨b⟩
    -- other = None
    · simp [Insts.CoreCmpPartialEqSecretOutput.eq, read_discriminant, WP.spec_ok]
    -- other = Send b
    · simp [Insts.CoreCmpPartialEqSecretOutput.eq, read_discriminant, WP.spec_ok]
    -- other = Recv b
    · simp only [Insts.CoreCmpPartialEqSecretOutput.eq, read_discriminant,
        alloc.vec.partial_eq.PartialEqVec.eq, ite_true]
      split
      · rename_i h_len
        have h_len' : a.val.length = b.val.length := h_len
        obtain ⟨r, hr_eq, hr_iff⟩ := allM_zip_U8_post a.val b.val h_len'
        rw [hr_eq]
        simp only [WP.spec_ok]
        rw [hr_iff]
        exact (secretOutput_eq_iff (.Recv a) (.Recv b)).symm
      · rename_i h_len
        simp only [WP.spec_ok]
        have h_len' : ¬ a.val.length = b.val.length := h_len
        constructor
        · intro h_eq; cases h_eq
        · intro h_eq
          have := (secretOutput_eq_iff (.Recv a) (.Recv b)).mp h_eq
          exact absurd (congrArg List.length this) h_len'

end spqr.SecretOutput
