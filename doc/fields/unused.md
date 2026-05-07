# Unused and Repeated Lemmas/Theorems/Definitions

Analysis of `Spqr/Math/Gf.lean` and `Spqr/Specs/Encoding/Gf/`.

---

## 1. Unused in `Spqr/Math/Gf.lean`

These public lemmas in `Spqr/Math/Gf.lean` are **not referenced** by
any file under `Spqr/Specs/Encoding/Gf/`:

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `POLY_GF2_dvd_modByMonic_sub` | lemma | 517 | Shows `POLY_GF2 ∣ (p %ₘ POLY_GF2 - p)`. Only used internally by `modByMonic_modByMonic_self` (line 525). Not referenced by any Specs file. |
| `modByMonic_modByMonic_self` | lemma | 525 | Idempotence of `%ₘ POLY_GF2`. Not used by any Specs file. |

All **private** definitions in `Spqr/Math/Gf.lean` (`gf2ModAux`, `gf2Mod`,
`gf2NoDivisorOfDeg`, `gf2ModAux_preserves_dvd`, `gf2ModAux_log2_lt`,
`natToGF2Poly_natDegree_eq_log2`, `natToGF2Poly_monic_of_ge_two`,
`gf2Mod_ne_zero_of_not_dvd`, `natToGF2Poly_pow2`, `natToGF2Poly_surj`,
`monic_eq_natToGF2Poly`, `gf2NoDivisorOfDeg_POLY`, `gf2_no_divisor_all`)
are all used within the file's internal proof chain
(`POLY_GF2_irreducible` → `exists_ringHom_modByMonic` → `φ` / `hφ`).

---

## 2. Unused in `Spqr/Specs/Encoding/Gf/`

### 2.1 `Reduce/ReduceFromByte.lean` — unused definition

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `reduceByteTable_poly` | noncomputable def | 327 | Algebraic counterpart `(p * X ^ 16) %ₘ POLY_GF2`. Not used by any other file. The actual polynomial correctness is established by `reduceByteTable_eq_poly_full` in `ReduceBytes.lean`, which works directly with the `Nat`-level `reduceByteTable`. Only mentioned in comments in `PolyReduce.lean`. |

### 2.2 `GF16/Eq.lean` — unused theorem

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `gf16_eq_iff` | theorem | 64 | Structural equality ↔ value equality for `GF16`. Not referenced by any other file. |

### 2.3 `GF16/ConstSub.lean` — unused polynomial-level spec

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `const_sub_spec'` | theorem | 74 | Polynomial-level postcondition (`natToGF2Poly result = natToGF2Poly self - natToGF2Poly other`). The `@[step]` GF216-level `const_sub_spec` (line 99) is what's used by downstream proofs. |

### 2.4 `GF16/DivImpl.lean` — unused `Range<Usize>` iterator spec

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `next_spec` | `@[step]` theorem | 92 | Spec for `Range<Usize>` iterator `next`. All range-iterator proofs in the codebase use `Range<I32>` (via the private axioms `IteratorRange_next_I32_ok` / `IteratorRange_next_I32_post`), never `Range<Usize>`. The `const_div` loop in `ConstDiv.lean` uses a `while i < 16` pattern (not a `for` loop), so it bypasses the iterator infrastructure entirely. |

### 2.5 `ParallelMult.lean` — unused polynomial-level body spec

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `parallel_mult_loop_body_spec'` | theorem | 97 | Polynomial-level body spec expressing the postcondition in terms of `natToGF2Poly … %ₘ POLY_GF2`. The `@[step]` GF216-level `parallel_mult_loop_body_spec` (line 147) is what's actually used by `parallel_mult_loop_spec`. |

### 2.6 `Unaccelerated/PolyMul.lean` — unused items

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `and_one_shiftLeft_eq_zero_of_not_testBit` | private theorem | 241 | Proves `testBit k = false → n &&& (1 <<< k) = 0` (the "forward" direction). Never invoked; the proof of `poly_mul_loop_spec` uses only `not_testBit_of_and_one_shiftLeft_eq_zero` (the converse direction, line 248) and `testBit_of_and_one_shiftLeft_ne_zero` (line 231). |
| `poly_mul_spec'` | theorem | 363 | Returns `result.val = clmul a.val b.val 16`. Not used by any other file; the `@[step]` `poly_mul_spec` (polynomial-level, line 371) is used instead. |

### 2.7 `Mul2U16.lean` — unused polynomial-level spec

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `mul2_u16_spec'` | theorem | 55 | Polynomial-level postcondition for the double-product. Only consumed by `parallel_mult_loop_body_spec'` (ParallelMult.lean line 115), which is itself unused (see §2.5 above). The `@[step]` GF216-level `mul2_u16_spec` (line 77) is what's actually used. |

---

## 3. Repeated / Duplicated Definitions and Proofs

### Status of previously reported duplications

The following duplications from the previous audit have been **resolved**:

| Issue | Status | Details |
|-------|--------|---------|
| `natToGF2Poly 1 = 1` proved twice | ✅ Fixed | `natToGF2Poly_one` is now public in `Gf.lean` (line 413) and directly imported by `ONE.lean` (line 92). |
| `POLY_GF2.Monic` re-proved from scratch | ✅ Fixed | `ReduceBytes.lean` now uses `have hmonic := POLY_GF2_monic` (imported) instead of re-proving. |
| `POLY_GF2.natDegree = 16` re-proved | ✅ Fixed | `ReduceBytes.lean` now uses `have hPOLYdeg := POLY_GF2_natDegree` (imported). |
| `POLY_GF2 ≠ 1` re-proved in multiple files | ✅ Fixed | `POLY_GF2_ne_one` is now a public theorem in `Gf.lean` (line 178) and used via import in `ReduceBytes.lean`. |
| `reduceFromByteSpec_poly` duplicates `reduceByteTable_poly` | ✅ Fixed | `reduceFromByteSpec_poly` and its trivial equality theorem have been removed. |
| `poly_reduce_poly_mul_spec` duplicates `mul_spec'` | ✅ Fixed | `poly_reduce_poly_mul_spec` has been removed from `PolyReduce.lean`. |

### Remaining note

`reduceByteTable_poly` (ReduceFromByte.lean line 327) defines the same
algebraic operation — `(p * X ^ 16) %ₘ POLY_GF2` — that
`reduceByteTable_eq_poly_full` (ReduceBytes.lean line 244) proves about
the `Nat`-level `reduceByteTable`.  The definition is unused (see §2.1)
and could be removed without affecting any proof.
