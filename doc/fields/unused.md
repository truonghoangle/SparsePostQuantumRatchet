# Unused and Repeated Lemmas/Theorems/Definitions

Analysis of `Spqr/Math/Gf.lean` and `Spqr/Specs/Encoding/Gf/`.

---

## 1. Unused in `Spqr/Math/Gf.lean`

These public lemmas/theorems/definitions in `Spqr/Math/Gf.lean` are **not referenced** by
any file under `Spqr/Specs/Encoding/Gf/`:

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `natToGF2Poly_mod_eq_of_lt` | theorem | 125 | Truncation identity for values `< 2^n`. Mentioned in a comment in `PolyReduce.lean` (line 264) but never invoked in any proof. |
| `natToGF2Poly_modByMonic_eq` | lemma | 588 | Multiplicativity of `%ₘ POLY_GF2`. Not used by any Specs file. |

These **private** definitions in `Spqr/Math/Gf.lean` are unused even *within* the file:

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `gf2IrredCheck` | private def | 206 | A wrapper combining `gf2NoDivisorOfDeg` for all degrees. The actual irreducibility proof (`POLY_GF2_irreducible`) checks each degree individually via `gf2NoDivisorOfDeg_POLY` and never calls `gf2IrredCheck`. |
| `gf2IrredCheck_POLY` | private lemma | 210 | Proves `gf2IrredCheck 0x1100b = true` by `decide`, but this fact is never used by `POLY_GF2_irreducible` or any other lemma. |

---

## 2. Unused in `Spqr/Specs/Encoding/Gf/`

### 2.1 `Reduce/PolyReduce.lean` — unused cluster

The following definitions and lemmas form a self-contained "bit-by-bit reduction"
development that is **never used** downstream. The actual `poly_reduce_spec` proof
uses `polyReduceSpec_correct` via a different (two-pass table-based) path.

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `polyMod` | def | 55 | Spec-level bit-by-bit polynomial reduction. Only used by `polyMod_eq_polyMod_poly`. |
| `polyMod_poly` | noncomputable def | 85 | Algebraic counterpart of `polyMod`. Only used within this cluster. |
| `polyMod_eq_polyMod_poly` | theorem | 104 | Correspondence between `polyMod` and `polyMod_poly`. Not used elsewhere. |
| `polyMod_poly_dvd_sub` | private lemma | 135 | Supporting lemma for `polyMod_poly_eq_modByMonic`. |
| `polyMod_poly_eq_modByMonic` | theorem | 170 | Shows `polyMod_poly` preserves congruence mod `POLY_GF2`. Not used elsewhere. |

### 2.2 `Reduce/PolyReduce.lean` — other unused items

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `reduceByteTable_poly_add` | theorem | 272 | Linearity of `reduceByteTable_poly`. Not used by any proof. |
| `first_pass_congr` | theorem | 324 | First-pass congruence (alternative proof path). Not used by `poly_reduce_spec` or any other theorem. |
| `second_pass_congr` | theorem | 373 | Second-pass congruence (alternative proof path). Not used by any theorem. |
| `polyReduceSpec_eq_modByMonic` | theorem | 828 | Shows `polyReduceSpec` preserves congruence. Not used outside this file. |
| `poly_reduce_poly_mul_spec` | theorem | 886 | Proves `mul a b` satisfies the polynomial-level spec. **Duplicates** `mul_spec'` in `Unaccelerated/Mul.lean` (same postcondition, same function). Not used by any other file. |

### 2.3 `Reduce/ReduceFromByte.lean` — unused items

| Name | Kind | Line | Notes |
|------|------|------|-------|
| `reduceFromByte` | def | 277 | Low-to-high loop spec. Only feeds into lemmas that are themselves unused externally. Superseded by `reduceByteLoopFull` in `ReduceBytes.lean`. |
| `reduceFromByte_carry_eq_zero` | lemma | 351 | Only used by `reduceByteTable_eq_reduceByteTable_poly` (which is itself unused externally). |
| `reduceByteTable_eq_reduceByteTable_poly` | theorem | 366 | Proves table correctness for `k < 16` only. **Superseded** by `reduceByteTable_eq_poly_full` in `ReduceBytes.lean` (which handles `k < 256`). |
| `reduceByteTable_poly_degree_lt` | theorem | 485 | Degree bound for `reduceByteTable_poly`. Not used by any other file. |
| `reduceFromByteSpec_poly` | noncomputable def | 504 | **Identical** to `reduceByteTable_poly` (same body: `(p * X ^ 16) %ₘ POLY_GF2`). See §3 below. |
| `reduceFromByteSpec_poly_eq_reduceByteTable_poly` | theorem | 508 | Trivially true since both definitions are identical. Not used elsewhere. |
| `reduceFromByteLoopSpec_eq_reduceByteTable` | theorem | 513 | Trivially `rfl`. Not used by any other file. |
| `reduce_from_byte_poly_spec` | theorem | 581 | Polynomial-level spec for `reduce_from_byte`, restricted to `a.val < 16`. Superseded by `reduceByteTable_eq_poly_full`. Not used externally. |

### 2.4 Other unused items across Specs files

| File | Name | Kind | Notes |
|------|------|------|-------|
| `GF16/ConstSub.lean` | `const_sub_spec'` | theorem (line 74) | Polynomial-level postcondition. The `@[step]` GF216-level `const_sub_spec` is what's used by downstream proofs. |
| `GF16/Eq.lean` | `gf16_eq_iff` | theorem (line 64) | Structural equality ↔ value equality for `GF16`. Not referenced by any other file. |
| `GF16/DivImpl.lean` | `next_spec` | `@[step]` theorem (line 92) | Spec for `Range<usize>` iterator `next`. All range-iterator proofs in the codebase use `Range<I32>` (via `IteratorRange_next_I32_ok`/`IteratorRange_next_I32_post`), never `Range<Usize>`. |
| `ParallelMult.lean` | `parallel_mult_loop_body_spec'` | theorem (line 97) | Polynomial-level body spec. The `@[step]` GF216-level `parallel_mult_loop_body_spec` is what's actually used by `parallel_mult_loop_spec`. |
| `Unaccelerated/PolyMul.lean` | `poly_mul_spec'` | theorem (line 363) | Returns `result.val = clmul a.val b.val 16`. Not used by any other file; the `@[step]` `poly_mul_spec` (polynomial-level) is used instead. |

---

## 3. Repeated / Duplicated Definitions and Proofs

### 3.1 `natToGF2Poly 1 = 1` — proved twice

| File | Name | Line | Visibility |
|------|------|------|------------|
| `Spqr/Math/Gf.lean` | `natToGF2Poly_one'` | 424 | `private` |
| `Spqr/Specs/Encoding/Gf/GF16/ONE.lean` | `natToGF2Poly_one` | 74 | `private` |

Both are `private`, so `ONE.lean` cannot import the one from `Gf.lean` and must
re-prove it.  **Recommendation**: make `natToGF2Poly_one'` public (and rename to
`natToGF2Poly_one`) so that `ONE.lean` can import it.

### 3.2 `POLY_GF2.Monic` — re-proved from scratch

| File | Line | Pattern |
|------|------|---------|
| `Spqr/Math/Gf.lean` | 174 | `theorem POLY_GF2_monic` (canonical) |
| `Reduce/ReduceBytes.lean` | ~199 | `have hmonic : POLY_GF2.Monic := by unfold POLY_GF2 …` |
| `Reduce/ReduceBytes.lean` | ~253 | `have hmonic : POLY_GF2.Monic := by unfold POLY_GF2 …` |

The two occurrences in `ReduceBytes.lean` re-prove monicity from scratch instead
of writing `have hmonic := POLY_GF2_monic` (as done correctly elsewhere, e.g.
`ReduceFromByte.lean` line 369).

### 3.3 `POLY_GF2.natDegree = 16` — re-proved

| File | Line | Pattern |
|------|------|---------|
| `Spqr/Math/Gf.lean` | 182 | `theorem POLY_GF2_natDegree` (canonical) |
| `Reduce/ReduceBytes.lean` | ~258 | `have hPOLYdeg : POLY_GF2.natDegree = 16 := by unfold POLY_GF2; compute_degree!` |

Re-proved instead of using the existing `POLY_GF2_natDegree`.

### 3.4 `POLY_GF2 ≠ 1` — re-proved in multiple files

| File | Line |
|------|------|
| `Reduce/ReduceBytes.lean` | ~259 |
| `Reduce/ReduceFromByte.lean` | ~431 |

Both files prove `POLY_GF2 ≠ 1` with an identical proof pattern.
This fact is also proved (inline) in `POLY_GF2_irreducible` (Gf.lean line 492)
but is not exported as a standalone lemma.  **Recommendation**: add a public
`POLY_GF2_ne_one` lemma to `Spqr/Math/Gf.lean`.

### 3.5 `reduceFromByteSpec_poly` duplicates `reduceByteTable_poly`

| File | Name | Line | Body |
|------|------|------|------|
| `Reduce/ReduceFromByte.lean` | `reduceByteTable_poly` | 346 | `(p * X ^ 16) %ₘ POLY_GF2` |
| `Reduce/ReduceFromByte.lean` | `reduceFromByteSpec_poly` | 504 | `(p * X ^ 16) %ₘ POLY_GF2` |

Identical definitions. The theorem `reduceFromByteSpec_poly_eq_reduceByteTable_poly`
(line 508) is trivially `simp`-provable and both the definition and the theorem are
unused. **Recommendation**: remove `reduceFromByteSpec_poly` and the trivial equality theorem.

### 3.6 `poly_reduce_poly_mul_spec` duplicates `mul_spec'`

| File | Name | Line |
|------|------|------|
| `Reduce/PolyReduce.lean` | `poly_reduce_poly_mul_spec` | 886 |
| `Unaccelerated/Mul.lean` | `mul_spec'` | 69 |

Both prove the same postcondition for `spqr.encoding.gf.unaccelerated.mul`:
```
natToGF2Poly result.val = (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2
```
`poly_reduce_poly_mul_spec` is never used. **Recommendation**: remove it.
