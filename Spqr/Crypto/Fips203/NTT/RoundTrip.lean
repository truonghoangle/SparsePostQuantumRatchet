/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.NTT.MultiplyNTTs
import Spqr.Crypto.Fips203.NTT.InvNTT
import Spqr.Crypto.Fips203.NTT.Spec
/-!
# FIPS 203 NTT Round-Trip and Multiplicative Homomorphism

NIST FIPS 203 (ML-KEM, August 2024), § 4.3, specifies the forward NTT (Algorithm 7)
and inverse NTT (Algorithm 8) as mutually inverse maps on `ℤ_q^{256}`.  Together with
`MultiplyNTTs` (Algorithm 9), they satisfy two fundamental identities:

1. **Round-trip**: `NTT⁻¹ ∘ NTT = id` and `NTT ∘ NTT⁻¹ = id`.
2. **Multiplicative homomorphism**: For polynomials `f, g ∈ R_q`,
   `NTT(f · g) = MultiplyNTTs(NTT(f), NTT(g))`.

The round-trip property is axiomatised only on the 256 standard basis vectors
(`invNtt_ntt_delta`, a finite set of concrete `ℤ_q` computations justified by
FIPS 203 correctness) and extended to all of `ℤ_q^{256}` by linearity of both
transforms; the reverse direction follows by finiteness and injectivity.
The multiplicative homomorphism encapsulates the CRT
isomorphism `R_q ≅ ∏ᵢ ℤ_q[X]/(X² − γᵢ)`.

**Source**: NIST FIPS 203, § 4.3 (Algorithms 7–10)
-/

noncomputable section

namespace Fips203

/-! ## Standard basis vectors -/

/-- The `j`-th standard basis vector `δⱼ` of `ℤ_q^{256}`. -/
def delta (j : Fin n) : Fin n → Zq := fun i => if i = j then 1 else 0

/-- Every coefficient vector is the linear combination `∑ⱼ f(j) · δⱼ`. -/
lemma eq_sum_delta (f : Fin n → Zq) :
    f = fun i => ∑ j : Fin n, f j * delta j i := by
  funext i
  simp [delta]

/-! ## Finite-sum linearity of the transforms -/

/-- `ntt` commutes with finite sums (from `ntt_zero` and `ntt_add`). -/
lemma ntt_sum (s : Finset (Fin n)) (g : Fin n → Fin n → Zq) :
    ntt (fun i => ∑ j ∈ s, g j i) = fun i => ∑ j ∈ s, ntt (g j) i := by
  induction s using Finset.induction_on with
  | empty => simpa using ntt_zero
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, g j i)
        = fun i => g a i + ∑ j ∈ s, g j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, ntt_add, ih]
    funext i
    simp [Finset.sum_insert ha]

/-- `invNtt` commutes with finite sums (from `invNtt_zero` and `invNtt_add`). -/
lemma invNtt_sum (s : Finset (Fin n)) (g : Fin n → Fin n → Zq) :
    invNtt (fun i => ∑ j ∈ s, g j i) = fun i => ∑ j ∈ s, invNtt (g j) i := by
  induction s using Finset.induction_on with
  | empty => simpa using invNtt_zero
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, g j i)
        = fun i => g a i + ∑ j ∈ s, g j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, invNtt_add, ih]
    funext i
    simp [Finset.sum_insert ha]

/-! ## Round-trip lemmas -/

/-- **Round trip on basis vectors** (axiomatised).  For each of the 256
standard basis vectors `δⱼ`, Algorithm 8 applied after Algorithm 7 returns
`δⱼ`.  This is a finite set of concrete `ℤ_q` computations guaranteed by
FIPS 203 § 4.3 correctness of the Cooley–Tukey / Gentleman–Sande butterfly
pair together with the final `128⁻¹ = 3303` scaling. -/
axiom invNtt_ntt_delta (j : Fin n) : invNtt (ntt (delta j)) = delta j

/-- **`NTT⁻¹(NTT(f)) = f`** — Algorithm 8 undoes Algorithm 7.  Proved by
decomposing `f = ∑ⱼ f(j) · δⱼ` and using linearity of both transforms
together with the basis-vector round trip `invNtt_ntt_delta`. -/
lemma invNtt_ntt (f : Fin n → Zq) : invNtt (ntt f) = f := by
  have h1 : ntt f = fun i => ∑ j : Fin n, f j * ntt (delta j) i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [ntt_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (ntt_smul (f j) (delta j)) i
  have h2 : invNtt (ntt f) = fun i => ∑ j : Fin n, f j * invNtt (ntt (delta j)) i := by
    rw [h1, invNtt_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (invNtt_smul (f j) (ntt (delta j))) i
  rw [h2]
  simp only [invNtt_ntt_delta]
  exact (eq_sum_delta f).symm

/-- **`NTT(NTT⁻¹(f̂)) = f̂`** — Algorithm 7 undoes Algorithm 8.  Derived from
`invNtt_ntt`: a left-inverse on a finite type is a two-sided inverse. -/
lemma ntt_invNtt (f : Fin n → Zq) : ntt (invNtt f) = f := by
  have hinj : Function.Injective (ntt : (Fin n → Zq) → Fin n → Zq) := by
    intro a b hab
    have h := congrArg invNtt hab
    rwa [invNtt_ntt, invNtt_ntt] at h
  obtain ⟨g, hg⟩ := Finite.surjective_of_injective hinj f
  rw [← hg, invNtt_ntt]


/-! ## Multiplicative homomorphism -/

/-- Polynomial multiplication in `R_q` at the coefficient-vector level. -/
def polyMulCoeffs (f g : Fin n → Zq) : Fin n → Zq :=
  Rq.toCoeffs (Rq.ofCoeffs f * Rq.ofCoeffs g)

/-! ### Linearity of `Rq.ofCoeffs` and `Rq.toCoeffs` -/

/-- `Rq.ofCoeffs` of the zero vector is `0`. -/
lemma ofCoeffs_zero : Rq.ofCoeffs (fun _ => (0 : Zq)) = 0 := by
  simp [Rq.ofCoeffs]

/-- `Rq.ofCoeffs` is additive. -/
lemma ofCoeffs_add (f g : Fin n → Zq) :
    Rq.ofCoeffs (fun i => f i + g i) = Rq.ofCoeffs f + Rq.ofCoeffs g := by
  unfold Rq.ofCoeffs
  rw [← map_add, ← Finset.sum_add_distrib]
  exact congrArg (AdjoinRoot.mk cycloPoly)
    (Finset.sum_congr rfl fun i _ => by rw [map_add]; ring)

/-- `Rq.ofCoeffs` turns coefficientwise scaling into multiplication by the
constant polynomial `C c`. -/
lemma ofCoeffs_smul (c : Zq) (f : Fin n → Zq) :
    Rq.ofCoeffs (fun i => c * f i)
      = AdjoinRoot.mk cycloPoly (Polynomial.C c) * Rq.ofCoeffs f := by
  unfold Rq.ofCoeffs
  rw [← map_mul, Finset.mul_sum]
  exact congrArg (AdjoinRoot.mk cycloPoly)
    (Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring)

/-- `Rq.toCoeffs 0 = 0`. -/
lemma toCoeffs_zero : Rq.toCoeffs 0 = fun _ => (0 : Zq) := by
  funext i
  simp [Rq.toCoeffs]

/-- `Rq.toCoeffs` is additive. -/
lemma toCoeffs_add (r s : Rq) :
    Rq.toCoeffs (r + s) = fun i => Rq.toCoeffs r i + Rq.toCoeffs s i := by
  funext i
  simp [Rq.toCoeffs, map_add]

/-- `Rq.toCoeffs` commutes with scaling by a constant polynomial. -/
lemma toCoeffs_smul (c : Zq) (r : Rq) :
    Rq.toCoeffs (AdjoinRoot.mk cycloPoly (Polynomial.C c) * r)
      = fun i => c * Rq.toCoeffs r i := by
  funext i
  have h : AdjoinRoot.mk cycloPoly (Polynomial.C c) * r = c • r := by
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq]; rfl
  rw [h]
  simp [Rq.toCoeffs, map_smul]

/-! ### Bilinearity of `polyMulCoeffs` -/

/-- Commutativity of `polyMulCoeffs`. -/
lemma polyMulCoeffs_comm (f g : Fin n → Zq) :
    polyMulCoeffs f g = polyMulCoeffs g f := by
  unfold polyMulCoeffs; rw [mul_comm]

/-- Left annihilation for `polyMulCoeffs`. -/
lemma polyMulCoeffs_zero_left (g : Fin n → Zq) :
    polyMulCoeffs (fun _ => 0) g = fun _ => 0 := by
  unfold polyMulCoeffs
  rw [ofCoeffs_zero, zero_mul, toCoeffs_zero]

/-- Right annihilation for `polyMulCoeffs`. -/
lemma polyMulCoeffs_zero_right (f : Fin n → Zq) :
    polyMulCoeffs f (fun _ => 0) = fun _ => 0 := by
  rw [polyMulCoeffs_comm]; exact polyMulCoeffs_zero_left f

/-- Left additivity of `polyMulCoeffs`. -/
lemma polyMulCoeffs_add_left (f f' g : Fin n → Zq) :
    polyMulCoeffs (fun i => f i + f' i) g =
      fun i => polyMulCoeffs f g i + polyMulCoeffs f' g i := by
  unfold polyMulCoeffs
  rw [ofCoeffs_add, add_mul, toCoeffs_add]

/-- Right additivity of `polyMulCoeffs`. -/
lemma polyMulCoeffs_add_right (f g g' : Fin n → Zq) :
    polyMulCoeffs f (fun i => g i + g' i) =
      fun i => polyMulCoeffs f g i + polyMulCoeffs f g' i := by
  rw [polyMulCoeffs_comm, polyMulCoeffs_add_left,
    polyMulCoeffs_comm g f, polyMulCoeffs_comm g' f]

/-- Left scaling of `polyMulCoeffs`. -/
lemma polyMulCoeffs_smul_left (c : Zq) (f g : Fin n → Zq) :
    polyMulCoeffs (fun i => c * f i) g = fun i => c * polyMulCoeffs f g i := by
  unfold polyMulCoeffs
  rw [ofCoeffs_smul, mul_assoc, toCoeffs_smul]

/-- Right scaling of `polyMulCoeffs`. -/
lemma polyMulCoeffs_smul_right (c : Zq) (f g : Fin n → Zq) :
    polyMulCoeffs f (fun i => c * g i) = fun i => c * polyMulCoeffs f g i := by
  rw [polyMulCoeffs_comm, polyMulCoeffs_smul_left, polyMulCoeffs_comm g f]

/-- `polyMulCoeffs` commutes with finite sums in the left argument. -/
lemma polyMulCoeffs_sum_left (s : Finset (Fin n)) (F : Fin n → Fin n → Zq)
    (g : Fin n → Zq) :
    polyMulCoeffs (fun i => ∑ j ∈ s, F j i) g =
      fun i => ∑ j ∈ s, polyMulCoeffs (F j) g i := by
  induction s using Finset.induction_on with
  | empty => simpa using polyMulCoeffs_zero_left g
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, F j i)
        = fun i => F a i + ∑ j ∈ s, F j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, polyMulCoeffs_add_left, ih]
    funext i
    simp [Finset.sum_insert ha]

/-- `polyMulCoeffs` commutes with finite sums in the right argument. -/
lemma polyMulCoeffs_sum_right (s : Finset (Fin n)) (f : Fin n → Zq)
    (G : Fin n → Fin n → Zq) :
    polyMulCoeffs f (fun i => ∑ k ∈ s, G k i) =
      fun i => ∑ k ∈ s, polyMulCoeffs f (G k) i := by
  rw [polyMulCoeffs_comm, polyMulCoeffs_sum_left]
  funext i
  exact Finset.sum_congr rfl fun k _ => congrFun (polyMulCoeffs_comm (G k) f) i

/-! ### Finite-sum linearity of `multiplyNTTs` -/

/-- `multiplyNTTs` commutes with finite sums in the left argument. -/
lemma multiplyNTTs_sum_left (s : Finset (Fin n)) (F : Fin n → Fin n → Zq)
    (gh : Fin n → Zq) :
    multiplyNTTs (fun i => ∑ j ∈ s, F j i) gh =
      fun i => ∑ j ∈ s, multiplyNTTs (F j) gh i := by
  induction s using Finset.induction_on with
  | empty => simpa using multiplyNTTs_zero_left gh
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, F j i)
        = fun i => F a i + ∑ j ∈ s, F j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, multiplyNTTs_add_left, ih]
    funext i
    simp [Finset.sum_insert ha]

/-- `multiplyNTTs` commutes with finite sums in the right argument. -/
lemma multiplyNTTs_sum_right (s : Finset (Fin n)) (fh : Fin n → Zq)
    (G : Fin n → Fin n → Zq) :
    multiplyNTTs fh (fun i => ∑ k ∈ s, G k i) =
      fun i => ∑ k ∈ s, multiplyNTTs fh (G k) i := by
  induction s using Finset.induction_on with
  | empty => simpa using multiplyNTTs_zero_right fh
  | insert a s ha ih =>
    have h1 : (fun i => ∑ k ∈ insert a s, G k i)
        = fun i => G a i + ∑ k ∈ s, G k i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, multiplyNTTs_add_right, ih]
    funext i
    simp [Finset.sum_insert ha]

/-- **Butterfly correctness** (axiomatised).  The imperative Cooley–Tukey
butterfly network of Algorithm 7 (`ntt`) computes the algebraically defined
CRT projection `nttSpec` of `Spec.lean` — i.e. coefficient pair `(2i, 2i+1)`
of the output is the image of the input polynomial in `ℤ_q[X]/(X² − γᵢ)`.

This is the single remaining link between the FIPS 203 § 4.3 pseudocode and
its mathematical specification.  Removing it requires a layer-by-layer loop
invariant for `nttInnerLoop`/`nttMiddleLoop`/`nttOuterLoop` of the form
"after processing block length `len`, each contiguous block of size `2·len`
holds the coefficients of `f mod (X^{2·len} − ζ^{bitRev-indexed power})`",
together with the `bitRev7Table` index bookkeeping — a substantial but
self-contained formalization roadmap:

1. closed-form lemma for `nttInnerLoop` as a parallel butterfly on a block;
2. invariant: one `nttMiddleLoop` layer splits each residue
   `f mod (X^{2len} − γ²)` into `f mod (X^{len} ± γ)`;
3. induction over `nttLens = [128, 64, 32, 16, 8, 4, 2]` connecting the
   threaded zeta index `k` with `bitRev7Table`;
4. base case: blocks of size 2 are exactly the `crtHom i` coordinates. -/
axiom ntt_eq_nttSpec : (ntt : (Fin n → Zq) → Fin n → Zq) = nttSpec

/-- **CRT isomorphism on basis vectors**.  For each pair of
standard basis vectors `δⱼ, δₖ`, the NTT of their product in `R_q` equals the
componentwise `MultiplyNTTs` product of their NTTs.  Proved from the
butterfly-correctness bridge `ntt_eq_nttSpec` together with the fully proven
CRT multiplicativity `nttSpec_toCoeffs_mul` and the coefficient round trip
`toCoeffs_ofCoeffs` of `Spec.lean`:  the NTT realises the CRT isomorphism
`R_q ≅ ∏ᵢ ℤ_q[X]/(X² − γᵢ)` under which ring multiplication corresponds to
`BaseCaseMultiply` on each component. -/
lemma ntt_polyMul_delta (j k : Fin n) :
    ntt (polyMulCoeffs (delta j) (delta k)) =
      multiplyNTTs (ntt (delta j)) (ntt (delta k)) := by
  rw [ntt_eq_nttSpec]
  unfold polyMulCoeffs
  rw [nttSpec_toCoeffs_mul, toCoeffs_ofCoeffs, toCoeffs_ofCoeffs]

/-- **`NTT(f · g) = MultiplyNTTs(NTT(f), NTT(g))`** — the CRT isomorphism.
Proved by decomposing `f = ∑ⱼ f(j)·δⱼ` and `g = ∑ₖ g(k)·δₖ` and expanding both
sides into the double sum `∑ⱼ ∑ₖ f(j)·g(k)·(…)` using bilinearity of
`polyMulCoeffs` and `multiplyNTTs` together with linearity of `ntt`; the
summands then agree by the basis-vector identity `ntt_polyMul_delta`. -/
lemma ntt_polyMul (f g : Fin n → Zq) :
    ntt (polyMulCoeffs f g) = multiplyNTTs (ntt f) (ntt g) := by
  have hdg : ∀ j : Fin n, polyMulCoeffs (delta j) g
      = fun i => ∑ k : Fin n, g k * polyMulCoeffs (delta j) (delta k) i := by
    intro j
    conv_lhs => rw [eq_sum_delta g]
    rw [polyMulCoeffs_sum_right]
    funext i
    exact Finset.sum_congr rfl fun k _ =>
      congrFun (polyMulCoeffs_smul_right (g k) (delta j) (delta k)) i
  have hfg : polyMulCoeffs f g
      = fun i => ∑ j : Fin n, f j * polyMulCoeffs (delta j) g i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [polyMulCoeffs_sum_left]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (polyMulCoeffs_smul_left (f j) (delta j) g) i
  have hL : ntt (polyMulCoeffs f g)
      = fun i => ∑ j : Fin n, ∑ k : Fin n,
          f j * (g k * ntt (polyMulCoeffs (delta j) (delta k)) i) := by
    rw [hfg, ntt_sum]
    funext i
    refine Finset.sum_congr rfl fun j _ => ?_
    calc ntt (fun i => f j * polyMulCoeffs (delta j) g i) i
        = f j * ntt (polyMulCoeffs (delta j) g) i :=
          congrFun (ntt_smul (f j) (polyMulCoeffs (delta j) g)) i
      _ = f j * ntt (fun i => ∑ k : Fin n,
            g k * polyMulCoeffs (delta j) (delta k) i) i := by rw [hdg j]
      _ = f j * ∑ k : Fin n,
            ntt (fun i => g k * polyMulCoeffs (delta j) (delta k) i) i := by
          rw [ntt_sum Finset.univ
            (fun k i => g k * polyMulCoeffs (delta j) (delta k) i)]
      _ = ∑ k : Fin n,
            f j * (g k * ntt (polyMulCoeffs (delta j) (delta k)) i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [congrFun (ntt_smul (g k) (polyMulCoeffs (delta j) (delta k))) i]
  have hnf : ntt f = fun i => ∑ j : Fin n, f j * ntt (delta j) i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [ntt_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ => congrFun (ntt_smul (f j) (delta j)) i
  have hng : ntt g = fun i => ∑ k : Fin n, g k * ntt (delta k) i := by
    conv_lhs => rw [eq_sum_delta g]
    rw [ntt_sum]
    funext i
    exact Finset.sum_congr rfl fun k _ => congrFun (ntt_smul (g k) (delta k)) i
  have hR : multiplyNTTs (ntt f) (ntt g)
      = fun i => ∑ j : Fin n, ∑ k : Fin n,
          f j * (g k * multiplyNTTs (ntt (delta j)) (ntt (delta k)) i) := by
    rw [hnf, hng, multiplyNTTs_sum_left]
    funext i
    refine Finset.sum_congr rfl fun j _ => ?_
    calc multiplyNTTs (fun i => f j * ntt (delta j) i)
            (fun i => ∑ k : Fin n, g k * ntt (delta k) i) i
        = f j * multiplyNTTs (ntt (delta j))
            (fun i => ∑ k : Fin n, g k * ntt (delta k) i) i :=
          congrFun (multiplyNTTs_smul_left (f j) (ntt (delta j))
            (fun i => ∑ k : Fin n, g k * ntt (delta k) i)) i
      _ = f j * ∑ k : Fin n,
            multiplyNTTs (ntt (delta j)) (fun i => g k * ntt (delta k) i) i := by
          rw [multiplyNTTs_sum_right Finset.univ
            (ntt (delta j)) (fun k i => g k * ntt (delta k) i)]
      _ = ∑ k : Fin n,
            f j * (g k * multiplyNTTs (ntt (delta j)) (ntt (delta k)) i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [congrFun (multiplyNTTs_smul_right (g k)
              (ntt (delta j)) (ntt (delta k))) i]
  rw [hL, hR]
  funext i
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
    rw [ntt_polyMul_delta]


/-! ## Derived round-trip theorems -/

/-- `invNtt ∘ ntt = id` (function composition form). -/
theorem invNtt_comp_ntt : invNtt ∘ ntt = (id : (Fin n → Zq) → Fin n → Zq) := by
  ext f i; simp only [Function.comp, id]; exact congrFun (invNtt_ntt f) i

/-- `ntt ∘ invNtt = id` (function composition form). -/
theorem ntt_comp_invNtt : ntt ∘ invNtt = (id : (Fin n → Zq) → Fin n → Zq) := by
  ext f i; simp only [Function.comp, id]; exact congrFun (ntt_invNtt f) i

/-- `ntt` is injective. -/
theorem ntt_injective : Function.Injective (ntt : (Fin n → Zq) → Fin n → Zq) := by
  intro f g h; have := congrArg invNtt h; rwa [invNtt_ntt, invNtt_ntt] at this

/-- `invNtt` is injective. -/
theorem invNtt_injective : Function.Injective (invNtt : (Fin n → Zq) → Fin n → Zq) := by
  intro f g h; have := congrArg ntt h; rwa [ntt_invNtt, ntt_invNtt] at this

/-- `ntt` is surjective. -/
theorem ntt_surjective : Function.Surjective (ntt : (Fin n → Zq) → Fin n → Zq) :=
  fun fh => ⟨invNtt fh, ntt_invNtt fh⟩

/-- `invNtt` is surjective. -/
theorem invNtt_surjective : Function.Surjective (invNtt : (Fin n → Zq) → Fin n → Zq) :=
  fun f => ⟨ntt f, invNtt_ntt f⟩

/-- `ntt` is bijective. -/
theorem ntt_bijective : Function.Bijective (ntt : (Fin n → Zq) → Fin n → Zq) :=
  ⟨ntt_injective, ntt_surjective⟩

/-- `invNtt` is bijective. -/
theorem invNtt_bijective : Function.Bijective (invNtt : (Fin n → Zq) → Fin n → Zq) :=
  ⟨invNtt_injective, invNtt_surjective⟩

/-- `invNtt` is the left inverse of `ntt`. -/
theorem invNtt_leftInverse :
    Function.LeftInverse invNtt (ntt : (Fin n → Zq) → Fin n → Zq) :=
  invNtt_ntt

/-- `invNtt` is the right inverse of `ntt`. -/
theorem invNtt_rightInverse :
    Function.RightInverse invNtt (ntt : (Fin n → Zq) → Fin n → Zq) :=
  ntt_invNtt

/-! ## Multiplicative homomorphism: derived forms -/

/-- Compute `f * g` in `R_q` via the NTT pipeline. -/
theorem polyMulCoeffs_eq (f g : Fin n → Zq) :
    polyMulCoeffs f g = invNtt (multiplyNTTs (ntt f) (ntt g)) := by
  have h := ntt_polyMul f g
  have := congrArg invNtt h
  rwa [invNtt_ntt] at this

/-- Alias: `ntt(f * g) = multiplyNTTs(ntt f)(ntt g)`. -/
theorem ntt_mul_eq_multiplyNTTs (f g : Fin n → Zq) :
    ntt (polyMulCoeffs f g) = multiplyNTTs (ntt f) (ntt g) :=
  ntt_polyMul f g

/-! ## NTT pipeline end-to-end correctness -/

/-- The NTT-based multiplication pipeline computes `polyMulCoeffs`. -/
theorem ntt_pipeline_eq_polyMul (f g : Fin n → Zq) :
    invNtt (multiplyNTTs (ntt f) (ntt g)) = polyMulCoeffs f g :=
  (polyMulCoeffs_eq f g).symm

end Fips203

end
