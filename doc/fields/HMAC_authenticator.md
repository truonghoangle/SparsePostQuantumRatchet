# Verification Plan — Authenticator Pipeline over a Structural HMAC / SHA-2 Foundation

## 0. Objective

This document is a single, self-contained, executable plan for fully
verifying the authenticator subsystem of this repository, **from the
mathematical standards up to the extracted Rust code**, in one unbroken
refinement chain:

```
FIPS 180-2 (SHA-1/SHA-256/SHA-384/SHA-512 mathematics)
        │
RFC 2104 / FIPS 198-1 (structural HMAC: H((K⊕opad) ∥ H((K⊕ipad) ∥ m)))
        │
spec.hmac_bytes — the single executable HMAC specification
        │
libcrux_hmac.hmac external model (SrcTranslated/FunsExternal.lean)
        │
extracted authenticator functions (SrcTranslated/Funs.lean):
new · update · mac_ct · mac_hdr · verify_ct · verify_hdr · into_pb · from_pb
        │
end-to-end theorems: the Rust MAC values *are* the RFC 2104 / FIPS 180-2
composition; verification decisions are exactly tag equality
```

The plan covers every function and constant listed in
[`doc/truong/authenticator_functions.txt`](../truong/authenticator_functions.txt)
(`src/authenticator.rs`, `src/authenticator/serialize.rs`) and the entire
hash/HMAC mathematics needed underneath them. It is organised as one ordered
sequence of phases (§5), each split into independently landable steps with
concrete files, deliverables, and a Definition of Done.

**Design principle — no opaque HMAC.** The HMAC specification
`spec.hmac_bytes` is *defined* from the structural model from the start
(Phase 3), built on the executable SHA functions of Phase 1. There is no
intermediate "uninterpreted core" stage to refine away later: a single
definition serves every downstream spec, and structural theorems
(truncation, lengths, two-call decomposition) are available to all consumers
immediately. Only HKDF keeps an opaque core (its RFC 5869 instantiation is
an optional follow-up, §7).

**Spec philosophy.**

* Each spec theorem characterises the **value** computed, not merely
  totality and lengths.
* Every definition is total and executable where possible (`def`, never
  `axiom`); partiality (message-length bounds, concat overflow bounds) is
  expressed via explicit hypotheses.
* Everything that touches HMAC is stated for an **arbitrary**
  `alg : libcrux_hmac.Algorithm`; the concrete `Sha256` appears only at the
  final call-site specs as an instantiation.
* Cryptographic assumptions (collision resistance, keyed-block injectivity,
  HKDF injectivity) are named `Prop`-valued **premises** of conditional
  theorems — never axioms. **The global axiom count must strictly
  decrease** (the concat and `black_box` axioms are eliminated; zero are
  added).
* Fidelity of the mathematics to the foreign Rust hash binaries (which
  Aeneas does not extract) is witnessed by the official **FIPS / RFC test
  vectors**, checked by `native_decide` (Steps 1.7, 2.7).

---

## 1. Inputs and Ground Rules

### 1.1 Source material

| Input | Role |
|-------|------|
| [`doc/field/fips180-2withchangenotice.pdf`](../field/fips180-2withchangenotice.pdf) | normative definition of SHA-1, SHA-256, SHA-384, SHA-512 |
| RFC 2104, FIPS 198-1 | normative definition of HMAC and tag truncation |
| RFC 2202, RFC 4231, FIPS 180-2 appendices | official test vectors |
| `libcrux-hmac-0.0.6/src/hmac.rs` | the Rust dispatcher (`hmac_sha1`, `hmac_sha2_256`, `hmac_sha2_384`, `hmac_sha2_512`) the model must match |
| `src/authenticator.rs`, `src/authenticator/serialize.rs`, `src/util.rs`, `src/kdf.rs` | the Rust sources of the authenticator pipeline |
| `SrcTranslated/Funs.lean`, `SrcTranslated/Types.lean` | the Aeneas extraction the specs are stated against |
| `SrcTranslated/FunsExternal.lean` | the external-model layer this plan (re)defines |

### 1.2 Extracted shapes the specs must match (read off `SrcTranslated/Funs.lean` before starting; line numbers indicative)

- `update` (~line 4904): `Slice.concat [root_key, k]` → ikm;
  `Slice.concat [45-byte label, ep.to_be_bytes]` → info;
  `hkdf_to_vec zeros32 ikm info 64`; result keys are
  `kdf_out[..32].to_vec` / `kdf_out[32..].to_vec`.
- `new` (~line 4946): `v ← from_elem 0u8 32`; calls
  `update { root_key := v, mac_key := v } ep root_key` — `new` is
  definitionally `update` at the all-zero seed for *both* fields.
- `mac_ct` / `mac_hdr` (~lines 5013/5054): `Slice.concat
  [label (35/33 bytes), ep.to_be_bytes, payload]`; then
  `hmac Sha256 mac_key data (some MACSIZE)`.
- `verify_ct` / `verify_hdr` (~lines 5039/5080): `compare expected_mac tag`;
  result `≠ 0 ⇒ Err InvalidCtMac/InvalidHdrMac`, else `Ok ()`.
- `util.compare` (~line 5004): loop over `0..lhs.len()`, XOR-OR
  accumulation over **both** slices — it indexes `rhs` at `lhs`'s indices,
  so it panics when `rhs.len < lhs.len`; then `util.is_non_zero`
  (returns `0#u8` or `1#u8` via `core.hint.black_box`).
- `into_pb` / `from_pb`: field-wise clones between `Authenticator` and its
  protobuf struct.

These shapes fix the byte-level definitions of Phase 4 (labels, input
assembly) and the preconditions of Phases 6–7 (concat overflow bounds,
equal-length compare).

### 1.3 External obstacles this plan removes

| Obstacle (in `SrcTranslated/FunsExternal.lean`) | Why it blocks | Removed by |
|---|---|---|
| `libcrux_hmac.hmac` has no faithful model | every MAC spec | Step 3.2 (structural model) |
| `kdf.hkdf_to_slice` has no faithful model | `update`/`new` specs | Step 3.3 (opaque-core wrapper model) |
| `core.hint.black_box` is an **axiom** | `verify_*` via `compare → is_non_zero → black_box` | Step 3.4 (identity model) |
| `alloc.slice.Slice.concat` / `Slice.Insts.AllocSliceConcatTVec.concat` are **axioms** | `update`, `mac_ct`, `mac_hdr` (input assembly) | Step 3.5 (guarded flatten model) |
| `Shared0T.Insts.CoreBorrowBorrow.borrow` axiom | the `Concat` instance at call sites | Step 3.5 (identity, if the WP proofs need it) |
| no specs for `Vec.index` at `RangeTo`/`RangeFrom`, `Slice.to_vec` | key splitting in `update` | Step 3.5 |
| no `U64.to_be_bytes` length/injectivity lemmas | epoch-binding injectivity (Phase 4) | Step 3.6 |

### 1.4 Global conventions (apply to every step)

- **Build**: every step ends with a green `lake build` (new errors are
  unacceptable; pre-existing unrelated warnings are tolerated).
- **Lint**: `./scripts/check-lint.sh` clean before a step is done.
- **Registration**: every new file added to `Spqr.lean` in alphabetical
  import order.
- **No `sorry`, no new axioms** in any landed step. Verify with
  `grep -rn sorry Spqr/Math Spqr/Specs SrcTranslated/FunsExternal.lean` and
  `scripts/Audit.lean` where applicable.
- **Attributes**: external-model spec theorems get `@[simp, step_simps]`;
  function specs get `@[step]` (house style).
- **File style**: per `doc/STYLE_GUIDE.md` — copyright header, module
  docstring quoting the Rust source and/or FIPS/RFC section numbers,
  `natural language description` / `natural language specs` blocks,
  `**Source**` line.
- **Regression discipline**: any step that touches a shared model or an
  existing spec must first `grep -rn <name> Spqr/ SrcTranslated/` for all
  consumers and fix them within the same step. In particular
  `kdf.hkdf_to_slice` is called by chain functions and v1 send paths, and
  `libcrux_hmac.hmac` by every MAC call site — a full build after Steps
  3.2/3.3 is mandatory.
- **No Rust-side changes**: `aeneas-config.yml`, the sources, and
  `src-modifications.diff` are untouched; all work is in the Lean
  model/spec layer.

---

## 2. Mathematical Background

### 2.1 SHA-1 / SHA-2 (FIPS 180-2)

All four algorithms share one skeleton, differing only in parameters:

| Parameter | SHA-1 | SHA-256 | SHA-384 | SHA-512 |
|---|---|---|---|---|
| word type `w` | 32-bit | 32-bit | 64-bit | 64-bit |
| block size (bytes) `B` | 64 | 64 | 128 | 128 |
| length-field width (bytes) `L` | 8 | 8 | 16 | 16 |
| schedule length | 80 | 64 | 80 | 80 |
| state words | 5 | 8 | 8 | 8 |
| digest (bytes) | 20 | 32 | **48** (truncated from 64) | 64 |
| max message length (bits) | < 2⁶⁴ | < 2⁶⁴ | < 2¹²⁸ | < 2¹²⁸ |

Pipeline for a message `m : List U8`:

```
m ──pad──► padded bytes (length ≡ 0 mod B)
  ──parse──► blocks : List (List w), 16 words each
  ──foldl compress H⁽⁰⁾──► final state H⁽ᴺ⁾
  ──serialize big-endian (+ take 48 for SHA-384)──► digest : List U8
```

Ingredients, with FIPS 180-2 references:

* **Words** (§2–3): `Std.U32` / `Std.U64` (Aeneas scalars already provide
  `2^n`-modular `+`, `&&&`, `|||`, `^^^`, `~~~`, shifts); `rotl`/`rotr`
  defined on top of shifts.
* **Logical functions** (§4.1): SHA-1 `f_t` (`Ch`/`Parity`/`Maj` by round
  range); SHA-2 `Ch`, `Maj`, `Σ₀`, `Σ₁`, `σ₀`, `σ₁`, separately for the
  `{256}` (32-bit) and `{512}` (64-bit) families; SHA-384 reuses the 512
  functions.
* **Constants** (§4.2): SHA-1 `K_t` (4 values by round range); `K^{256}`
  (64 words); `K^{512}` (80 words) — literal lists transcribed from the
  standard, length-checked by `decide`, value-checked by the test vectors.
* **Initial hash values** (§5.3): per-variant `H⁽⁰⁾`; SHA-384's distinct IV
  (§5.3.3) is what separates it from plainly truncated SHA-512.
* **Padding** (§5.1): `m ++ [0x80] ++ 0^k ++ (8·|m| big-endian in L bytes)`
  with `k` minimal so the total length is a multiple of `B`
  (Merkle–Damgård strengthening).
* **Parsing** (§5.2): split into `B`-byte blocks; each block into 16
  big-endian words.
* **Schedule + compression** (§6): the `W_t` recurrences and one round
  function per family; `compress state block =
  state +ʷ foldl round state (schedule block)` (wordwise modular `+`).
* **Digest**: big-endian serialization of the final state; SHA-384 takes
  the first 48 bytes.

### 2.2 HMAC (RFC 2104 §2, FIPS 198-1 §4–5)

For a hash `H` with block size `B` and output length `hLen`:

```
K₀   = if |K| ≤ B then K ++ 0^(B−|K|) else H(K) ++ 0^(B−hLen)
ipad = 0x36 ×B        opad = 0x5c ×B
HMAC(K, m) = H( (K₀ ⊕ opad) ∥ H( (K₀ ⊕ ipad) ∥ m ) )
tag        = leftmost t bytes of HMAC(K, m)          (FIPS 198-1 §5)
```

The model is parameterized by the hash, in two layers:

* a **generic layer** over an abstract `H : List U8 → List U8` with
  hypothesis `H_len : ∀ m, (H m).length = hLen` — home of all structural
  lemmas;
* four **concrete instances** at the Phase-1 hashes, matching the Rust
  dispatcher one-to-one.

Per-algorithm sizes (companions; `block_len ≠ hash_len`):

| | SHA-1 | SHA-256 | SHA-384 | SHA-512 |
|---|---|---|---|---|
| `hash_len` | 20 | 32 | 48 | 64 |
| `block_len` | 64 | 64 | 128 | 128 |

### 2.3 The authenticator protocol (read off the Rust sources)

* **Key schedule**: `update(rk_old, k, ep)` computes
  `okm = HKDF(salt = 0³², ikm = rk_old ∥ k, info = LABEL_UPD ∥ ep_be, 64)`
  and splits it: `root_key' = okm[..32]`, `mac_key' = okm[32..]`.
  `new(root_key, ep) = update(⟨0³², 0³²⟩, root_key, ep)`.
* **MACs**: `mac_ct(ep, ct) = HMAC-SHA-256(mac_key,
  LABEL_CT ∥ ep_be ∥ ct)[..32]`; `mac_hdr` analogous with `LABEL_HDR`.
  The labels (45/35/33 bytes) provide domain separation.
* **Verification**: constant-time XOR-OR comparison of the expected tag
  against the recomputed MAC; `Ok ()` iff equal, else the respective error.
* **Serialization**: `into_pb`/`from_pb` are field-wise clones; round-trips
  are identities.

---

## 3. Architecture and File Layout

Target tree (all files are deliverables of this plan):

```
Spqr/Math/Hash/                          ── Phase 1 (FIPS 180-2)
├── Word.lean              rotations, modular word arithmetic        (1.1)
├── Pad.lean               MD-strengthening padding, pad_inj         (1.2)
├── Parse.lean             B-byte blocks, big-endian codecs          (1.3)
├── Sha1/Constants.lean    K_t, H⁽⁰⁾                                  (1.4)
├── Sha2/Constants.lean    K^{256}, K^{512}, IVs incl. SHA-384       (1.4)
├── Sha1/Round.lean        f_t, schedule, compress                   (1.5)
├── Sha2/Round.lean        Ch/Maj/Σ/σ ×2 families, schedule, compress(1.5)
├── Params.lean            HashParams structure + 4 instances        (1.6)
├── Core.lean              hashCore, digest, sha1…sha512, theorems   (1.6)
└── TestVectors.lean       FIPS 180-2 appendix vectors               (1.7)

Spqr/Math/Hmac/                          ── Phase 2 (RFC 2104 / FIPS 198-1)
├── Xor.lean               xorBytes, ipad/opad bytes                 (2.2)
├── Key.lean               normKey (K₀)                              (2.3)
├── Core.lean              hmacCore, hmacTrunc, structure lemmas     (2.4)
├── Alg.lean               hmacAlg over the four SHA instances       (2.5)
├── Security.lean          HashCR, HashKeyBinding, injectivity       (2.6)
└── TestVectors.lean       RFC 2202 / RFC 4231 vectors               (2.7)

Spqr/Aux/LibcruxHmac/                    ── Phase 3 (algorithm tables + spec API)
├── HashLen.lean           Algorithm.hash_len                        (3.1)
├── BlockLen.lean          Algorithm.block_len                       (3.1)
└── HmacBytes.lean         spec.hmac_bytes := structural HMAC        (3.2)

SrcTranslated/FunsExternal.lean          ── Phase 3 (external models)
                           libcrux_hmac.hmac model + specs           (3.2)
                           spec.hkdf_bytes + kdf.hkdf_to_slice model (3.3)
                           core.hint.black_box identity model        (3.4)

Spqr/Specs/Aeneas/                       ── Phase 3 (plumbing specs)
├── SliceConcat.lean       guarded flatten model + spec              (3.5)
├── VecIndexRange.lean     index at RangeTo/RangeFrom                (3.5)
├── SliceToVec.lean        to_vec value spec                         (3.5)
└── U64ToBeBytes.lean      length-8 + injectivity                    (3.6)

Spqr/Specs/Kdf/HkdfToVec.lean            functional hkdf_to_vec spec (3.3)

Spqr/Specs/Authenticator/                ── Phases 4–9
├── Defs.lean              labels, input assembly, key-schedule and
│                          MAC models, derived_from, WF, premises    (4.1)
├── MACSIZE.lean           constant + linking lemmas                 (6.3)
├── Update.lean            functional update_spec                    (6.1)
├── New.lean               new_spec via update_spec                  (6.2)
├── MacCt.lean             mac_ct_spec (+ end-to-end corollary)      (7.1)
├── MacHdr.lean            mac_hdr_spec (+ end-to-end corollary)     (7.2)
├── VerifyCt.lean          verify_ct decision spec                   (7.3)
├── VerifyHdr.lean         verify_hdr decision spec                  (7.4)
├── EndToEnd.lean          IT-theorems + hash-premise corollaries    (7.5)
├── Error/Fmt.lean         Display/Debug message equations           (9.1)
└── Serialize/
    ├── IntoPb.lean        pure equation + preservation              (8.1)
    ├── FromPb.lean        pure equation + preservation              (8.1)
    └── RoundTrip.lean     round-trip identities                     (8.2)

Spqr/Specs/Util/Compare.lean             constant-time compare       (5.1)
```

Where a listed file already exists in the repository, the step **replaces or
extends** its content to meet the deliverable as specified here; the plan
does not depend on what any prior version contained.

---

## 4. Definition and Theorem Inventory

### 4.1 SHA layer (namespace `spec.sha`; Phase 1)

Definitions:

| # | Definition | Statement / Value | File |
|---|------------|-------------------|------|
| S1 | `rotl`, `rotr`, `shr` | `rotl n x = (x <<< n) ||| (x >>> (width − n))` etc., `U32`/`U64` | `Word.lean` |
| S2 | `wadd` | wordwise modular addition (wrapping `+`; value lemma `(wadd x y).val = (x.val + y.val) % 2^width`) | `Word.lean` |
| S3 | `HashParams` | structure: word ops, `blockSize`, `lenFieldSize`, `scheduleLen`, `stateLen`, `digestSize`, schedule/round functions, `K`, `H0`; instances `sha1Params`, `sha256Params`, `sha384Params`, `sha512Params` | `Params.lean` |
| S4 | `pad (B L) (m)` | `m ++ [0x80] ++ replicate k 0 ++ lenBytes L (8·m.length)`, `k = (B − (m.length + 1 + L) % B) % B` | `Pad.lean` |
| S5 | `lenBytes (L n : Nat)` | `n` big-endian in `L` bytes (used under `n < 2^(8L)`) | `Pad.lean` |
| S6 | `toBlocks (B) (bs)` | `bs.chunksExact B : List (List U8)` | `Parse.lean` |
| S7 | `wordsBE` / `bytesBE` | big-endian codecs `List U8 ↔ List w` (4-/8-byte groups) | `Parse.lean` |
| S8 | `Ch`, `Maj`, `Parity` | `(x &&& y) ^^^ (~~~x &&& z)`, … per family | `Sha*/Round.lean` |
| S9 | `bsig0/bsig1/ssig0/ssig1` | Σ/σ rotation-shift combinations, `{256}` and `{512}` variants | `Sha2/Round.lean` |
| S10 | `schedule` | `W_t` recurrences as a `List w` fold (SHA-1 includes `rotl 1`) | `Sha*/Round.lean` |
| S11 | `compress` | one-block transition: rounds fold + wordwise `wadd` of the input state | `Sha*/Round.lean` |
| S12 | `hashCore (P)` | `(toBlocks P.B (pad P.B P.L m)).foldl P.compress P.H0` | `Core.lean` |
| S13 | `digest (P)` | `(bytesBE (hashCore P m)).take P.digestSize` | `Core.lean` |
| S14 | `sha1, sha256, sha384, sha512` | `digest` at the four instances | `Core.lean` |

Lemmas:

| # | Lemma | Statement |
|---|-------|-----------|
| SL1 | `rotl_rotr_inverse`, `rotl_mod_width` | rotation algebra for normalizing round expressions |
| SL2 | `wadd_assoc`, `wadd_comm`, `wadd_val` | modular-addition algebra |
| SL3 | `lenBytes_length` | `(lenBytes L n).length = L` |
| SL4 | `lenBytes_inj` | injective for `n < 2^(8L)` |
| SL5 | `pad_length_mod` | `(pad B L m).length % B = 0` (for `1 + L ≤ B`) |
| SL6 | `pad_prefix` | `(pad B L m).take m.length = m` |
| SL7 | `pad_length_le` | `(pad B L m).length ≤ m.length + L + B` |
| SL8 | `toBlocks_length` / `toBlocks_flatten` | each block has length `B`; flatten is the identity when `B ∣ bs.length` |
| SL9 | `wordsBE_bytesBE` / `bytesBE_wordsBE` | codec round-trips |
| SL10 | `wordsBE_length`, `bytesBE_length` | codec length equations |
| SL11 | `K256_length = 64`, `K512_length = 80`, `H0_*_length` | constant-table sanity (`decide`) |
| SL12 | `schedule_length`, `compress_state_length` | schedule has `scheduleLen` entries; `compress` preserves `stateLen` |

Theorems:

| # | Theorem | Statement |
|---|---------|-----------|
| ST1 | `digest_length` | `(digest P m).length = P.digestSize`; corollaries `sha1_length = 20` … `sha512_length = 64` |
| ST2 | `digest_deterministic` | explicit determinism (pure function), citable downstream |
| ST3 | `hashCore_append_block` | `hashCore (bs ++ [b]) = compress (hashCore bs) b` — the Merkle–Damgård step |
| ST4 | `digest_eq_foldl` | unfolding equation exposing pad/parse/fold/serialize (normal form for Phase-2 proofs) |
| ST5 | `pad_inj` | `pad B L` is injective (SL4 + SL6 + length analysis) — MD-strengthening suffix-freeness |
| ST6 | `sha384_eq_trunc_sha512_iv` | SHA-384 = `take 48` of the 64-bit core **at the SHA-384 IV** |
| STV1 | FIPS test vectors | `native_decide` checks of the appendix vectors (`"abc"`, `""`, the 448-bit message; million-`a` only if compile time permits) for all four variants |

### 4.2 HMAC layer (namespace `spec.hmac`; Phase 2)

Definitions:

| # | Definition | Statement / Value |
|---|------------|-------------------|
| M1 | `xorBytes` | `zipWith (^^^) : List U8 → List U8 → List U8` |
| M2 | `ipadBytes B = replicate B 0x36`, `opadBytes B = replicate B 0x5c` | RFC 2104 constants |
| M3 | `normKey H B hLen K` | key normalization `K₀` (hash-if-long, zero-pad to `B`) |
| M4 | `hmacCore H B K m` | `H ((normKey … K ⊕ opadBytes B) ++ H ((normKey … K ⊕ ipadBytes B) ++ m))` |
| M5 | `hmacTrunc H B K m t` | `(hmacCore H B K m).take t` |
| M6 | `hmacAlg : Algorithm → List U8 → List U8 → List U8` | `hmacCore` at the Phase-1 hash for each algorithm, with `B = alg.block_len` |
| M7 | `HashCR H : Prop`, `HashKeyBinding H : Prop` | hash-level crypto premises: collision resistance on the relevant domain; injectivity of the keyed first block |

Lemmas:

| # | Lemma | Statement |
|---|-------|-----------|
| ML1 | `xorBytes_length` | `min` of lengths; equal-length corollary |
| ML2 | `xorBytes_self_inverse` | XOR involution at equal lengths |
| ML3 | `xorBytes_inj_left` | `xorBytes · p` injective on fixed-length inputs |
| ML4 | `ipad_ne_opad` | `0x36 ≠ 0x5c` ⇒ inner/outer key blocks differ (domain separation inside HMAC) |
| ML5 | `normKey_length` | `= B` (needs `hLen ≤ B`, true at all four instances) |
| ML6 | `normKey_short_eq` | for `|K| ≤ B`: `normKey … K = K ++ replicate (B−|K|) 0` (the authenticator's 32-byte keys take this branch) |
| ML7 | `normKey_inj_on_short` | injective on `{K // K.length = n}` for fixed `n ≤ B` |
| ML8 | `hmacCore_structure` | unfolding equation exposing the two nested hash calls |

Theorems:

| # | Theorem | Statement |
|---|---------|-----------|
| MT1 | `hmacCore_length` | `= hLen` (from `H_len`) |
| MT2 | `hmacTrunc_length` | `= min t hLen`; `= t` for `t ≤ hLen` |
| MT3 | `hmacCore_deterministic` | explicit determinism |
| MT4 | `hmacAlg_length` | `∀ alg K m, (hmacAlg alg K m).length = alg.hash_len` (by `cases alg` + MT1 + ST1) |
| MT5 | `hmacCore_eq_of_normKey_eq` | HMAC depends on `K` only through `K₀` |
| MT6 | `hmacCore_inj_of_hash` | **conditional**: `HashCR H → HashKeyBinding H →` equal tags from fixed-length keys imply equal key and message (via ML3/ML7/ML8) |
| MTV1 | RFC test vectors | `native_decide` checks of RFC 2202 / RFC 4231 vectors at all four instances |

### 4.3 Spec-API layer (Phase 3)

| # | Item | Statement / Value | Key lemmas |
|---|------|-------------------|------------|
| A1 | `Algorithm.hash_len` | `Sha1 ↦ 20, Sha256 ↦ 32, Sha384 ↦ 48, Sha512 ↦ 64` | per-constructor `@[simp]` (`rfl`), `hash_len_pos`, `hash_len_le : ≤ 64` |
| A2 | `Algorithm.block_len` | `Sha1/Sha256 ↦ 64, Sha384/Sha512 ↦ 128` | per-constructor `@[simp]`, `block_len_pos`, `hash_len_le_block_len` |
| A3 | `spec.hmac_bytes alg key data n` | **`:= (hmacAlg alg key data).takeD n 0#u8`** — defined structurally, no opaque | `hmac_bytes_length : … = n`; `hmac_bytes_eq_core` (for `n ≤ hash_len`, `= (hmacAlg …).take n`); `hmac_bytes_full` (at `n = hash_len`, `= hmacAlg …`) |
| A4 | `spec.hmac_tag_len alg tl`, `spec.hmac_vec` | tag-length resolution (`some l ↦ l`, `none ↦ hash_len`) and the `Vec`-typed wrapper | `hmac_vec_length`, `hmac_vec_val_core` |
| A5 | `spec.hkdf_bytes salt ikm info L` | `(hkdf_bytes_raw …).takeD L 0#u8` with `opaque hkdf_bytes_raw` (+ `Inhabited ⟨[]⟩`) | `hkdf_bytes_length` (provable, no axiom) |
| A6 | `libcrux_hmac.hmac` model | `fun alg key payload tl => ok ⟨spec.hmac_bytes alg key.val payload.val (hmac_tag_len alg tl), …⟩` | `hmac_some_spec`, `hmac_none_spec`, `hmac_cases_spec` |
| A7 | `kdf.hkdf_to_slice` model | `ok ⟨spec.hkdf_bytes salt.val ikm.val info.val okm.length, …⟩` | `hkdf_to_slice_spec` |
| A8 | `core.hint.black_box` model | `fun x => ok x` (it is an optimisation barrier, not a semantic operation) | `black_box_spec : ⦃ r => r = x ⦄` |
| A9 | concat / index / to_vec / U64 models & specs | see Steps 3.5–3.6 | `concat_spec`, `index_range_to/from_spec`, `to_vec_spec`, `to_be_bytes_length/inj` |

External-model spec theorems (all algorithm-generic):

| Lemma | Statement |
|-------|-----------|
| `hmac_some_spec` | `hmac alg key payload (some l) ⦃ v => v.val = spec.hmac_bytes alg key.val payload.val l.val ∧ v.length = l.val ⦄` |
| `hmac_none_spec` | `hmac alg key payload none ⦃ v => v.val = spec.hmac_bytes … alg.hash_len ∧ v.length = alg.hash_len ⦄` |
| `hmac_cases_spec` | four-way length corollary `20 ∣ 32 ∣ 48 ∣ 64` by `cases alg <;> simp` |
| `hkdf_to_slice_spec` | `⦃ s => s.val = spec.hkdf_bytes salt.val ikm.val info.val okm.length ∧ s.length = okm.length ⦄` |
| `hkdf_to_vec_spec` | `⦃ v => v.val = spec.hkdf_bytes … okm_len.val ∧ v.length = okm_len.val ⦄` |

### 4.4 Protocol layer (Phase 4; namespace of `Spqr/Specs/Authenticator/Defs.lean`)

| # | Definition | Statement / Value | Key lemmas |
|---|------------|-------------------|------------|
| P1–P3 | `AUTH_UPDATE_LABEL` / `CT_MAC_LABEL` / `HDR_MAC_LABEL` | the exact 45/35/33 label bytes from the extraction (so `rfl`-level equality holds) | length lemmas; `CT_HDR_label_ne`, `CT_HDR_label_not_prefix` (`decide`) |
| P4 | `ZERO_SALT` | `List.replicate 32 0#u8` | `ZERO_SALT_length` |
| P5–P8 | `update_ikm rk k := rk ++ k`; `update_info ep := AUTH_UPDATE_LABEL ++ ep.to_be_bytes`; `mac_data_ct ep ct := CT_MAC_LABEL ++ ep.to_be_bytes ++ ct`; `mac_data_hdr` analogous | exact byte assemblies of the Rust code | lengths; `update_ikm_inj` (fixed length 32), `update_info_inj`, `mac_data_ct_inj`, `mac_data_hdr_inj` (fixed-width prefixes + A9 injectivity); **`mac_data_ct_ne_hdr`** (domain separation, from `CT_HDR_label_not_prefix`) |
| P9–P11 | `update_okm rk k ep := spec.hkdf_bytes ZERO_SALT (update_ikm rk k) (update_info ep) 64`; `update_root_key := (…).take 32`; `update_mac_key := (…).drop 32` | the key schedule | `update_okm_length`, `update_okm_split` (`take_append_drop`), key lengths = 32 |
| P12–P13 | `mac_ct_model alg mk ep ct := spec.hmac_bytes alg mk (mac_data_ct ep ct) 32`; `mac_hdr_model` analogous | **algorithm-generic** MAC models | `mac_*_model_length` (∀ alg, = 32); **`mac_ct_model_eq_core`**: at `.Sha256`, `= (hmacCore sha256 64 mk (mac_data_ct ep ct)).take 32`, and since `32 = hash_len Sha256` the `take` is the identity — the model *is* the RFC 2104 composition (from A3 + MT1) |
| P14 | `compare_model` | XOR-OR fold over common indices | used by Phase 5 |
| P15 | `HmacInjOn32 : Prop` | equal 32-byte tags from 32-byte keys ⇒ equal key and data | premise of `mac_*_model_inj`, `mac_ct_ne_mac_hdr`, `verify_*_binds`; **discharged** to `HashCR sha256 ∧ HashKeyBinding sha256` by the bridge theorem (Step 7.5) |
| P16 | `HkdfInj : Prop` | equal outputs (fixed salt, L) ⇒ equal ikm and info | premise of `update_binds_inputs` |
| P17 | `derived_from rk mk rk_old k ep : Prop` | `rk.val = update_root_key rk_old k ep ∧ mk.val = update_mac_key rk_old k ep` | `derived_from_lengths`, `derived_from_of_eq` |
| P18 | `auth_reachable rk mk : Prop` | inductive: some `(rk_old, k, ep)` derivation step reaches `(rk, mk)` | `auth_reachable_lengths` |
| P19 | `Authenticator.WF` | both keys have length 32 | `WF_of_derived_from`, `WF_of_reachable` |

### 4.5 End-to-end theorems (Phase 7)

| # | Theorem | Statement |
|---|---------|-----------|
| E1 | `mac_ct_end_to_end` | under the concat bound: `mac_ct self ep ct ⦃ res => res.val = hmacCore spec.sha.sha256 64 self.mac_key.val (CT_MAC_LABEL ++ ep.to_be_bytes ++ ct.val) ⦄` — the extracted Rust value equals the RFC 2104 / FIPS 180-2 composition |
| E2 | `mac_hdr_end_to_end` | analogous |
| E3 | `verify_ct_end_to_end` | `Ok () ↔ expected_mac.val = (the E1 value)` |
| E4 | `verify_hdr_end_to_end` | analogous |
| E5 | `update_end_to_end` | `derived_from` with `hkdf_bytes` (still opaque-cored; deepens automatically once the RFC 5869 follow-up of §7 lands) |
| E6 | `mac_ct_model_inj_of_hash`, `verify_ct_binds_of_hash` | the conditional security theorems with premises `HashCR sha256`, `HashKeyBinding sha256` (replacing the monolithic `HmacInjOn32` via the bridge theorem `HmacInjOn32_of_hash`) |

### 4.6 Security properties → formal counterparts

| Property | Unconditional theorem | Conditional theorem (premise) |
|----------|----------------------|-------------------------------|
| Key separation | `derived_keys_pairwise`, `mac_ct_depends_only_on_mac_key`, `update_mac_key_independent_of_old_mac_key` | — |
| Forward secrecy | `derived_from` postcondition of `update_spec` | — |
| Input binding | `update_ikm_inj`, `update_info_inj` | `update_binds_inputs` (`HkdfInj`) |
| MAC unforgeability shadow | — | `mac_ct_model_inj`, `verify_ct_binds` (`HmacInjOn32`); via E6 also from `HashCR`/`HashKeyBinding` only |
| Domain separation ct/hdr | `mac_data_ct_ne_hdr` (inputs) | `mac_ct_ne_mac_hdr` (outputs, `HmacInjOn32`) |
| Structural MAC characterisation | E1–E4 (equality with the RFC 2104 composition) | — |

That the premises hold for real SHA-256 is a computational assumption; the
development records exactly which results depend on it, and reduces the
HMAC-level premise to hash-level ones — after Phase 7 the only crypto
assumptions left below the MAC layer concern the hash function itself.

---

## 5. Execution Steps

Steps within a phase marked ∥ may land in parallel / any order.
**Phases 1–2 (mathematics) and the plumbing half of Phase 3 (Steps 3.4–3.6)
are mutually independent and may proceed in parallel**; Step 3.2 needs
Phases 1–2; Phases 4–9 are sequential along the DAG in §6.

### Phase 0 — Baseline

- [ ] **Step 0.1 — Record the baseline.**
  `lake build`; `grep -rn sorry Spqr/`; list current axioms/opaques
  (`grep -n "^axiom\|^noncomputable axiom" SrcTranslated/FunsExternal.lean`,
  `grep -rn "^opaque" Spqr/`). Note all of it in the PR description of the
  first landed step. *DoD*: baseline recorded; success criteria of
  Step 10.1 are measured against it.

### Phase 1 — SHA-1/SHA-2 mathematics (`Spqr/Math/Hash/`)

- [ ] **Step 1.1 — `Word.lean`** (S1–S2; SL1–SL2). Audit Aeneas/Mathlib
  for existing rotation lemmas first; re-export rather than re-prove.
- [ ] **Step 1.2 — `Pad.lean`** (S4–S5; SL3–SL7; ST5). Pure
  `List U8`/`Nat` reasoning (reuse `Spqr/Math/List.lean`); the only
  nontrivial proof is `pad_inj`.
- [ ] **Step 1.3 — `Parse.lean`** (S6–S7; SL8–SL10). Reuse the
  `chunksExact` idiom of `Spqr/Specs/Aeneas/SliceChunksExact.lean` and the
  `U16` byte-codec lemmas (`Spqr/Specs/Aeneas/U16FromBeBytes.lean`) as
  templates.
- [ ] **Step 1.4 — Constants** (`Sha1/Constants.lean`,
  `Sha2/Constants.lean`; SL11). Transcribe `K`-tables and IVs from FIPS
  180-2 §4.2/§5.3; length checks by `decide`; value correctness is gated by
  Step 1.7's vectors.
- [ ] **Step 1.5 — Round functions** (`Sha1/Round.lean`,
  `Sha2/Round.lean`; S8–S11, SL12). Keep `schedule`/`compress` as
  `List`-based folds, opaque to `simp`, exposing only equational lemmas.
- [ ] **Step 1.6 — `Params.lean` + `Core.lean`** (S3, S12–S14; ST1–ST4,
  ST6).
- [ ] **Step 1.7 — `TestVectors.lean`** (STV1; `native_decide`; the
  million-`a` vector stays commented out if compile time is prohibitive).

Internal dependency order: 1.1 → {1.2, 1.3, 1.5} (1.5 also needs 1.4) →
1.6 → 1.7.

### Phase 2 — Structural HMAC mathematics (`Spqr/Math/Hmac/`)

- [ ] **Step 2.1 — Generic-layer scaffolding decision.** Fix the
  parameterization `(H : List U8 → List U8) (B hLen : Nat)
  (H_len : ∀ m, (H m).length = hLen) (hB : hLen ≤ B)` used by Steps
  2.3–2.6 (structure vs. section variables; pick whichever keeps `simp`
  normal forms smallest and document the choice in `Core.lean`'s
  docstring).
- [ ] **Step 2.2 — `Xor.lean`** (M1–M2; ML1–ML4). No Phase-1 dependency.
- [ ] **Step 2.3 — `Key.lean`** (M3; ML5–ML7).
- [ ] **Step 2.4 — `Core.lean`** (M4–M5; ML8; MT1–MT3, MT5).
- [ ] **Step 2.5 — `Alg.lean`** (M6; MT4) — instantiation at the four
  Phase-1 hashes with the §2.2 block sizes; the definition Step 3.2 plugs
  into `spec.hmac_bytes`.
- [ ] **Step 2.6 — `Security.lean`** (M7; MT6). State `HashCR`/
  `HashKeyBinding` against the generic layer; MT6's proof uses ML3/ML7 and
  the two-call decomposition ML8.
- [ ] **Step 2.7 — `TestVectors.lean`** (MTV1).

### Phase 3 — External models and spec API

- [ ] **Step 3.1 — Algorithm tables** (`Spqr/Aux/LibcruxHmac/HashLen.lean`,
  `BlockLen.lean`; A1–A2). Per-constructor `@[simp]` lemmas (`rfl`),
  `hash_len_pos`, `hash_len_le`, `block_len_pos`,
  `hash_len_le_block_len` (all by `cases alg`). No other dependency; may
  land first in the whole plan.

- [ ] **Step 3.2 — `spec.hmac_bytes` + the `libcrux_hmac.hmac` model**
  (A3–A4, A6). In `Spqr/Aux/LibcruxHmac/HmacBytes.lean`:

  ```lean
  def spec.hmac_bytes (alg : libcrux_hmac.Algorithm)
      (key data : List Std.U8) (n : Nat) : List Std.U8 :=
    (spec.hmac.hmacAlg alg key data).takeD n 0#u8
  ```

  plus `hmac_tag_len`, `hmac_vec`, and the theorems `hmac_bytes_length`
  (by `takeD` length), `hmac_bytes_eq_core`, `hmac_bytes_full`,
  `hmac_vec_val_core` (from MT4 + A1). In
  `SrcTranslated/FunsExternal.lean`: replace the body of
  `libcrux_hmac.hmac` (signature and attributes unchanged) with

  ```lean
  fun alg key payload tag_len =>
    let n := match tag_len with | some l => l.val | none => alg.hash_len
    ok ⟨spec.hmac_bytes alg key.val payload.val n, by …⟩
    -- bound: l.property in the `some` branch; hash_len_le in `none`
  ```

  and prove `hmac_some_spec` / `hmac_none_spec` / `hmac_cases_spec`
  (`@[simp, step_simps]`). *Regression*: grep every `hmac` consumer
  (`SrcTranslated/Funs.lean` call sites in authenticator, chain, v1 paths)
  and full `lake build`. *Depends on Phases 1–2.*

- [ ] **Step 3.3 — HKDF model + `hkdf_to_vec_spec`** (A5, A7). In
  `FunsExternal.lean`: `opaque spec.hkdf_bytes_raw` (+ `Inhabited ⟨[]⟩`),
  wrapper `spec.hkdf_bytes … := (…).takeD L 0#u8`, `hkdf_bytes_length`;
  replace the body of `kdf.hkdf_to_slice` with
  `ok ⟨spec.hkdf_bytes salt.val ikm.val info.val okm.length, by …⟩` and
  prove `hkdf_to_slice_spec`. In `Spqr/Specs/Kdf/HkdfToVec.lean`: the
  functional `hkdf_to_vec_spec` (postcondition
  `v.val = spec.hkdf_bytes … okm_len.val ∧ v.length = okm_len.val`; proof:
  from_elem → deref_mut → `hkdf_to_slice_spec` → write-back). Both halves
  land as **one** green build. *Regression*: chain/v1 callers of
  `hkdf_to_slice`/`hkdf_to_vec`.

- [ ] **Step 3.4 — `core.hint.black_box` identity model** (A8). ∥
  Replace the axiom with `fun x => ok x` + `black_box_spec`
  (`@[simp, step_simps]`). *Regression*: verify `util.is_non_zero` is its
  only caller; build.

- [ ] **Step 3.5 — Slice/Vec plumbing specs** (A9). ∥
  New files under `Spqr/Specs/Aeneas/`:
  - `SliceConcat.lean`: replace both concat axioms with the guarded
    flatten model —
    `if h : ((s.val.map Slice.val).flatten).length ≤ Usize.max
     then ok ⟨…, h⟩ else fail .panic`
    (faithful: Rust aborts on capacity overflow). Spec takes the bound as
    a **precondition** and concludes
    `v.val = (s.val.map Slice.val).flatten`. Model
    `Shared0T.Insts.CoreBorrowBorrow.borrow` as identity if the WP proofs
    need it. The bounds become hypotheses of `update_spec` (`32 + k.length
    ≤ Usize.max`) and `mac_ct_spec`/`mac_hdr_spec`
    (`35/33 + 8 + payload.length ≤ Usize.max`); document this in each
    docstring.
  - `VecIndexRange.lean`: `Vec.index` at `RangeTo` (`= v.val.take n`,
    precondition `n ≤ v.length`) and `RangeFrom` (`= v.val.drop n`).
    Check whether Aeneas already ships usable lemmas; wrap instead of
    re-prove.
  - `SliceToVec.lean`: `to_vec inst s ⦃ v => v.val = s.val ⦄` (via
    `CloneU8`; reuse the clone idiom from the serialize specs).
- [ ] **Step 3.6 — `U64ToBeBytes.lean`** (A9). ∥
  Modelled on `U16ToBeBytes.lean`: `(to_be_bytes ep).length = 8` and
  `to_be_bytes_inj`. Needed by Phase 4's injectivity lemmas.

### Phase 4 — Protocol definitions layer

- [ ] **Step 4.1 — `Spqr/Specs/Authenticator/Defs.lean`** (P1–P19; may
  land in 2–3 internal commits). Contents in dependency order:
  1. labels + `ZERO_SALT` (P1–P4) with `decide`-level lemmas — byte
     literals copied from the extraction so `rfl` matches the extracted
     arrays;
  2. input assembly + injectivity + domain separation (P5–P8, using
     Step 3.6);
  3. key-schedule and MAC models (P9–P13), including
     `mac_ct_model_eq_core` / `mac_hdr_model_eq_core` — available
     immediately because `spec.hmac_bytes` is structural (Step 3.2);
  4. `derived_from`, `auth_reachable`, `WF` (P17–P19) and, if a legacy
     `jointly_derived` predicate exists in the tree, the bridge lemma
     `derived_from_jointly_derived` so its consumers keep compiling;
  5. crypto premises + conditional theorems (P15–P16):
     `mac_ct_model_inj`, `mac_hdr_model_inj`, `mac_ct_ne_mac_hdr`,
     `update_binds_inputs`, `derived_keys_pairwise` — each with the premise
     explicit.
  *DoD*: file proven end-to-end; imports only Phase-3 layers.

### Phase 5 — Constant-time comparison

- [ ] **Step 5.1 — `Spqr/Specs/Util/Compare.lean`** (P14 + L1–L3).
  - `compare_model` (XOR-OR fold);
  - `is_non_zero_spec` (`1#u8` iff input ≠ 0; uses `black_box_spec`);
  - `compare_loop_spec` (L1): invariant "accumulator = 0 ↔ all inspected
    bytes equal" via the repo's range-iterator loop idiom
    (`Spqr/Aux/Aeneas/StdNextCoreIterRangeStep.lean`);
  - `compare_spec` (L2): with precondition `lhs.length = rhs.length`
    (which also rules out the asymmetric-panic branch):
    `util.compare lhs rhs ⦃ r => r = 0#u8 ↔ lhs.val = rhs.val ⦄`; if a
    weaker `rhs.length ≥ lhs.length` suffices, state that and derive the
    equal-length corollary;
  - `compare_refl` (L3).
  *DoD*: proven; last prerequisite for Phase 7's verify specs.

### Phase 6 — Core ratchet specs

- [ ] **Step 6.1 — `Update.lean` — functional `update_spec`.**
  `update_spec (h : 32 + k.length ≤ Usize.max) : update self ep k
   ⦃ r => derived_from r.root_key r.mac_key self.root_key.val k.val ep ⦄`
  (drop the bound if it turns out dischargeable from slice properties).
  Proof: `step*` through the Step 3.3/3.5 specs. Corollaries:
  `update_lengths`, `update_preserves_WF`,
  `update_mac_key_independent_of_old_mac_key` (the extracted body never
  reads `self.mac_key`), conditional `update_binds_inputs` (`HkdfInj`),
  plus the legacy-predicate corollary if applicable (Step 4.1.4).
  *DoD*: `grep -rn sorry Spqr/Specs/Authenticator` is empty.
- [ ] **Step 6.2 — `New.lean`.**
  `new_eq_update` (definitional); `new_spec` as `update_spec` at the
  zero seed: `derived_from r.root_key r.mac_key (List.replicate 32 0#u8)
  root_key.val ep` (bound `32 + root_key.length ≤ Usize.max` inherited).
  Corollaries: `new_lengths`, `new_WF`, `new_reachable`.
- [ ] **Step 6.3 — `MACSIZE.lean`.** ∥
  `MACSIZE` value lemmas (`MACSIZE_eq`, `MACSIZE_val`, `MACSIZE_spec`,
  `MACSIZE_pos`, `MACSIZE_le_max`) and linking lemmas
  `MACSIZE_eq_hmac_output : ∀ alg key e d, (mac_ct_model alg key e d).length
  = MACSIZE.val`, `MACSIZE_eq_update_key_length`, plus the observational
  `MACSIZE_eq_hash_len_Sha256` (no theorem may *depend* on it). Imports
  `Defs.lean`.

### Phase 7 — MAC, verify, and end-to-end layer

- [ ] **Step 7.1 — `MacCt.lean`.**
  `mac_ct_spec (h : 43 + ct.length ≤ Usize.max) : mac_ct self ep ct
   ⦃ res => res.val = mac_ct_model .Sha256 self.mac_key.val ep ct.val ∧
            res.length = MACSIZE.val ⦄`
  via the generic `hmac_some_spec` at `.Sha256` + the concat spec.
  Corollaries: `mac_ct_length`, `mac_ct_deterministic`,
  `mac_ct_depends_only_on_mac_key`; conditional `mac_ct_inj`
  (`HmacInjOn32`). **End-to-end corollary E1** follows by rewriting with
  `mac_ct_model_eq_core` (place it here or in `EndToEnd.lean`, Step 7.5).
- [ ] **Step 7.2 — `MacHdr.lean`.** ∥ with 7.1
  Mirror with `mac_hdr_model`, bound `41 + hdr.length`; E2 analogous.
- [ ] **Step 7.3 — `VerifyCt.lean`.**
  Generic helper `verify_decision` (decision skeleton `Ok ↔ tag equality`
  for any `alg`, from `compare_spec` + `mac_ct_model_length`); then
  `verify_ct_spec (h₁ : expected_mac.length = 32) (h₂ : concat bound) :
   verify_ct self ep ct expected_mac
   ⦃ r => (r = .Ok () ↔ expected_mac.val = mac_ct_model .Sha256 …) ∧
          (r = .Err .InvalidCtMac ↔ expected_mac.val ≠ …) ⦄`.
  Corollaries: `verify_ct_complete` (mac-then-verify yields `Ok`),
  `verify_ct_sound`, `verify_ct_total`; conditional `verify_ct_binds`
  (`HmacInjOn32`, `self.WF`); end-to-end E3.
- [ ] **Step 7.4 — `VerifyHdr.lean`.** ∥ with 7.3
  Mirror via `verify_decision` + `.InvalidHdrMac`; conditional
  `verify_hdr_rejects_ct_macs` (via `mac_ct_ne_mac_hdr`); E4.
- [ ] **Step 7.5 — `EndToEnd.lean`.**
  Collect E1–E5 (those not already housed in 7.1–7.4), prove the **bridge
  theorem** `HmacInjOn32_of_hash : HashCR spec.sha.sha256 →
  HashKeyBinding spec.sha.sha256 → HmacInjOn32` (from MT6 + ML6/ML7 at the
  32-byte instance), and derive E6 (`mac_ct_model_inj_of_hash`,
  `verify_ct_binds_of_hash`).

### Phase 8 — Serialization closure

- [ ] **Step 8.1 — `Serialize/IntoPb.lean` / `FromPb.lean`.**
  Pure equations `into_pb_eq : into_pb self = ok ⟨self.root_key,
  self.mac_key⟩` and `from_pb_eq` (restating the clone helper as
  `CloneVec.clone v = ok v` first); preservation theorems
  `into_pb_preserves_derived_from` / `from_pb_preserves_derived_from`
  (via `derived_from_of_eq`).
- [ ] **Step 8.2 — `Serialize/RoundTrip.lean`.**
  `from_pb_into_pb_id : (into_pb auth >>= from_pb) = ok auth` (by `rw`
  with the `_eq` equations + structure eta), `into_pb_from_pb_id`,
  `round_trip_preserves_mac_ct` (the formal counterpart of the
  non-extracted Rust test `serialize::test::round_trip`), and
  `round_trip_preserves_derived_from`.

### Phase 9 — Error formatting (independent; any time after Phase 0)

- [ ] **Step 9.1 — `Error/Fmt.lean`.** ∥
  `Error.message` / `Error.debugName` (the six `thiserror` strings /
  variant names); single-equation specs `display_fmt_spec` /
  `debug_fmt_spec` (fmt behaves as `Formatter.write_str f
  (Error.message self)`); injectivity of both maps (by `decide`).

### Phase 10 — Final audit

- [ ] **Step 10.1 — Audit and close out.**
  - `lake build` green; `./scripts/check-lint.sh` clean.
  - `grep -rn sorry Spqr/Math Spqr/Specs SrcTranslated/FunsExternal.lean`
    → empty on the touched trees.
  - Axiom/opaque diff vs. Step 0.1: concat axioms (×2) and `black_box`
    **removed**; **zero axioms added**; the only remaining crypto opaque
    is `hkdf_bytes_raw`.
  - Every E-theorem (E1–E6) present and proven; STV1/MTV1 vectors pass.
  - Update the §8 progress table; update
    `doc/truong/authenticator_functions.txt` cross-references if the repo
    convention requires it.

---

## 6. Dependency DAG

```
0.1 baseline
  │
  ├────────────── mathematics track ──────────────┐
  │   1.1 Word ─► {1.2 Pad, 1.3 Parse, 1.5 Rounds}│
  │                1.4 Constants ──► 1.5          │
  │                {1.2,1.3,1.5} ─► 1.6 Core ─► 1.7 Vectors
  │                                  │
  │   2.1 scaffolding ─ 2.2 Xor ─► 2.3 Key ─► 2.4 Core ─► 2.5 Alg ─► 2.7 Vectors
  │                                  │                └─► 2.6 Security
  │                                  ▼
  │   3.1 hash_len/block_len ──► 3.2 spec.hmac_bytes + hmac model
  │                                  │
  ├────────────── plumbing track ────┼────────────────────────────┐
  │   3.3 hkdf model + hkdf_to_vec_spec                           │
  │   3.4 black_box ──────────────► 5.1 compare_spec              │
  │   3.5 concat / index / to_vec                                 │
  │   3.6 U64.to_be_bytes                                         │
  │        │                        │                             │
  │        ▼                        ▼                             │
  │   4.1 Defs.lean (labels, models incl. *_eq_core,              │
  │       derived_from, WF, HmacInjOn32/HkdfInj)                  │
  │        │                                                      │
  │   ┌────┼──────────┬──────────────┬──────────────┐             │
  │   ▼    ▼          ▼              ▼              ▼             │
  │ 6.1 update    6.3 MACSIZE    7.1 mac_ct     7.2 mac_hdr       │
  │   │                              │              │             │
  │   ▼                              ▼              ▼             │
  │ 6.2 new                     7.3 verify_ct  7.4 verify_hdr     │
  │   │                              └──────┬───────┘             │
  │   ▼                                     ▼                     │
  │ 8.1 into_pb/from_pb ─► 8.2 RoundTrip   7.5 EndToEnd (needs 2.6)
  │                                                               │
  │ 9.1 Error/Fmt (independent)                                   │
  └──────────────────────────────► 10.1 final audit ◄─────────────┘
```

Critical path: 1.1 → 1.6 → 2.5 → 3.2 → 4.1 → 7.1 → 7.3 → 7.5 → 10.1.
Everything off that path (1.7, 2.6/2.7, 3.3–3.6, 5.1, 6.x, 8.x, 9.1) can be
parallelised across contributors.

---

## 7. Risk Register & Design Decisions

| # | Risk / decision | Resolution |
|---|-----------------|-----------|
| R1 | SHA round-function proofs blow up `simp` | keep `schedule`/`compress` opaque-to-simp; expose only equational lemmas (ST3/ST4, ML8) downstream |
| R2 | Constant-table transcription errors | STV1/MTV1 `native_decide` vectors catch any wrong constant (1.7/2.7 gate 1.4) |
| R3 | `native_decide` cost on large vectors | restrict to the short official vectors; long ones stay commented out |
| R4 | Aeneas scalar API gaps (rotations, 64-bit folds) | Step 1.1 audits available lemmas first; missing ones are proved locally, never assumed |
| R5 | Rust hash cores are not extracted ⇒ no machine-checked link below the `hmac` boundary | acknowledged scope limit: the correctness statement lives at the `libcrux_hmac.hmac` boundary; fidelity below it is evidenced by the FIPS/RFC vectors |
| R6 | Replacing `libcrux_hmac.hmac` / `kdf.hkdf_to_slice` bodies breaks non-authenticator consumers (chain, v1 paths) | mandatory consumer grep + full `lake build` inside Steps 3.2/3.3; fix-ups land in the same step |
| R7 | Flatten model of `concat` cannot be unconditionally `ok` (`Usize.max` overflow) | overflow-guarded model; bounds become explicit preconditions of `update_spec`/`mac_*_spec`, documented per docstring |
| R8 | `compare` indexes `rhs` at `lhs` indices (asymmetric panic) | the `compare_spec` precondition is settled during the Step 5.1 proof; equal length suffices at both call sites |
| R9 | Pre-existing weaker specs/predicates in the tree (e.g. a legacy joint-derivation predicate) | each phase **replaces** statements but adds bridge corollaries (Step 4.1.4) so existing consumers keep compiling; regression grep per §1.4 |
| R10 | Structure eta for the round-trip identities | Lean 4 structures have definitional eta; fall back to field-wise statements if the extraction interferes |
| R11 | Crypto-level claims about uninterpreted functions | only conditional theorems with named `Prop` premises (P15/P16, M7); the axiom count strictly decreases |
| R12 | `aeneas-config.yml` / Rust sources | no changes required; all work is in the Lean model/spec layer |

**Optional follow-up (out of scope for the checklist):** instantiate
`hkdf_bytes` concretely from `spec.hmac_bytes` per RFC 5869
(`PRK = HMAC(0³², ikm)`; `T(1) = HMAC(PRK, info ∥ 0x01) = root_key`;
`T(2) = HMAC(PRK, T(1) ∥ info ∥ 0x02) = mac_key`), parameterised by the
algorithm. This removes the last crypto opaque and automatically deepens E5
to pure HMAC-SHA-256 terms — no statement above Phase 4 needs to change,
because everything is phrased via `spec.hkdf_bytes`.

---

## 8. Success Criteria & Progress Tracking

| Metric | Baseline (Step 0.1) | Target (Step 10.1) |
|--------|--------------------:|-------------------:|
| Authenticator items with a **functional** spec | measured at 0.1 | 10 of 11 (the 11th, the Rust `round_trip` test, is superseded by `RoundTrip.lean`) |
| `sorry` in `Spqr/Math` + `Spqr/Specs` + `FunsExternal.lean` | measured at 0.1 | 0 |
| Axioms on the authenticator path | ≥ 3 (`concat` ×2, `black_box`) | 0 — **net decrease, zero added** |
| Opaque crypto cores | measured at 0.1 | 1 (`hkdf_bytes_raw` only; HMAC and SHA fully structural & executable) |
| New definitions | — | 14 (S) + 7 (M) + 9 (A) + 19 (P) |
| New lemmas/theorems | — | ≈ 19 SL + 7 ST + 8 ML + 7 MT + 5 model specs + ≈ 36 protocol lemmas + 6 E-theorems + 2 vector suites |
| End-to-end characterisation | — | E1–E4: extracted Rust MAC/verify ≡ RFC 2104 / FIPS 180-2 composition |
| Crypto assumptions below the MAC layer | monolithic | only `HashCR sha256`, `HashKeyBinding sha256`, `HkdfInj` — all named premises |

Execution checklist (mirror of §5 — tick as steps land):

- [ ] 0.1 Baseline recorded
- [ ] 1.1 `Hash/Word.lean` — rotations, modular word arithmetic
- [ ] 1.2 `Hash/Pad.lean` — padding, `pad_inj`
- [ ] 1.3 `Hash/Parse.lean` — blocks, BE codecs
- [ ] 1.4 `Sha1/Constants.lean`, `Sha2/Constants.lean`
- [ ] 1.5 `Sha1/Round.lean`, `Sha2/Round.lean`
- [ ] 1.6 `Hash/Params.lean` + `Hash/Core.lean` (ST1–ST6)
- [ ] 1.7 `Hash/TestVectors.lean` (FIPS vectors)
- [ ] 2.1 Generic-layer scaffolding decision
- [ ] 2.2 `Hmac/Xor.lean`
- [ ] 2.3 `Hmac/Key.lean`
- [ ] 2.4 `Hmac/Core.lean` (hmacCore, MT1–MT3, MT5)
- [ ] 2.5 `Hmac/Alg.lean` (hmacAlg, MT4)
- [ ] 2.6 `Hmac/Security.lean` (HashCR/HashKeyBinding, MT6)
- [ ] 2.7 `Hmac/TestVectors.lean` (RFC 2202/4231 vectors)
- [ ] 3.1 `HashLen.lean` + `BlockLen.lean`
- [ ] 3.2 `spec.hmac_bytes` (structural) + `libcrux_hmac.hmac` model + specs
- [ ] 3.3 HKDF model + functional `hkdf_to_vec_spec` (one PR)
- [ ] 3.4 `black_box` identity model
- [ ] 3.5 `SliceConcat` / `VecIndexRange` / `SliceToVec` specs
- [ ] 3.6 `U64ToBeBytes` lemmas
- [ ] 4.1 `Authenticator/Defs.lean` (labels, models, `derived_from`, `WF`, premises)
- [ ] 5.1 `Util/Compare.lean` (`compare_spec`)
- [ ] 6.1 functional `update_spec`
- [ ] 6.2 `New.lean`
- [ ] 6.3 `MACSIZE.lean`
- [ ] 7.1 `MacCt.lean` (+ E1)
- [ ] 7.2 `MacHdr.lean` (+ E2)
- [ ] 7.3 `VerifyCt.lean` (+ E3)
- [ ] 7.4 `VerifyHdr.lean` (+ E4)
- [ ] 7.5 `EndToEnd.lean` (E5, bridge theorem, E6)
- [ ] 8.1 `IntoPb`/`FromPb` pure equations + preservation
- [ ] 8.2 `Serialize/RoundTrip.lean`
- [ ] 9.1 `Error/Fmt.lean`
- [ ] 10.1 Final audit (build, lint, sorry/axiom check, tables updated)
