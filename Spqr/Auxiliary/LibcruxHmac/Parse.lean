/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Auxiliary.LibcruxHmac.Pad

/-!
# Block parsing and big-endian codecs for SHA-1 / SHA-2

FIPS 180-2 §5.2 specifies how a padded message (whose length is a multiple
of the block size `B`) is split into blocks, and how each block is parsed
into words of the appropriate width:

* **Block splitting**: the padded byte stream is divided into `B`-byte blocks
  (`B = 64` for SHA-1/SHA-256, `B = 128` for SHA-384/SHA-512);
* **Word parsing**: each block is further divided into 16 words of `w` bits
  (`w = 32` for SHA-1/SHA-256, `w = 64` for SHA-384/SHA-512), each decoded
  in **big-endian** byte order;
* **Digest serialization**: the final hash state (a list of words) is
  serialized back to bytes in big-endian order.

This file defines:

* `toBlocks B bs` — split a list into `B`-element blocks (S6);
* `natOfBE` / `natToBE` — big-endian byte↔natural-number codecs;
* `wordOfBytesBE32/64`, `bytesOfWordBE32/64` — single-word codecs;
* `wordsBE32/64`, `bytesBE32/64` — list-level codecs (S7);

together with:

natural language specs:
- `toBlocks_chunk_length` (SL8): each block has length exactly `B`;
- `toBlocks_flatten` (SL8): flattening recovers the input when `B ∣ bs.length`;
- `toBlocks_length` (SL8): number of blocks = `bs.length / B`;
- `bytesOfWordBE32_length` / `bytesOfWordBE64_length`: single-word codec lengths;
- `bytesBE32_length` / `bytesBE64_length` (SL10): list codec length equations;
- `wordsBE32_length` / `wordsBE64_length` (SL10): list codec length equations;
- `natOfBE_natToBE` / `natToBE_natOfBE` (SL9 foundation): Nat-level round-trips;
- `wordOfBytesBE32_bytesOfWordBE32` / `bytesOfWordBE32_wordOfBytesBE32` (SL9):
  single-word round-trips;
- `wordsBE32_bytesBE32` / `bytesBE32_wordsBE32` (SL9): list-level round-trips;
- similarly for 64-bit variants.

**Source**: FIPS 180-2 §5.2 (parsing the message into blocks).
-/

open Aeneas Aeneas.Std

namespace spec.sha

/-! ## Block splitting (S6, FIPS 180-2 §5.2) -/

/-- Split a list into non-overlapping blocks of exactly `B` elements,
    discarding any incomplete trailing portion.

    FIPS 180-2 §5.2: the padded message (whose length is a multiple of `B`)
    is divided into `B`-byte blocks `M⁽¹⁾, M⁽²⁾, …, M⁽ᴺ⁾`. -/
def toBlocks {α : Type*} (B : Nat) (bs : List α) : List (List α) :=
  if B = 0 then []
  else if bs.length < B then []
  else bs.take B :: toBlocks B (bs.drop B)
termination_by bs.length
decreasing_by simp [List.length_drop]; omega

/-- **Spec lemma (`toBlocks_nil`)**: splitting an empty list produces
    no blocks. -/
@[simp]
theorem toBlocks_nil {α : Type*} (B : Nat) : toBlocks B ([] : List α) = [] := by
  unfold toBlocks; simp

/-- **Spec lemma (`toBlocks_zero`)**: block size 0 produces no blocks. -/
@[simp]
theorem toBlocks_zero {α : Type*} (bs : List α) : toBlocks 0 bs = [] := by
  unfold toBlocks; simp

/-- Unfolding equation for `toBlocks` when `B > 0` and the list is long
    enough. -/
theorem toBlocks_cons {α : Type*} (B : Nat) (hB : B ≠ 0) (bs : List α)
    (h : B ≤ bs.length) :
    toBlocks B bs = bs.take B :: toBlocks B (bs.drop B) := by
  conv_lhs => rw [toBlocks]
  simp [hB, show ¬(bs.length < B) from by omega]

/-- **Spec lemma (`toBlocks_chunk_length`, SL8)**: every block produced by
    `toBlocks B bs` has length exactly `B` (when `B > 0`). -/
theorem toBlocks_chunk_length {α : Type*} (B : Nat) (hB : B ≠ 0) (bs : List α) :
    ∀ c ∈ toBlocks B bs, c.length = B := by
  unfold toBlocks
  simp only [hB]
  split
  · simp
  · rename_i hge
    simp only [List.mem_ite_nil_left, not_lt, List.mem_cons, and_imp]
    intro c hc hc1
    rcases hc1 with hc | hc
    · grind
    · exact toBlocks_chunk_length B hB (bs.drop B) c hc
termination_by bs.length
decreasing_by simp [List.length_drop]; omega

/-- **Spec lemma (`toBlocks_length`, SL8)**: the number of blocks is
    `bs.length / B` (when `B > 0`). -/
theorem toBlocks_length {α : Type*} (B : Nat) (hB : B ≠ 0) (bs : List α) :
    (toBlocks B bs).length = bs.length / B := by
  by_cases h : B ≤ bs.length
  · have hBpos : 0 < B := by omega
    rw [toBlocks_cons B hB bs h, List.length_cons,
        toBlocks_length B hB (bs.drop B), List.length_drop]
    exact (Nat.div_eq_sub_div hBpos h).symm
  · push Not at h
    rw [toBlocks]
    simp only [if_neg hB, if_pos h, List.length_nil]
    exact (Nat.div_eq_of_lt h).symm
termination_by bs.length
decreasing_by simp [List.length_drop]; omega


/-- **Spec lemma (`toBlocks_flatten`, SL8)**: flattening the blocks recovers
    the original list, provided the block size divides the list length. -/
theorem toBlocks_flatten {α : Type*} (B : Nat) (hB : B ≠ 0) (bs : List α)
    (hdiv : B ∣ bs.length) :
    (toBlocks B bs).flatten = bs := by
  unfold toBlocks
  simp only [hB]
  split
  · simp_all
  · rename_i hge
    split
    · rename_i hlt
      simp only [List.flatten_nil]
      exact (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_dvd_of_lt hdiv hlt)).symm
    · simp only [List.flatten_cons]
      have hdvd : B ∣ (bs.drop B).length := by
        obtain ⟨k, hk⟩ := hdiv
        refine ⟨k - 1, ?_⟩
        rw [List.length_drop, hk]
        cases k with
        | zero => omega
        | succ n => simp [Nat.mul_succ]
      rw [toBlocks_flatten B hB (bs.drop B) hdvd]
      exact List.take_append_drop B bs
termination_by bs.length
decreasing_by simp [List.length_drop]; omega

/-- Auxiliary: splitting a flattened list of uniform-length sublists recovers
    the original sublists.  Used for the list-level codec round-trips. -/
theorem toBlocks_flatten_map {α : Type*} (k : Nat) (hk : k ≠ 0) (xss : List (List α))
    (hall : ∀ xs ∈ xss, xs.length = k) :
    toBlocks k xss.flatten = xss := by
  induction xss with
  | nil => simp
  | cons xs xss' ih =>
    have hxs : xs.length = k := hall xs List.mem_cons_self
    have hall' : ∀ ys ∈ xss', ys.length = k :=
      fun ys hy => hall ys (List.mem_cons_of_mem xs hy)
    simp only [List.flatten_cons]
    rw [toBlocks_cons k hk (xs ++ xss'.flatten) (by simp [hxs])]
    congr 1
    · rw [← hxs]; simp
    · rw [show (xs ++ xss'.flatten).drop k = xss'.flatten from by rw [← hxs]; simp]
      exact ih hall'

/-! ## Big-endian byte ↔ natural-number codecs -/

/-- Decode a sequence of bytes as a big-endian natural number.

    `natOfBE [b₀, b₁, …, bₙ₋₁] = b₀·256ⁿ⁻¹ + b₁·256ⁿ⁻² + ⋯ + bₙ₋₁`

    Defined as a left fold so that the key lemma `natOfBE_append_singleton`
    holds by `List.foldl_append`. -/
def natOfBE (bs : List U8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.val) 0

/-- `natOfBE` of the empty list is 0. -/
@[simp]
theorem natOfBE_nil : natOfBE ([] : List U8) = 0 := rfl

/-- `natOfBE` of a singleton is the byte's value. -/
@[simp]
theorem natOfBE_singleton (b : U8) : natOfBE [b] = b.val := by
  simp [natOfBE]

/-- Key structural lemma: appending a byte multiplies the accumulated value
    by 256 and adds the new byte.

    This matches the recursion pattern of `natToBE` / `lenBytes` and makes
    both round-trip proofs straightforward. -/
theorem natOfBE_append_singleton (bs : List U8) (b : U8) :
    natOfBE (bs ++ [b]) = natOfBE bs * 256 + b.val := by
  simp [natOfBE, List.foldl_append]

/-- Upper bound: `natOfBE bs < 256 ^ bs.length`. -/
theorem natOfBE_bound (bs : List U8) : natOfBE bs < 256 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [natOfBE]
  | append_singleton xs x ih =>
    rw [natOfBE_append_singleton, List.length_append, List.length_singleton]
    have hx : x.val < 256 := by scalar_tac
    have hxs : natOfBE xs + 1 ≤ 256 ^ xs.length := ih
    calc natOfBE xs * 256 + x.val
        < 256 ^ xs.length * 256 := by nlinarith
      _ = 256 ^ (xs.length + 1) := by rw [pow_succ]

/-! ### Encoding: natural number to big-endian bytes -/

/-- Encode a natural number as `n` big-endian bytes.

    This is an alias for `lenBytes` (defined in `Pad.lean`); the alternate
    name is provided for clarity in the codec context. -/
abbrev natToBE := lenBytes

/-- `natToBE n v` produces exactly `n` bytes. -/
@[simp]
theorem natToBE_length (n v : Nat) : (natToBE n v).length = n :=
  lenBytes_length n v

/-! ### Byte-reconstruction helper -/

/-- The `.val` of `byte n` is `n % 256`. -/
theorem byte_mod_val (n : Nat) : (byte n).val = n % 256 := by
  simp [UScalar.val, BitVec.toNat_ofNat]

/-- Reconstructing a `U8` via `byte` from its `.val` gives back the original
    byte: `byte b.val = b` for every `b : U8`. -/
theorem byte_val_id (b : U8) : byte b.val = b := by
  simp only [byte]
  rw [UScalar.eq_equiv_bv_eq]
  simp

/-! ### Nat-level codec round-trips -/

/-- Auxiliary modular-arithmetic identity used by `natOfBE_natToBE`:
    `(v / b % a) * b + v % b = v % (a * b)` for positive `a` and `b`. -/
private theorem mod_mul_decomp (v a b : Nat) :
    (v / b % a) * b + v % b = v % (a * b) := by
  -- Introduce quotients and remainders as named variables
  set q := v / b
  set r := v % b
  set qk := q / a
  set rk := q % a
  -- Key equalities from Nat.div_add_mod
  have h1 := Nat.div_add_mod v b      -- b * q + r = v
  have h2 := Nat.div_add_mod q a      -- a * qk + rk = q
  have h3 : qk = v / (b * a) := Nat.div_div_eq_div_mul v b a
  have h4 := Nat.div_add_mod v (b * a) -- (b * a) * (v / (b * a)) + v % (b * a) = v
  -- Expand v two ways and equate
  have expand : v = b * a * qk + rk * b + r := by grind
  rw [Nat.mul_comm a b]
  grind

/-- **Spec lemma (`natOfBE_natToBE`)**: decoding an encoded value recovers it
    modulo the representable range: `natOfBE (natToBE n v) = v % 256^n`.

    Together with `natToBE_natOfBE`, this establishes the big-endian
    byte↔Nat codec as a faithful round-trip. -/
theorem natOfBE_natToBE (n v : Nat) :
    natOfBE (natToBE n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [natToBE, lenBytes, natOfBE, Nat.mod_one]
  | succ k ih =>
    simp only [natToBE, lenBytes]
    rw [natOfBE_append_singleton, ih, byte_mod_val,
        Nat.mod_eq_of_lt (Nat.mod_lt v (by omega : (0 : Nat) < 256))]
    -- Goal: v / 256 % 256 ^ k * 256 + v % 256 = v % 256 ^ (k + 1)
    rw [Nat.pow_succ]
    exact mod_mul_decomp v (256 ^ k) 256


/-- **Spec lemma (`natToBE_natOfBE`)**: encoding a decoded byte sequence
    recovers the original bytes: `natToBE bs.length (natOfBE bs) = bs`.

    Proof by reverse induction on `bs`, using the fact that `natToBE`
    peels off least-significant bytes (matching `natOfBE_append_singleton`). -/
theorem natToBE_natOfBE (bs : List U8) :
    natToBE bs.length (natOfBE bs) = bs := by
  induction bs using List.reverseRecOn with
  | nil => simp [natToBE, lenBytes]
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton]
    simp only [natToBE, lenBytes]
    rw [natOfBE_append_singleton]
    have hx_lt : x.val < 256 := by scalar_tac
    -- Simplify division and modulus by literal 256
    have h_div : (natOfBE xs * 256 + x.val) / 256 = natOfBE xs := by
      rw [show natOfBE xs * 256 + x.val = x.val + natOfBE xs * 256 from by ring]
      rw [Nat.add_mul_div_right _ _ (by omega : (0 : Nat) < 256)]
      simp [Nat.div_eq_of_lt hx_lt]
    have h_mod : (natOfBE xs * 256 + x.val) % 256 = x.val := by
      rw [show natOfBE xs * 256 + x.val = x.val + 256 * natOfBE xs from by ring]
      simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx_lt]
    rw [h_div, h_mod]
    simp [byte_val_id]
    grind

/-! ## Single-word codecs -/

/-- Decode a list of bytes (big-endian) into a 32-bit word.

    Takes (at most) the first 4 bytes, decodes them as a big-endian natural
    number, and wraps the result into a `U32`.  If fewer than 4 bytes are
    provided, the missing bytes are implicitly zero (most-significant). -/
def wordOfBytesBE32 (bs : List U8) : U32 :=
  ⟨BitVec.ofNat 32 (natOfBE (bs.take 4))⟩

/-- Encode a 32-bit word as 4 big-endian bytes. -/
def bytesOfWordBE32 (w : U32) : List U8 :=
  natToBE 4 w.val

/-- Decode a list of bytes (big-endian) into a 64-bit word.

    Takes (at most) the first 8 bytes, decodes them as a big-endian natural
    number, and wraps the result into a `U64`.  If fewer than 8 bytes are
    provided, the missing bytes are implicitly zero (most-significant). -/
def wordOfBytesBE64 (bs : List U8) : U64 :=
  ⟨BitVec.ofNat 64 (natOfBE (bs.take 8))⟩

/-- Encode a 64-bit word as 8 big-endian bytes. -/
def bytesOfWordBE64 (w : U64) : List U8 :=
  natToBE 8 w.val

/-! ### Single-word codec lengths -/

/-- **Spec lemma (`bytesOfWordBE32_length`)**: encoding a `U32` always
    produces exactly 4 bytes. -/
@[simp]
theorem bytesOfWordBE32_length (w : U32) : (bytesOfWordBE32 w).length = 4 :=
  natToBE_length 4 w.val

/-- **Spec lemma (`bytesOfWordBE64_length`)**: encoding a `U64` always
    produces exactly 8 bytes. -/
@[simp]
theorem bytesOfWordBE64_length (w : U64) : (bytesOfWordBE64 w).length = 8 :=
  natToBE_length 8 w.val

/-! ### Single-word round-trips (SL9 foundation) -/

/-- **Spec lemma (`wordOfBytesBE32_bytesOfWordBE32`, SL9)**:
    decoding an encoded `U32` recovers the original word. -/
@[simp]
theorem wordOfBytesBE32_bytesOfWordBE32 (w : U32) :
    wordOfBytesBE32 (bytesOfWordBE32 w) = w := by
  simp only [wordOfBytesBE32, bytesOfWordBE32]
  rw [show (natToBE 4 w.val).take 4 = natToBE 4 w.val from by
    simp [List.take_of_length_le]]
  rw [natOfBE_natToBE]
  have h256 : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
  rw [h256, Nat.mod_eq_of_lt (show w.val < 2 ^ 32 from by
    change w.bv.toNat < 2 ^ 32; exact w.bv.isLt)]
  rw [UScalar.eq_equiv_bv_eq]
  simp

/-- **Spec lemma (`bytesOfWordBE32_wordOfBytesBE32`, SL9)**:
    encoding a decoded 4-byte sequence recovers the original bytes. -/
theorem bytesOfWordBE32_wordOfBytesBE32 (bs : List U8) (hlen : bs.length = 4) :
    bytesOfWordBE32 (wordOfBytesBE32 bs) = bs := by
  simp only [bytesOfWordBE32, wordOfBytesBE32]
  rw [show bs.take 4 = bs from by rw [← hlen]; simp]
  show natToBE 4 (⟨BitVec.ofNat 32 (natOfBE bs)⟩ : U32).val = bs
  simp only [UScalar.val]
  have h256 : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
  rw [show (BitVec.ofNat 32 (natOfBE bs)).toNat = natOfBE bs from by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (h256 ▸ hlen ▸ natOfBE_bound bs)]
  rw [← hlen]
  exact natToBE_natOfBE bs


/-- **Spec lemma (`wordOfBytesBE64_bytesOfWordBE64`, SL9)**:
    decoding an encoded `U64` recovers the original word. -/
@[simp]
theorem wordOfBytesBE64_bytesOfWordBE64 (w : U64) :
    wordOfBytesBE64 (bytesOfWordBE64 w) = w := by
  simp only [wordOfBytesBE64, bytesOfWordBE64]
  rw [show (natToBE 8 w.val).take 8 = natToBE 8 w.val from by
    simp [List.take_of_length_le]]
  rw [natOfBE_natToBE]
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  rw [h256, Nat.mod_eq_of_lt (show w.val < 2 ^ 64 from by
    change w.bv.toNat < 2 ^ 64; exact w.bv.isLt)]
  rw [UScalar.eq_equiv_bv_eq]
  simp

/-- **Spec lemma (`bytesOfWordBE64_wordOfBytesBE64`, SL9)**:
    encoding a decoded 8-byte sequence recovers the original bytes. -/
theorem bytesOfWordBE64_wordOfBytesBE64 (bs : List U8) (hlen : bs.length = 8) :
    bytesOfWordBE64 (wordOfBytesBE64 bs) = bs := by
  simp only [bytesOfWordBE64, wordOfBytesBE64]
  rw [show bs.take 8 = bs from by rw [← hlen]; simp]
  show natToBE 8 (⟨BitVec.ofNat 64 (natOfBE bs)⟩ : U64).val = bs
  simp only [UScalar.val]
  have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  rw [show (BitVec.ofNat 64 (natOfBE bs)).toNat = natOfBE bs from by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (h256 ▸ hlen ▸ natOfBE_bound bs)]
  rw [← hlen]
  exact natToBE_natOfBE bs

/-! ## List-level codecs (S7) -/

/-- Parse a byte sequence into big-endian 32-bit words (groups of 4 bytes).

    Incomplete trailing groups are discarded (see `toBlocks`). -/
def wordsBE32 (bs : List U8) : List U32 :=
  (toBlocks 4 bs).map wordOfBytesBE32

/-- Serialize a list of 32-bit words to big-endian bytes (4 bytes per word). -/
def bytesBE32 (ws : List U32) : List U8 :=
  (ws.map bytesOfWordBE32).flatten

/-- Parse a byte sequence into big-endian 64-bit words (groups of 8 bytes).

    Incomplete trailing groups are discarded (see `toBlocks`). -/
def wordsBE64 (bs : List U8) : List U64 :=
  (toBlocks 8 bs).map wordOfBytesBE64

/-- Serialize a list of 64-bit words to big-endian bytes (8 bytes per word). -/
def bytesBE64 (ws : List U64) : List U8 :=
  (ws.map bytesOfWordBE64).flatten

/-! ### List-level codec lengths (SL10) -/

/-- **Spec lemma (`wordsBE32_length`, SL10)**: the number of 32-bit words is
    `bs.length / 4`. -/
@[simp]
theorem wordsBE32_length (bs : List U8) :
    (wordsBE32 bs).length = bs.length / 4 := by
  simp [wordsBE32, toBlocks_length 4 (by omega)]

/-- **Spec lemma (`bytesBE32_length`, SL10)**: serializing `ws.length` words
    produces `4 * ws.length` bytes. -/
@[simp]
theorem bytesBE32_length (ws : List U32) :
    (bytesBE32 ws).length = 4 * ws.length := by
  induction ws with
  | nil => simp [bytesBE32]
  | cons w ws ih =>
    simp only [bytesBE32, List.map_cons, List.flatten_cons, List.length_append,
               bytesOfWordBE32_length, List.length_cons] at ih ⊢
    omega

/-- **Spec lemma (`wordsBE64_length`, SL10)**: the number of 64-bit words is
    `bs.length / 8`. -/
@[simp]
theorem wordsBE64_length (bs : List U8) :
    (wordsBE64 bs).length = bs.length / 8 := by
  simp [wordsBE64, toBlocks_length 8 (by omega)]

/-- **Spec lemma (`bytesBE64_length`, SL10)**: serializing `ws.length` words
    produces `8 * ws.length` bytes. -/
@[simp]
theorem bytesBE64_length (ws : List U64) :
    (bytesBE64 ws).length = 8 * ws.length := by
  induction ws with
  | nil => simp [bytesBE64]
  | cons w ws ih =>
    simp only [bytesBE64, List.map_cons, List.flatten_cons, List.length_append,
               bytesOfWordBE64_length, List.length_cons] at ih ⊢
    omega

/-! ### List-level round-trips (SL9) -/

/-- **Spec lemma (`wordsBE32_bytesBE32`, SL9)**: parsing serialized 32-bit
    words recovers the original word list. -/
@[simp]
theorem wordsBE32_bytesBE32 (ws : List U32) :
    wordsBE32 (bytesBE32 ws) = ws := by
  simp only [wordsBE32, bytesBE32]
  rw [toBlocks_flatten_map 4 (by omega) (ws.map bytesOfWordBE32) (by
    intro xs hxs
    simp only [List.mem_map] at hxs
    obtain ⟨w, _, rfl⟩ := hxs
    exact bytesOfWordBE32_length w)]
  rw [List.map_map]
  have h : wordOfBytesBE32 ∘ bytesOfWordBE32 = id :=
    funext fun w => wordOfBytesBE32_bytesOfWordBE32 w
  rw [h, List.map_id]


/-- **Spec lemma (`bytesBE32_wordsBE32`, SL9)**: serializing parsed 32-bit
    words recovers the original byte sequence (when the length is divisible
    by 4). -/
theorem bytesBE32_wordsBE32 (bs : List U8) (hdiv : 4 ∣ bs.length) :
    bytesBE32 (wordsBE32 bs) = bs := by
  simp only [bytesBE32, wordsBE32, List.map_map]
  -- Each chunk has length 4 by toBlocks_chunk_length
  have hchunk := toBlocks_chunk_length 4 (by omega) bs
  -- bytesOfWordBE32 ∘ wordOfBytesBE32 = id on 4-byte chunks
  rw [List.map_congr_left (g := id) (fun c hc => by
    simp only [Function.comp_apply, id_eq]
    exact bytesOfWordBE32_wordOfBytesBE32 c (hchunk c hc))]
  simp [List.map_id, toBlocks_flatten 4 (by omega) bs hdiv]


/-- **Spec lemma (`wordsBE64_bytesBE64`, SL9)**: parsing serialized 64-bit
    words recovers the original word list. -/
@[simp]
theorem wordsBE64_bytesBE64 (ws : List U64) :
    wordsBE64 (bytesBE64 ws) = ws := by
  simp only [wordsBE64, bytesBE64]
  rw [toBlocks_flatten_map 8 (by omega) (ws.map bytesOfWordBE64) (by
    intro xs hxs
    simp only [List.mem_map] at hxs
    obtain ⟨w, _, rfl⟩ := hxs
    exact bytesOfWordBE64_length w)]
  rw [List.map_map]
  have h : wordOfBytesBE64 ∘ bytesOfWordBE64 = id :=
    funext fun w => wordOfBytesBE64_bytesOfWordBE64 w
  rw [h, List.map_id]


/-- **Spec lemma (`bytesBE64_wordsBE64`, SL9)**: serializing parsed 64-bit
    words recovers the original byte sequence (when the length is divisible
    by 8). -/
theorem bytesBE64_wordsBE64 (bs : List U8) (hdiv : 8 ∣ bs.length) :
    bytesBE64 (wordsBE64 bs) = bs := by
  simp only [bytesBE64, wordsBE64, List.map_map]
  have hchunk := toBlocks_chunk_length 8 (by omega) bs
  rw [List.map_congr_left (g := id) (fun c hc => by
    simp only [Function.comp_apply, id_eq]
    exact bytesOfWordBE64_wordOfBytesBE64 c (hchunk c hc))]
  simp [List.map_id, toBlocks_flatten 8 (by omega) bs hdiv]


end spec.sha
