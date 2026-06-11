/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Deserialize

/-!
# Spec theorem for `PolyDecoder::from_pb`: loop body 1

The extracted Lean function `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0.body` performs
one step of the *inner* point-deserialization loop inside `PolyDecoder::from_pb`.  Given the
serialized byte vector `pts : Vec<u8>` for one of the 16 protobuf point-sets, the current sorted
set `v : SortedSet<Pt>` of already-decoded cartesian evaluation points, and the current byte
cursor `j : usize`, the body either:

  1. **Done** (`pts.len() < j + 4`): not enough bytes remain to decode another point, so the
     loop terminates and `v` is returned unchanged.
  2. **Continue** (`j + 4 ≤ pts.len()`): reads the next 4 bytes `(pts[j], pts[j+1], pts[j+2],
     pts[j+3])`, deserializes them into a cartesian point `Pt { x, y }` over GF(2¹⁶) via
     `Pt::deserialize` (big-endian decoding: `x.value = pts[j]·256 + pts[j+1]` and
     `y.value = pts[j+2]·256 + pts[j+3]`), pushes the resulting point onto the sorted set, and
     advances the cursor by 4.

In GF(2¹⁶) each field element is represented as a 16-bit unsigned integer; the big-endian
two-byte encoding satisfies `value = hi·256 + lo`.

The body spec composes:
  1. `Usize.+` (saturating-bound check `j + 4 ≤ Usize.max`) — to advance the cursor.
  2. `alloc.vec.Vec.len` — to read the source byte vector length.
  3. `alloc.vec.Vec.index` (`SliceIndexUsizeSlice`) — to retrieve each of the four bytes.
  4. `encoding.polynomial.Pt.deserialize` (spec from `Pt/Deserialize.lean`) — to reconstruct the
     `Pt` from the 4-byte chunk.
  5. `sorted_vec.SortedSet.push` (opaque axiom) — to insert the decoded point into the sorted
     set.  Because `SortedSet.push` is extracted as an opaque axiom (no provable behaviour), we
     parameterise the spec by a hypothetical successful push result `v_push` and propagate it
     through the postcondition.

**Source**: spqr/src/encoding/polynomial.rs (lines 842:12-846:13)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

/-! ## Spec theorem for the inner from_pb loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0.body`**:

One step of the inner 4-byte-chunk deserialization loop inside `PolyDecoder::from_pb`.  Given the
serialized byte vector `pts`, the running sorted set of decoded points `v`, and the current byte
cursor `j`, the body decides between termination (insufficient bytes left) and a single decode +
push step.

• The function always succeeds (no panic) provided the cursor can advance by 4 without overflow
  (`j.val + 4 ≤ Usize.max`) and the opaque `SortedSet.push` axiom returns `ok` on the decoded
  cartesian point.

• In the **done** case (`pts.len() < j + 4`):
    the sorted set is returned unchanged: `v' = v`.

• In the **cont** case (`j + 4 ≤ pts.len()`):
    - the cursor has advanced by 4: `j'.val = j.val + 4`;
    - there exists a cartesian point `p : Pt` whose coordinates are the big-endian two-byte
      decodings of the next 4 bytes of `pts`:
        `p.x.value.val = (pts[j]).val · 256 + (pts[j+1]).val`
        `p.y.value.val = (pts[j+2]).val · 256 + (pts[j+3]).val`
      and `v'` is exactly the sorted set produced by pushing `p` onto `v`.

    This corresponds to the Rust body:
    ```rust
    while j + 4 <= pts.len() {
        let chunk: [u8; 4] = [pts[j], pts[j + 1], pts[j + 2], pts[j + 3]];
        v.push(Pt::deserialize(chunk));
        j += 4;
    }
    ```

This establishes that one step of the inner loop faithfully deserializes a single cartesian point
from its 4-byte big-endian encoding and inserts it into the sorted set.

**Source**: spqr/src/encoding/polynomial.rs (lines 842:12-846:13)
-/
@[step]
theorem body_spec
    (pts : alloc.vec.Vec Std.U8)
    (v : sorted_vec.SortedSet Pt)
    (j : Std.Usize)
    (h_j_overflow : j.val + 4 ≤ Usize.max) :
    body pts v j ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ pts.val.length < j.val + 4
      | ControlFlow.cont (v', j') =>
          j.val + 4 ≤ pts.val.length ∧
          j'.val = j.val + 4 ∧
          ∃ (p : Pt),
            p.x.value.val =
              (pts.val[j.val]!).val * 256 + (pts.val[j.val + 1]!).val ∧
            p.y.value.val =
              (pts.val[j.val + 2]!).val * 256 + (pts.val[j.val + 3]!).val ∧
            ∃ (n : Std.Usize) (o : Option Pt),
              sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd v p =
                ok ((n, o), v') ⦄ := by
  unfold body
  step*
  simp_all only [Array.getElem!_Nat_eq, List.Vector.length_val, UScalar.ofNatCore_val_eq,
    Nat.ofNat_pos, getElem!_pos, Nat.one_lt_ofNat, Nat.reduceLT, Nat.lt_add_one,
    List.getElem!_eq_getElem?_getD, true_and]
  constructor
  · -- cont case: enough bytes remain; perform deserialize + push + advance
    grind
  · -- done case: insufficient bytes
    simp_all
    use p
    simp_all
    simp[Array.make]
    simp [sorted_vec.SortedSet.push]
    grind


end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0
