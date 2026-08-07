import Std.Tactic.BVDecide
import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopInvariant

/-!
# BLAKE2F positive-round word bridge

This file contains local algebra facts connecting the bytecode's 256-bit stack-word operations
used in the shared `mixG` routine to the trusted model's 64-bit operations.

The positive-round trace computes BLAKE2F words as `UInt256` values and explicitly masks every
intermediate result with `u64MaskWord`.  The semantic invariant stores model words as
`UInt64`, embedded into bytecode memory with `u64AsWord`.  These lemmas are the reusable bridge
between the two views.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private def u256bv (x : UInt256) : BitVec 256 :=
  BitVec.ofNat 256 x.toNat

private theorem u256bv_toNat (x : UInt256) :
    (u256bv x).toNat = x.toNat := by
  simp [u256bv, BitVec.toNat, BitVec.ofNat]
  exact x.val.isLt

private theorem u256bv_inj {x y : UInt256} (h : u256bv x = u256bv y) : x = y := by
  apply u256_inj
  have hv := congrArg BitVec.toNat h
  simpa [u256bv_toNat] using hv

private theorem u256bv_ofNat (n : Nat) :
    u256bv (UInt256.ofNat n) = BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rfl

private theorem u256bv_add (x y : UInt256) :
    u256bv (x + y) = u256bv x + u256bv y := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  simp [u256bv_toNat, uadd_toNat, UInt256.size]

private theorem u256bv_land (x y : UInt256) :
    u256bv (UInt256.land x y) = u256bv x &&& u256bv y := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  simp [u256bv_toNat]
  rw [u256_land_toNat]
  change Nat.land x.toNat y.toNat % UInt256.size = Nat.land x.toNat y.toNat
  exact Nat.mod_eq_of_lt (by
    have hy : y.toNat < 2 ^ 256 := by
      change y.toNat < UInt256.size
      exact y.val.isLt
    simpa [UInt256.size] using Nat.and_lt_two_pow x.toNat hy)

private theorem u256bv_lor (x y : UInt256) :
    u256bv (UInt256.lor x y) = u256bv x ||| u256bv y := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  simp [u256bv_toNat]
  rw [u256_lor_toNat]
  change Nat.lor x.toNat y.toNat % UInt256.size = Nat.lor x.toNat y.toNat
  exact Nat.mod_eq_of_lt (by
    have hx : x.toNat < 2 ^ 256 := by
      change x.toNat < UInt256.size
      exact x.val.isLt
    have hy : y.toNat < 2 ^ 256 := by
      change y.toNat < UInt256.size
      exact y.val.isLt
    simpa [UInt256.size] using Nat.or_lt_two_pow hx hy)

private theorem u256bv_xor (x y : UInt256) :
    u256bv (UInt256.xor x y) = u256bv x ^^^ u256bv y := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rw [BitVec.toNat_xor]
  rw [u256bv_toNat, u256bv_toNat]
  unfold UInt256.xor Fin.xor
  simp only
  apply Nat.mod_eq_of_lt
  change Nat.bitwise bne x.val.val y.val.val < 2 ^ 256
  exact Nat.bitwise_lt_two_pow x.val.isLt y.val.isLt

private theorem u256bv_shl (x : UInt256) (n : Nat) (hn : n < 256) :
    u256bv (UInt256.shiftLeft x (UInt256.ofNat n)) = u256bv x <<< n := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rw [ushl_ofNat_toNat x n hn]
  simp [u256bv_toNat, UInt256.size]

private theorem u256bv_shr (x : UInt256) (n : Nat) (hn : n < 256) :
    u256bv (UInt256.shiftRight x (UInt256.ofNat n)) = u256bv x >>> n := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  rw [ushr_ofNat_toNat x n hn]
  simp [u256bv_toNat]

private theorem bitvec_ofNat_toNat_eq_setWidth {n m : Nat} (x : BitVec n) :
    BitVec.ofNat m x.toNat = BitVec.setWidth m x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem u256bv_u64AsWord (w : UInt64) :
    u256bv (u64AsWord w) = BitVec.setWidth 256 w.toBitVec := by
  cases w with | ofBitVec wb =>
  unfold u64AsWord
  rw [u256bv_ofNat]
  change BitVec.ofNat 256 wb.toNat = BitVec.setWidth 256 wb
  rw [bitvec_ofNat_toNat_eq_setWidth]

private theorem u256bv_u64MaskWord :
    u256bv u64MaskWord = BitVec.ofNat 256 18446744073709551615 := by
  apply BitVec.eq_of_toNat_eq
  rw [u256bv_toNat]
  native_decide

theorem mask64Bytecode_u64AsWord_add3 (a b x : UInt64) :
    mask64Bytecode (u64AsWord a + u64AsWord b + u64AsWord x) =
      u64AsWord (a + b + x) := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_add, u256bv_add,
    u256bv_u64MaskWord,
    u256bv_u64AsWord, u256bv_u64AsWord, u256bv_u64AsWord, u256bv_u64AsWord]
  cases a with | ofBitVec ab =>
  cases b with | ofBitVec bb =>
  cases x with | ofBitVec xb =>
  change (BitVec.ofNat 256 18446744073709551615 &&&
      ((BitVec.setWidth 256 ab + BitVec.setWidth 256 bb) + BitVec.setWidth 256 xb)) =
    BitVec.setWidth 256 (UInt64.add (UInt64.add (UInt64.ofBitVec ab) (UInt64.ofBitVec bb))
      (UInt64.ofBitVec xb)).toBitVec
  simp [UInt64.add]
  bv_decide

theorem mask64Bytecode_u64AsWord_add2 (a b : UInt64) :
    mask64Bytecode (u64AsWord a + u64AsWord b) =
      u64AsWord (a + b) := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_add,
    u256bv_u64MaskWord,
    u256bv_u64AsWord, u256bv_u64AsWord, u256bv_u64AsWord]
  cases a with | ofBitVec ab =>
  cases b with | ofBitVec bb =>
  change (BitVec.ofNat 256 18446744073709551615 &&&
      (BitVec.setWidth 256 ab + BitVec.setWidth 256 bb)) =
    BitVec.setWidth 256 (UInt64.add (UInt64.ofBitVec ab) (UInt64.ofBitVec bb)).toBitVec
  simp [UInt64.add]
  bv_decide

theorem land_u64AsWord_u64Mask (w : UInt64) :
    UInt256.land (u64AsWord w) u64MaskWord = u64AsWord w := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_u64AsWord, u256bv_u64MaskWord]
  cases w with | ofBitVec wb =>
  change (BitVec.setWidth 256 wb &&& BitVec.ofNat 256 18446744073709551615) =
    BitVec.setWidth 256 wb
  bv_decide

theorem rotr64Bytecode_u64AsWord_xor_32_32 (d a : UInt64) :
    rotr64Bytecode (UInt256.xor (u64AsWord d) (u64AsWord a))
        (UInt256.ofNat 32) (UInt256.ofNat 32) =
      u64AsWord (Model.rotr64 (d ^^^ a) (UInt64.ofNat 32)) := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_lor,
    u256bv_shr _ 32 (by decide), u256bv_shl _ 32 (by decide),
    u256bv_u64MaskWord,
    u256bv_xor, u256bv_u64AsWord, u256bv_u64AsWord, u256bv_u64AsWord]
  cases d with | ofBitVec db =>
  cases a with | ofBitVec ab =>
  simp [Model.rotr64]
  bv_decide

theorem rotr64Bytecode_u64AsWord_xor_24_40 (d a : UInt64) :
    rotr64Bytecode (UInt256.xor (u64AsWord d) (u64AsWord a))
        (UInt256.ofNat 24) (UInt256.ofNat 40) =
      u64AsWord (Model.rotr64 (d ^^^ a) (UInt64.ofNat 24)) := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_lor,
    u256bv_shr _ 24 (by decide), u256bv_shl _ 40 (by decide),
    u256bv_u64MaskWord,
    u256bv_xor, u256bv_u64AsWord, u256bv_u64AsWord, u256bv_u64AsWord]
  cases d with | ofBitVec db =>
  cases a with | ofBitVec ab =>
  simp [Model.rotr64]
  bv_decide

theorem rotr64Bytecode_u64AsWord_xor_16_48 (d a : UInt64) :
    rotr64Bytecode (UInt256.xor (u64AsWord d) (u64AsWord a))
        (UInt256.ofNat 16) (UInt256.ofNat 48) =
      u64AsWord (Model.rotr64 (d ^^^ a) (UInt64.ofNat 16)) := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_lor,
    u256bv_shr _ 16 (by decide), u256bv_shl _ 48 (by decide),
    u256bv_u64MaskWord,
    u256bv_xor, u256bv_u64AsWord, u256bv_u64AsWord, u256bv_u64AsWord]
  cases d with | ofBitVec db =>
  cases a with | ofBitVec ab =>
  simp [Model.rotr64]
  bv_decide

theorem rotr64Bytecode_u64AsWord_xor_63_1 (d a : UInt64) :
    rotr64Bytecode (UInt256.xor (u64AsWord d) (u64AsWord a))
        (UInt256.ofNat 63) (UInt256.ofNat 1) =
      u64AsWord (Model.rotr64 (d ^^^ a) (UInt64.ofNat 63)) := by
  apply u256bv_inj
  rw [u256bv_land, u256bv_lor,
    u256bv_shr _ 63 (by decide), u256bv_shl _ 1 (by decide),
    u256bv_u64MaskWord,
    u256bv_xor, u256bv_u64AsWord, u256bv_u64AsWord, u256bv_u64AsWord]
  cases d with | ofBitVec db =>
  cases a with | ofBitVec ab =>
  simp [Model.rotr64]
  bv_decide

end Blake2f
