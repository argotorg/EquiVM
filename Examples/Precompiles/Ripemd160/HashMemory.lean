import Examples.Precompiles.Ripemd160.Common

/-!
# RIPEMD-160 runtime memory layout

Arithmetic and memory views used by the optimized Yul hash routine. The routine enters at PC 776
with a Solidity `bytes memory` pointer at `128` and allocates its padded message at the current free
memory pointer.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def hashPaddedLengthWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (calldataSizeWord I + ⟨72⟩) (UInt256.lnot ⟨63⟩)

def hashPadPtr (I : ExecutionEnv) : UInt256 := fallbackFreePtr I

def hashNewFreePtr (I : ExecutionEnv) : UInt256 :=
  hashPadPtr I + hashPaddedLengthWord I

def hashAllocatedMem (I : ExecutionEnv) : ByteArray :=
  (hashNewFreePtr I).toByteArray.write 0 (fallbackPaddedMem I) 64 32

def hashCopiedMem (I : ExecutionEnv) : ByteArray :=
  (hashAllocatedMem I).write 160 (hashAllocatedMem I)
    (hashPadPtr I).toNat I.calldata.size

def hashCopiedAw (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (MachineState.M (fallbackPaddedAw I).toNat
    (max (hashPadPtr I).toNat 160) I.calldata.size)

/-- Number of 32-byte zeroing stores performed by the padding loop. -/
def hashZeroIterations (I : ExecutionEnv) : Nat :=
  (Model.paddedLength I.calldata.size - I.calldata.size + 31) / 32

/-- The loop's byte index after `i` zeroing stores. -/
def hashZeroIndexWord (I : ExecutionEnv) (i : Nat) : UInt256 :=
  UInt256.ofNat (I.calldata.size + 32 * i)

def hashZeroMem (I : ExecutionEnv) : Nat → ByteArray
  | 0 => hashCopiedMem I
  | i + 1 =>
      (⟨0⟩ : UInt256).toByteArray.write 0 (hashZeroMem I i)
        (hashPadPtr I + hashZeroIndexWord I i).toNat 32

def hashZeroAw (I : ExecutionEnv) : Nat → UInt256
  | 0 => hashCopiedAw I
  | i + 1 => UInt256.ofNat (MachineState.M (hashZeroAw I i).toNat
      (hashPadPtr I + hashZeroIndexWord I i).toNat 32)

def hashMarkerAddr (I : ExecutionEnv) : UInt256 :=
  hashPadPtr I + calldataSizeWord I

def hashMarkerMem (I : ExecutionEnv) : ByteArray :=
  (⟨#[0x80]⟩ : ByteArray).write 0
    (hashZeroMem I (hashZeroIterations I)) (hashMarkerAddr I).toNat 1

def hashMarkerAw (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (MachineState.M (hashZeroAw I (hashZeroIterations I)).toNat
    (hashMarkerAddr I).toNat 1)

def hashSwap64Stage8 (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft x ⟨8⟩) ⟨0xff00ff00ff00ff00⟩)
    (UInt256.land (UInt256.shiftRight x ⟨8⟩) ⟨0x00ff00ff00ff00ff⟩)

def hashSwap64Stage16 (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft x ⟨16⟩) ⟨0xffff0000ffff0000⟩)
    (UInt256.land (UInt256.shiftRight x ⟨16⟩) ⟨0x0000ffff0000ffff⟩)

def hashSwap64 (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft (hashSwap64Stage16 (hashSwap64Stage8 x)) ⟨32⟩)
      ⟨0xffffffff00000000⟩)
    (UInt256.land (UInt256.shiftRight (hashSwap64Stage16 (hashSwap64Stage8 x)) ⟨32⟩)
      ⟨0x00000000ffffffff⟩)

def hashBitLengthWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (hashSwap64 (UInt256.shiftLeft (calldataSizeWord I) ⟨3⟩)) ⟨192⟩

private def hashU256Bv (x : UInt256) : BitVec 256 := BitVec.ofNat 256 x.toNat

private theorem hashU256Bv_toNat (x : UInt256) : (hashU256Bv x).toNat = x.toNat := by
  simp only [hashU256Bv, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le x.val.isLt (by decide))

private theorem hashU256Bv_land (a b : UInt256) :
    hashU256Bv (UInt256.land a b) = hashU256Bv a &&& hashU256Bv b := by
  apply BitVec.eq_of_toNat_eq
  simp [hashU256Bv, uland_toNat]

private theorem hashU256Bv_lor (a b : UInt256) :
    hashU256Bv (UInt256.lor a b) = hashU256Bv a ||| hashU256Bv b := by
  apply BitVec.eq_of_toNat_eq
  simp only [hashU256Bv, BitVec.toNat_ofNat, BitVec.toNat_or, u256_lor_toNat]
  have ha : a.toNat < 2 ^ 256 := lt_of_lt_of_le a.val.isLt (by decide)
  have hb : b.toNat < 2 ^ 256 := lt_of_lt_of_le b.val.isLt (by decide)
  rw [show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)

private theorem hashU256Bv_shl (a : UInt256) (n : Nat) (hn : n < 256) :
    hashU256Bv (UInt256.shiftLeft a (UInt256.ofNat n)) = hashU256Bv a <<< n := by
  apply BitVec.eq_of_toNat_eq
  simp only [hashU256Bv, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  have ha : a.toNat < 2 ^ 256 := lt_of_lt_of_le a.val.isLt (by decide)
  rw [ushl_ofNat_toNat a n hn, show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_mod, Nat.mod_eq_of_lt ha]

private theorem hashU256Bv_shr (a : UInt256) (n : Nat) (hn : n < 256) :
    hashU256Bv (UInt256.shiftRight a (UInt256.ofNat n)) = hashU256Bv a >>> n := by
  apply BitVec.eq_of_toNat_eq
  simp only [hashU256Bv, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  have ha : a.toNat < 2 ^ 256 := lt_of_lt_of_le a.val.isLt (by decide)
  rw [ushr_ofNat_toNat a n hn, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) ha)]

private def hashSwapBv8_64 (x : BitVec 64) : BitVec 64 :=
  ((x <<< 8) &&& 0xff00ff00ff00ff00#64) |||
    ((x >>> 8) &&& 0x00ff00ff00ff00ff#64)

private def hashSwapBv16_64 (x : BitVec 64) : BitVec 64 :=
  ((x <<< 16) &&& 0xffff0000ffff0000#64) |||
    ((x >>> 16) &&& 0x0000ffff0000ffff#64)

private def hashSwapBv64_64 (x : BitVec 64) : BitVec 64 :=
  ((hashSwapBv16_64 (hashSwapBv8_64 x) <<< 32) &&& 0xffffffff00000000#64) |||
    ((hashSwapBv16_64 (hashSwapBv8_64 x) >>> 32) &&& 0x00000000ffffffff#64)

private def hashSwapBv8_256 (x : BitVec 256) : BitVec 256 :=
  ((x <<< 8) &&& 0xff00ff00ff00ff00#256) |||
    ((x >>> 8) &&& 0x00ff00ff00ff00ff#256)

private def hashSwapBv16_256 (x : BitVec 256) : BitVec 256 :=
  ((x <<< 16) &&& 0xffff0000ffff0000#256) |||
    ((x >>> 16) &&& 0x0000ffff0000ffff#256)

private def hashSwapBv64_256 (x : BitVec 256) : BitVec 256 :=
  ((hashSwapBv16_256 (hashSwapBv8_256 x) <<< 32) &&& 0xffffffff00000000#256) |||
    ((hashSwapBv16_256 (hashSwapBv8_256 x) >>> 32) &&& 0x00000000ffffffff#256)

private theorem hashU256Bv_hashSwap64Stage8 (x : UInt256) :
    hashU256Bv (hashSwap64Stage8 x) = hashSwapBv8_256 (hashU256Bv x) := by
  have shl8 (a : UInt256) := hashU256Bv_shl a 8 (by decide)
  have shr8 (a : UInt256) := hashU256Bv_shr a 8 (by decide)
  unfold hashSwap64Stage8 hashSwapBv8_256
  rw [hashU256Bv_lor, hashU256Bv_land, hashU256Bv_land]
  rw [show (⟨8⟩ : UInt256) = UInt256.ofNat 8 from rfl, shl8, shr8]
  rw [show hashU256Bv (⟨0xff00ff00ff00ff00⟩ : UInt256) =
      0xff00ff00ff00ff00#256 by native_decide,
    show hashU256Bv (⟨0x00ff00ff00ff00ff⟩ : UInt256) =
      0x00ff00ff00ff00ff#256 by native_decide]

private theorem hashU256Bv_hashSwap64Stage16 (x : UInt256) :
    hashU256Bv (hashSwap64Stage16 x) = hashSwapBv16_256 (hashU256Bv x) := by
  have shl16 (a : UInt256) := hashU256Bv_shl a 16 (by decide)
  have shr16 (a : UInt256) := hashU256Bv_shr a 16 (by decide)
  unfold hashSwap64Stage16 hashSwapBv16_256
  rw [hashU256Bv_lor, hashU256Bv_land, hashU256Bv_land]
  rw [show (⟨16⟩ : UInt256) = UInt256.ofNat 16 from rfl, shl16, shr16]
  rw [show hashU256Bv (⟨0xffff0000ffff0000⟩ : UInt256) =
      0xffff0000ffff0000#256 by native_decide,
    show hashU256Bv (⟨0x0000ffff0000ffff⟩ : UInt256) =
      0x0000ffff0000ffff#256 by native_decide]

private theorem hashU256Bv_hashSwap64 (x : UInt256) :
    hashU256Bv (hashSwap64 x) = hashSwapBv64_256 (hashU256Bv x) := by
  have shl32 (a : UInt256) := hashU256Bv_shl a 32 (by decide)
  have shr32 (a : UInt256) := hashU256Bv_shr a 32 (by decide)
  unfold hashSwap64 hashSwapBv64_256
  rw [hashU256Bv_lor, hashU256Bv_land, hashU256Bv_land]
  rw [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl,
    shl32, shr32, hashU256Bv_hashSwap64Stage16, hashU256Bv_hashSwap64Stage8]
  rw [show hashU256Bv (⟨0xffffffff00000000⟩ : UInt256) =
      0xffffffff00000000#256 by native_decide,
    show hashU256Bv (⟨0x00000000ffffffff⟩ : UInt256) =
      0x00000000ffffffff#256 by native_decide]

private theorem hashSwapBv64_byte64 (x : BitVec 64) (q : Fin 8) :
    ((hashSwapBv64_64 x >>> ((7 - q.val) * 8)) &&& 0xff#64) =
      ((x >>> (q.val * 8)) &&& 0xff#64) := by
  fin_cases q <;>
    simp [hashSwapBv64_64, hashSwapBv16_64, hashSwapBv8_64] <;> bv_decide

private theorem hashSwapBv64_setWidth (x : BitVec 256) :
    (hashSwapBv64_256 x).setWidth 64 = hashSwapBv64_64 (x.setWidth 64) := by
  simp [hashSwapBv64_256, hashSwapBv16_256, hashSwapBv8_256,
    hashSwapBv64_64, hashSwapBv16_64, hashSwapBv8_64]
  bv_decide

private theorem hashSwapBv64_byte256 (x : BitVec 256) (q : Fin 8) :
    (((hashSwapBv64_256 (x <<< 3) <<< 192) >>> ((31 - q.val) * 8)) &&& 0xff#256) =
      (((x <<< 3) >>> (q.val * 8)) &&& 0xff#256) := by
  have h64 :
      (((hashSwapBv64_256 (x <<< 3)).setWidth 64 >>> ((7 - q.val) * 8)) &&&
          0xff#64) =
        ((((x <<< 3).setWidth 64) >>> (q.val * 8)) &&& 0xff#64) := by
    rw [hashSwapBv64_setWidth]
    exact hashSwapBv64_byte64 ((x <<< 3).setWidth 64) q
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hi8 : i < 8
  · have hbit := congrArg (fun z : BitVec 64 => z.getLsbD i) h64
    have hi64 : i < 64 := by omega
    have hi256 : i < 256 := by omega
    have hm64 : (0xff#64).getLsbD i = true := by
      rw [BitVec.getLsbD_ofNat]
      rw [show 255 = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp [hi8, hi64]
    have hm256 : (0xff#256).getLsbD i = true := by
      rw [BitVec.getLsbD_ofNat]
      rw [show 255 = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp [hi8, hi256]
    simp only at hbit
    rw [BitVec.getLsbD_and, hm64, Bool.and_true] at hbit
    rw [BitVec.getLsbD_and, hm256, Bool.and_true]
    fin_cases q <;> interval_cases i <;> simp_all
  · have hpow : 255 < 2 ^ i :=
      lt_of_lt_of_le (by norm_num : 255 < 2 ^ 8)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hmask : (0xff#256).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]
      simp [Nat.testBit_eq_false_of_lt hpow]
    simp [BitVec.getLsbD_and, hmask]

/-- The byte-swap sequence writes byte `q` of the little-endian 64-bit input into the
    corresponding big-endian byte position of the EVM word. -/
theorem hashBitLengthWord_byte (x : UInt256) (q : Nat) (hq : q < 8) :
    UInt256.land
        (UInt256.shiftRight
          (UInt256.shiftLeft (hashSwap64 (UInt256.shiftLeft x ⟨3⟩)) ⟨192⟩)
          (UInt256.ofNat ((31 - q) * 8))) ⟨0xff⟩ =
      UInt256.land
        (UInt256.shiftRight (UInt256.shiftLeft x ⟨3⟩)
          (UInt256.ofNat (q * 8))) ⟨0xff⟩ := by
  have hq256 : q * 8 < 256 := by omega
  have h31q256 : (31 - q) * 8 < 256 := by omega
  have hb :
      hashU256Bv (UInt256.land
        (UInt256.shiftRight
          (UInt256.shiftLeft (hashSwap64 (UInt256.shiftLeft x ⟨3⟩)) ⟨192⟩)
          (UInt256.ofNat ((31 - q) * 8))) ⟨0xff⟩) =
      hashU256Bv (UInt256.land
        (UInt256.shiftRight (UInt256.shiftLeft x ⟨3⟩)
          (UInt256.ofNat (q * 8))) ⟨0xff⟩) := by
    rw [hashU256Bv_land, hashU256Bv_land,
      hashU256Bv_shr _ _ h31q256, hashU256Bv_shr _ _ hq256]
    rw [show (⟨192⟩ : UInt256) = UInt256.ofNat 192 from rfl,
      show (⟨3⟩ : UInt256) = UInt256.ofNat 3 from rfl,
      hashU256Bv_shl _ 192 (by omega), hashU256Bv_shl _ 3 (by omega),
      hashU256Bv_hashSwap64, hashU256Bv_shl _ 3 (by omega)]
    norm_num [hashU256Bv]
    exact hashSwapBv64_byte256 (hashU256Bv x) (⟨q, hq⟩ : Fin 8)
  apply u256_inj
  simpa only [hashU256Bv_toNat] using congrArg BitVec.toNat hb

private theorem hashNatByte_mod64 (n q : Nat) (hq : q < 8) :
    ((n >>> (q * 8)) &&& 255) =
      (((n % 2 ^ 64) >>> (q * 8)) &&& 255) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hi : i < 8
  · rw [Nat.testBit_mod_two_pow]
    simp [show q * 8 + i < 64 by omega]
  · have hpow : 255 < 2 ^ i :=
      lt_of_lt_of_le (by norm_num : 255 < 2 ^ 8)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hpow]
    simp

theorem hashBitLengthByteValue (n q : Nat)
    (hn : n ≤ maxFallbackCalldataSize) (hq : q < 8) :
    (UInt256.land
      (UInt256.shiftRight (UInt256.shiftLeft (UInt256.ofNat n) ⟨3⟩)
        (UInt256.ofNat (q * 8))) ⟨0xff⟩).toNat =
      (Model.bitLength n >>> (q * 8)) &&& 255 := by
  rw [uland_toNat, show (⟨3⟩ : UInt256) = UInt256.ofNat 3 from rfl,
    ushr_ofNat_toNat _ _ (by omega), ushl_ofNat_toNat _ 3 (by omega)]
  rw [ulit_toNat' n (lt_of_le_of_lt hn (by native_decide)),
    show (⟨0xff⟩ : UInt256).toNat = 255 from by decide,
    show UInt256.size = 2 ^ 256 from by decide,
    Nat.mod_eq_of_lt (by unfold maxFallbackCalldataSize at hn; omega),
    Nat.shiftLeft_eq]
  unfold Model.bitLength
  exact hashNatByte_mod64 (n * 2 ^ 3) q hq

def hashLengthAddr (I : ExecutionEnv) : UInt256 :=
  hashNewFreePtr I + UInt256.lnot ⟨7⟩

def hashPaddedMessageMem (I : ExecutionEnv) : ByteArray :=
  (hashBitLengthWord I).toByteArray.write 0
    (hashMarkerMem I) (hashLengthAddr I).toNat 32

def hashPaddedMessageAw (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (MachineState.M (hashMarkerAw I).toNat (hashLengthAddr I).toNat 32)

def hashScratchPtr (I : ExecutionEnv) : UInt256 := hashNewFreePtr I

def hashScratchNewFreePtr (I : ExecutionEnv) : UInt256 :=
  hashScratchPtr I + ⟨832⟩

def hashScratchMem (I : ExecutionEnv) : ByteArray :=
  (hashScratchNewFreePtr I).toByteArray.write 0 (hashPaddedMessageMem I) 64 32

theorem lnot63_toNat : (UInt256.lnot ⟨63⟩).toNat = 2 ^ 256 - 64 := by
  unfold UInt256.lnot
  decide

theorem hashPaddedLengthWord_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPaddedLengthWord I).toNat = Model.paddedLength I.calldata.size := by
  unfold hashPaddedLengthWord calldataSizeWord Model.paddedLength
  rw [uland_toNat, lnot63_toNat, uadd_toNat]
  rw [ulit_toNat' I.calldata.size
    (lt_of_le_of_lt hsmall (by native_decide : maxFallbackCalldataSize < UInt256.size))]
  rw [show (⟨72⟩ : UInt256).toNat = 72 from by decide,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt (by unfold maxFallbackCalldataSize at hsmall; omega)]
  calc
    (I.calldata.size + 72) &&& (2 ^ 256 - 64) =
        64 * ((I.calldata.size + 72) / 64) := by
      simpa using nat_land_mask_pow (I.calldata.size + 72) 6 (by
        unfold maxFallbackCalldataSize at hsmall
        omega) (by decide)
    _ = (I.calldata.size + 72) / 64 * 64 := Nat.mul_comm _ _

theorem hashPaddedLengthWord_stack (I : ExecutionEnv) :
    UInt256.land (UInt256.lnot ⟨63⟩) (calldataSizeWord I + ⟨72⟩) =
      hashPaddedLengthWord I := by
  unfold hashPaddedLengthWord
  exact u256_land_comm _ _

theorem hashPaddedLength_bounds (n : Nat) :
    n + 8 < Model.paddedLength n ∧ Model.paddedLength n ≤ n + 72 := by
  unfold Model.paddedLength
  have hmod := Nat.mod_lt (n + 72) (by decide : 0 < 64)
  have hdecomp := Nat.mod_add_div (n + 72) 64
  omega

theorem hashPaddedLength_pos (n : Nat) : 0 < Model.paddedLength n := by
  have := (hashPaddedLength_bounds n).1
  omega

theorem hashPaddedLength_mod (n : Nat) : Model.paddedLength n % 64 = 0 := by
  unfold Model.paddedLength
  omega

theorem hashZeroIterations_pos (I : ExecutionEnv) : 0 < hashZeroIterations I := by
  unfold hashZeroIterations
  rw [Nat.lt_div_iff_mul_lt (by decide : 0 < 32)]
  have hbounds := hashPaddedLength_bounds I.calldata.size
  omega

theorem hashZeroIterations_le_three (I : ExecutionEnv) : hashZeroIterations I ≤ 3 := by
  unfold hashZeroIterations
  rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
  have hbounds := hashPaddedLength_bounds I.calldata.size
  omega

theorem hashZeroIterations_exit (I : ExecutionEnv) :
    Model.paddedLength I.calldata.size ≤
      I.calldata.size + 32 * hashZeroIterations I := by
  unfold hashZeroIterations
  have hbounds := hashPaddedLength_bounds I.calldata.size
  have hdiv := Nat.mod_add_div
    (Model.paddedLength I.calldata.size - I.calldata.size + 31) 32
  have hmod := Nat.mod_lt
    (Model.paddedLength I.calldata.size - I.calldata.size + 31)
    (by decide : 0 < 32)
  omega

theorem hashZeroIterations_body (I : ExecutionEnv) {i : Nat}
    (hi : i < hashZeroIterations I) :
    I.calldata.size + 32 * i < Model.paddedLength I.calldata.size := by
  unfold hashZeroIterations at hi
  rw [Nat.lt_div_iff_mul_lt (by decide : 0 < 32)] at hi
  have hbounds := hashPaddedLength_bounds I.calldata.size
  omega

theorem hashPadPtr_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPadPtr I).toNat = 160 + 32 * ((I.calldata.size + 31) / 32) := by
  have hmax : I.calldata.size ≤ 18446744073709551615 := by
    unfold maxFallbackCalldataSize at hsmall
    omega
  have hrounded :
      (roundedCalldataSizeWord I).toNat = 32 * ((I.calldata.size + 31) / 32) := by
    unfold roundedCalldataSizeWord calldataSizeWord
    rw [uland_toNat, lnot31_toNat, uadd_toNat]
    rw [ulit_toNat' I.calldata.size (lt_of_le_of_lt hmax (by decide))]
    rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    rw [show UInt256.size = 2 ^ 256 from by decide]
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.and_comm, nat_land_mask _ (by omega)]
  unfold hashPadPtr fallbackFreePtr fallbackAllocationSize
  rw [uadd_toNat, uadd_toNat, hrounded]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem hashPadPtr_after_data (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    160 + I.calldata.size ≤ (hashPadPtr I).toNat := by
  rw [hashPadPtr_toNat I hsmall]
  omega

theorem hashNewFreePtr_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashNewFreePtr I).toNat =
      (hashPadPtr I).toNat + Model.paddedLength I.calldata.size := by
  unfold hashNewFreePtr
  rw [uadd_toNat, hashPaddedLengthWord_toNat I hsmall,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt]
  rw [hashPadPtr_toNat I hsmall]
  have hp := (hashPaddedLength_bounds I.calldata.size).2
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem hashZeroIndexWord_toNat (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) (hi : i ≤ 3) :
    (hashZeroIndexWord I i).toNat = I.calldata.size + 32 * i := by
  unfold hashZeroIndexWord
  exact ulit_toNat' _ (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    unfold maxFallbackCalldataSize at hsmall
    omega)

theorem hashZeroAddress_toNat (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) (hi : i ≤ 3) :
    (hashPadPtr I + hashZeroIndexWord I i).toNat =
      (hashPadPtr I).toNat + I.calldata.size + 32 * i := by
  rw [uadd_toNat, hashZeroIndexWord_toNat I i hsmall hi,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt (by
    rw [hashPadPtr_toNat I hsmall]
    unfold maxFallbackCalldataSize at hsmall
    omega)]
  omega

theorem hashZeroIndexWord_next (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) (hi : i < 3) :
    hashZeroIndexWord I i + ⟨32⟩ = hashZeroIndexWord I (i + 1) := by
  apply u256_inj
  rw [uadd_toNat, hashZeroIndexWord_toNat I i hsmall (by omega),
    hashZeroIndexWord_toNat I (i + 1) hsmall (by omega),
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt (by
    have hpow : 18446744073709551520 < 2 ^ 256 := by norm_num
    unfold maxFallbackCalldataSize at hsmall
    omega)]
  omega

theorem hashMarkerAddr_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashMarkerAddr I).toNat = (hashPadPtr I).toNat + I.calldata.size := by
  unfold hashMarkerAddr calldataSizeWord
  rw [uadd_toNat, ulit_toNat' I.calldata.size (lt_of_le_of_lt hsmall (by
    native_decide)), show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt]
  rw [hashPadPtr_toNat I hsmall]
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem lnot7_toNat : (UInt256.lnot ⟨7⟩).toNat = UInt256.size - 8 := by
  unfold UInt256.lnot
  decide

theorem hashLengthAddr_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashLengthAddr I).toNat =
      (hashPadPtr I).toNat + Model.paddedLength I.calldata.size - 8 := by
  unfold hashLengthAddr
  rw [uadd_toNat, lnot7_toNat, hashNewFreePtr_toNat I hsmall]
  have hptr := hashPadPtr_toNat I hsmall
  have hpos := hashPaddedLength_pos I.calldata.size
  have hupper := (hashPaddedLength_bounds I.calldata.size).2
  have hsum : (hashPadPtr I).toNat + Model.paddedLength I.calldata.size < UInt256.size := by
    rw [hptr, show UInt256.size = 2 ^ 256 from by decide]
    unfold maxFallbackCalldataSize at hsmall
    omega
  have hrest : (hashPadPtr I).toNat + Model.paddedLength I.calldata.size - 8 <
      UInt256.size := by omega
  rw [show (hashPadPtr I).toNat + Model.paddedLength I.calldata.size +
      (UInt256.size - 8) = UInt256.size +
        ((hashPadPtr I).toNat + Model.paddedLength I.calldata.size - 8) by omega]
  rw [Nat.add_mod, Nat.mod_self, zero_add]
  simp [Nat.mod_eq_of_lt hrest]

theorem fallbackAllocMem_size (I : ExecutionEnv) : (fallbackAllocMem I).size = 96 := by
  unfold fallbackAllocMem
  exact toByteArray_write32_size_of_le solcFreePtrMem (fallbackFreePtr I) 64 96 96
    solcFreePtrMem_size (by rw [solcFreePtrMem_size]; omega) (by decide)

theorem fallbackLengthMem_size (I : ExecutionEnv) : (fallbackLengthMem I).size = 160 := by
  unfold fallbackLengthMem
  exact toByteArray_write32_size_of_ge (fallbackAllocMem I) (calldataSizeWord I)
    128 96 160 (fallbackAllocMem_size I) (by omega) (by
      native_decide) (by omega)

theorem fallbackCalldataMem_size (I : ExecutionEnv) :
    (fallbackCalldataMem I).size = 160 + I.calldata.size := by
  unfold fallbackCalldataMem
  by_cases hn : I.calldata.size = 0
  · rw [hn, byteArray_write_len_zero, fallbackLengthMem_size]
  · rw [show 160 = (fallbackLengthMem I).size by rw [fallbackLengthMem_size]]
    exact write_end_size_from I.calldata (fallbackLengthMem I) 0 I.calldata.size hn
      (by omega)

theorem fallbackPaddedMem_size (I : ExecutionEnv) :
    (fallbackPaddedMem I).size = 192 + I.calldata.size := by
  unfold fallbackPaddedMem
  rw [show 160 + I.calldata.size = (fallbackCalldataMem I).size by
    rw [fallbackCalldataMem_size]]
  have h := write_end_size_from (⟨0⟩ : UInt256).toByteArray
    (fallbackCalldataMem I) 0 32 (by decide) (by rw [toByteArray_size])
  calc
    ((⟨0⟩ : UInt256).toByteArray.write 0 (fallbackCalldataMem I)
        (fallbackCalldataMem I).size 32).size =
        (fallbackCalldataMem I).size + 32 := h
    _ = 192 + I.calldata.size := by rw [fallbackCalldataMem_size]; omega

theorem hashAllocatedMem_size (I : ExecutionEnv) :
    (hashAllocatedMem I).size = 192 + I.calldata.size := by
  unfold hashAllocatedMem
  apply toByteArray_write32_size_of_le (fallbackPaddedMem I) (hashNewFreePtr I)
    64 (192 + I.calldata.size) (192 + I.calldata.size)
  · rw [fallbackPaddedMem_size]
  · rw [fallbackPaddedMem_size]
    omega
  · omega

theorem hashAllocatedMem_read64 (I : ExecutionEnv) :
    (hashAllocatedMem I).readWithPadding 64 32 = (hashNewFreePtr I).toByteArray := by
  unfold hashAllocatedMem
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size]) (by
    rw [fallbackPaddedMem_size]
    omega)]
  rw [show 32 = (hashNewFreePtr I).toByteArray.size by rw [toByteArray_size]]
  exact byteArray_extract_self _

theorem fallbackCalldataMem_read_data (I : ExecutionEnv) {start len : Nat}
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hwindow : start + len ≤ I.calldata.size) :
    (fallbackCalldataMem I).readWithPadding (160 + start) len =
      I.calldata.extract start (start + len) := by
  unfold fallbackCalldataMem
  simpa [Nat.zero_add, Nat.add_assoc] using
    write_read_window_from I.calldata (fallbackLengthMem I)
      0 160 I.calldata.size start len
      (by omega) (by omega) (by rw [fallbackLengthMem_size]) hwindow hpos
      hlen64

theorem hashAllocatedMem_read_data (I : ExecutionEnv) {start len : Nat}
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hwindow : start + len ≤ I.calldata.size) :
    (hashAllocatedMem I).readWithPadding (160 + start) len =
      I.calldata.extract start (start + len) := by
  unfold hashAllocatedMem
  rw [write32_read_above_len _ _ 64 (160 + start) len
    (by rw [toByteArray_size])
    (by rw [fallbackPaddedMem_size]; omega)
    (by omega)
    (by rw [fallbackPaddedMem_size]; omega)
    hpos hlen64]
  unfold fallbackPaddedMem
  rw [write32_read_below_len _ _ (160 + I.calldata.size) (160 + start) len
    (by rw [toByteArray_size])
    (by rw [fallbackCalldataMem_size])
    (by omega)
    (by rw [fallbackCalldataMem_size]; omega)
    hpos hlen64]
  exact fallbackCalldataMem_read_data I hpos hlen64 hwindow

theorem hashCopiedMem_read_data (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {start len : Nat}
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hwindow : start + len ≤ I.calldata.size) :
    (hashCopiedMem I).readWithPadding ((hashPadPtr I).toNat + start) len =
      I.calldata.extract start (start + len) := by
  have hsource : 160 + I.calldata.size ≤ (hashAllocatedMem I).size := by
    rw [hashAllocatedMem_size]
    omega
  have hdest : (hashPadPtr I).toNat ≤ (hashAllocatedMem I).size := by
    rw [hashAllocatedMem_size, hashPadPtr_toNat I hsmall]
    omega
  unfold hashCopiedMem
  rw [write_read_window_from (hashAllocatedMem I) (hashAllocatedMem I)
    160 (hashPadPtr I).toNat I.calldata.size start len
    (by omega) hsource hdest hwindow hpos hlen64]
  rw [← readWithPadding_eq_extract' (hashAllocatedMem I) (160 + start) len
    hpos hlen64 (by rw [hashAllocatedMem_size]; omega)]
  exact hashAllocatedMem_read_data I hpos hlen64 hwindow

theorem hashCopiedMem_covers (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPadPtr I).toNat + I.calldata.size ≤ (hashCopiedMem I).size := by
  unfold hashCopiedMem
  by_cases hn : I.calldata.size = 0
  · rw [hn, byteArray_write_len_zero, hashAllocatedMem_size]
    rw [hashPadPtr_toNat I hsmall]
    omega
  · have hsrc : 160 + I.calldata.size ≤ (hashAllocatedMem I).size := by
      rw [hashAllocatedMem_size]
      omega
    have hdest : (hashPadPtr I).toNat ≤ (hashAllocatedMem I).size := by
      rw [hashAllocatedMem_size, hashPadPtr_toNat I hsmall]
      omega
    by_cases hin : (hashPadPtr I).toNat + I.calldata.size ≤
        (hashAllocatedMem I).size
    · rw [write_eq_gen_from _ _ 160 (hashPadPtr I).toNat I.calldata.size
        hn hsrc hin, ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
      omega
    · rw [write_eq_gen_extend_from _ _ 160 (hashPadPtr I).toNat I.calldata.size
        hn hsrc hdest (by omega), ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract]
      omega

theorem hashCopiedMem_read64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashCopiedMem I).readWithPadding 64 32 = (hashNewFreePtr I).toByteArray := by
  unfold hashCopiedMem
  by_cases hn : I.calldata.size = 0
  · rw [hn, byteArray_write_len_zero, hashAllocatedMem_read64]
  · rw [write_read_below_gen_extend_from _ _ 160 (hashPadPtr I).toNat
      I.calldata.size 64 hn (by rw [hashAllocatedMem_size]; omega) (by
        rw [hashAllocatedMem_size, hashPadPtr_toNat I hsmall]
        omega) (by
        rw [hashPadPtr_toNat I hsmall]
        omega)]
    exact hashAllocatedMem_read64 I

theorem hashZeroMem_covers (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ hashZeroIterations I) :
    (hashPadPtr I).toNat + I.calldata.size + 32 * i ≤ (hashZeroMem I i).size := by
  induction i with
  | zero => simpa [hashZeroMem] using hashCopiedMem_covers I hsmall
  | succ i ih =>
      have hi3 : i ≤ 3 := le_trans (by omega) (hashZeroIterations_le_three I)
      have hcover := ih (by omega)
      change _ ≤ ((⟨0⟩ : UInt256).toByteArray.write 0 (hashZeroMem I i)
        (hashPadPtr I + hashZeroIndexWord I i).toNat 32).size
      have hoff : (hashPadPtr I + hashZeroIndexWord I i).toNat ≤
          (hashZeroMem I i).size := by
        rw [hashZeroAddress_toNat I i hsmall hi3]
        exact hcover
      have hgrow := toByteArray_write_size_ge_off_add32 (⟨0⟩ : UInt256)
        (hashZeroMem I i) (hashPadPtr I + hashZeroIndexWord I i).toNat
        (by simp [Nat.sub_eq_zero_of_le hoff])
      calc
        (hashPadPtr I).toNat + I.calldata.size + 32 * (i + 1) =
            (hashPadPtr I + hashZeroIndexWord I i).toNat + 32 := by
          rw [hashZeroAddress_toNat I i hsmall hi3]
          omega
        _ ≤ ((⟨0⟩ : UInt256).toByteArray.write 0 (hashZeroMem I i)
            (hashPadPtr I + hashZeroIndexWord I i).toNat 32).size := hgrow

theorem hashZeroMem_read64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ hashZeroIterations I) :
    (hashZeroMem I i).readWithPadding 64 32 = (hashNewFreePtr I).toByteArray := by
  induction i with
  | zero => simpa [hashZeroMem] using hashCopiedMem_read64 I hsmall
  | succ i ih =>
      have hiPrev : i ≤ hashZeroIterations I := by omega
      have hi3 : i ≤ 3 := le_trans hiPrev (hashZeroIterations_le_three I)
      rw [hashZeroMem]
      rw [toByteArray_write_read_below_of_gap (⟨0⟩ : UInt256)
        (hashZeroMem I i) (hashPadPtr I + hashZeroIndexWord I i).toNat 64
        (by
          have hc := hashZeroMem_covers I hsmall hiPrev
          rw [hashPadPtr_toNat I hsmall] at hc
          omega)
        (by
          rw [hashZeroAddress_toNat I i hsmall hi3,
            hashPadPtr_toNat I hsmall]
          omega)
        (by
          have hc := hashZeroMem_covers I hsmall hiPrev
          have hoff : (hashPadPtr I + hashZeroIndexWord I i).toNat ≤
              (hashZeroMem I i).size := by
            rw [hashZeroAddress_toNat I i hsmall hi3]
            exact hc
          simp [Nat.sub_eq_zero_of_le hoff])]
      exact ih hiPrev

theorem hashZeroMem_read_data (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i start len : Nat}
    (hi : i ≤ hashZeroIterations I) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hwindow : start + len ≤ I.calldata.size) :
    (hashZeroMem I i).readWithPadding ((hashPadPtr I).toNat + start) len =
      I.calldata.extract start (start + len) := by
  induction i with
  | zero =>
      simpa [hashZeroMem] using
        hashCopiedMem_read_data I hsmall hpos hlen64 hwindow
  | succ i ih =>
      have hiPrev : i ≤ hashZeroIterations I := by omega
      have hi3 : i ≤ 3 := le_trans hiPrev (hashZeroIterations_le_three I)
      have hcover := hashZeroMem_covers I hsmall hiPrev
      have hdest : (hashPadPtr I + hashZeroIndexWord I i).toNat ≤
          (hashZeroMem I i).size := by
        rw [hashZeroAddress_toNat I i hsmall hi3]
        exact hcover
      rw [hashZeroMem]
      rw [write32_read_below_len _ _
        (hashPadPtr I + hashZeroIndexWord I i).toNat
        ((hashPadPtr I).toNat + start) len
        (by rw [toByteArray_size]) hdest
        (by rw [hashZeroAddress_toNat I i hsmall hi3]; omega)
        (by omega) hpos hlen64]
      exact ih hiPrev

theorem hashZeroMem_read_zero_byte (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i q : Nat}
    (hi : i ≤ hashZeroIterations I) (hq : q < 32 * i) :
    (hashZeroMem I i).readWithPadding
        ((hashPadPtr I).toNat + I.calldata.size + q) 1 =
      ⟨#[0]⟩ := by
  induction i with
  | zero => omega
  | succ i ih =>
      have hiPrev : i ≤ hashZeroIterations I := by omega
      have hi3 : i ≤ 3 := le_trans hiPrev (hashZeroIterations_le_three I)
      have hcover := hashZeroMem_covers I hsmall hiPrev
      have hdest : (hashPadPtr I + hashZeroIndexWord I i).toNat ≤
          (hashZeroMem I i).size := by
        rw [hashZeroAddress_toNat I i hsmall hi3]
        exact hcover
      rw [hashZeroMem]
      by_cases hold : q < 32 * i
      · rw [write32_read_below_len _ _
          (hashPadPtr I + hashZeroIndexWord I i).toNat
          ((hashPadPtr I).toNat + I.calldata.size + q) 1
          (by rw [toByteArray_size]) hdest
          (by rw [hashZeroAddress_toNat I i hsmall hi3]; omega)
          (by omega) (by omega) (by omega)]
        exact ih hiPrev hold
      · have hstart : q - 32 * i + 1 ≤ 32 := by omega
        have haddr :
            (hashPadPtr I + hashZeroIndexWord I i).toNat + (q - 32 * i) =
              (hashPadPtr I).toNat + I.calldata.size + q := by
          rw [hashZeroAddress_toNat I i hsmall hi3]
          omega
        rw [← haddr]
        rw [toByteArray_write_read_window_of_gap (⟨0⟩ : UInt256)
          (hashZeroMem I i) (hashPadPtr I + hashZeroIndexWord I i).toNat
          (q - 32 * i) 1 hstart (by omega) (by omega)
          (by simp [Nat.sub_eq_zero_of_le hdest])]
        rw [zero_toByteArray_eq_zeroes32,
          zeroes_extract_window 32 (q - 32 * i) 1 hstart]
        native_decide

theorem hashMarkerMem_read_data (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {start len : Nat}
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hwindow : start + len ≤ I.calldata.size) :
    (hashMarkerMem I).readWithPadding ((hashPadPtr I).toNat + start) len =
      I.calldata.extract start (start + len) := by
  have hcover := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hiterations : 0 < hashZeroIterations I := hashZeroIterations_pos I
  have hdest : (hashMarkerAddr I).toNat + 1 ≤
      (hashZeroMem I (hashZeroIterations I)).size := by
    rw [hashMarkerAddr_toNat I hsmall]
    omega
  unfold hashMarkerMem
  rw [write_read_below_len_from (⟨#[0x80]⟩ : ByteArray)
    (hashZeroMem I (hashZeroIterations I)) 0 (hashMarkerAddr I).toNat 1
    ((hashPadPtr I).toNat + start) len
    (by decide) (by decide) hdest
    (by rw [hashMarkerAddr_toNat I hsmall]; omega) hpos hlen64]
  exact hashZeroMem_read_data I hsmall (le_refl _) hpos hlen64 hwindow

theorem hashMarkerMem_size (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashMarkerMem I).size = (hashZeroMem I (hashZeroIterations I)).size := by
  have hc := hashZeroMem_covers I hsmall (le_refl (hashZeroIterations I))
  have hq := hashZeroIterations_pos I
  have hin : (hashMarkerAddr I).toNat + 1 ≤
      (hashZeroMem I (hashZeroIterations I)).size := by
    rw [hashMarkerAddr_toNat I hsmall]
    omega
  unfold hashMarkerMem
  exact write_size_of_inbounds_from (⟨#[0x80]⟩ : ByteArray)
    (hashZeroMem I (hashZeroIterations I)) 0 (hashMarkerAddr I).toNat 1
    (by decide) (by decide) hin

theorem hashMarkerMem_read_marker (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashMarkerMem I).readWithPadding (hashMarkerAddr I).toNat 1 = ⟨#[0x80]⟩ := by
  have hcover := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hdest : (hashMarkerAddr I).toNat ≤
      (hashZeroMem I (hashZeroIterations I)).size := by
    rw [hashMarkerAddr_toNat I hsmall]
    exact le_trans (by omega) hcover
  unfold hashMarkerMem
  simpa using write_read_window_from (⟨#[0x80]⟩ : ByteArray)
    (hashZeroMem I (hashZeroIterations I)) 0 (hashMarkerAddr I).toNat 1 0 1
    (by decide) (by decide) hdest (by decide) (by decide) (by decide)

theorem hashMarkerMem_read_zero_byte (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {p : Nat}
    (hnp : I.calldata.size < p)
    (hpadded : p < Model.paddedLength I.calldata.size) :
    (hashMarkerMem I).readWithPadding ((hashPadPtr I).toNat + p) 1 = ⟨#[0]⟩ := by
  have hiterations : 0 < hashZeroIterations I := hashZeroIterations_pos I
  have hcover := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hfilled := hashZeroIterations_exit I
  have hdest : (hashMarkerAddr I).toNat + 1 ≤
      (hashZeroMem I (hashZeroIterations I)).size := by
    rw [hashMarkerAddr_toNat I hsmall]
    omega
  have hread : (hashPadPtr I).toNat + p + 1 ≤
      (hashZeroMem I (hashZeroIterations I)).size := by
    omega
  unfold hashMarkerMem
  rw [write_read_above_len_from (⟨#[0x80]⟩ : ByteArray)
    (hashZeroMem I (hashZeroIterations I)) 0 (hashMarkerAddr I).toNat 1
    ((hashPadPtr I).toNat + p) 1
    (by decide) (by decide) hdest
    (by rw [hashMarkerAddr_toNat I hsmall]; omega)
    hread (by decide) (by decide)]
  have hq : p - I.calldata.size < 32 * hashZeroIterations I := by omega
  simpa [show I.calldata.size + (p - I.calldata.size) = p by omega,
    Nat.add_assoc] using
    hashZeroMem_read_zero_byte I hsmall (i := hashZeroIterations I) (le_refl _) hq

theorem hashPaddedMessageMem_read_data (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {start len : Nat}
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hwindow : start + len ≤ I.calldata.size) :
    (hashPaddedMessageMem I).readWithPadding ((hashPadPtr I).toNat + start) len =
      I.calldata.extract start (start + len) := by
  have hzero := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hfilled := hashZeroIterations_exit I
  have hmarkerSize := hashMarkerMem_size I hsmall
  have hdest : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
    rw [hashLengthAddr_toNat I hsmall, hmarkerSize]
    exact le_trans (by
      have := hashZeroIterations_exit I
      omega) hzero
  unfold hashPaddedMessageMem
  rw [write32_read_below_len _ _ (hashLengthAddr I).toNat
    ((hashPadPtr I).toNat + start) len
    (by rw [toByteArray_size]) hdest
    (by
      rw [hashLengthAddr_toNat I hsmall]
      have := (hashPaddedLength_bounds I.calldata.size).1
      omega)
    (by rw [hmarkerSize]; omega) hpos hlen64]
  exact hashMarkerMem_read_data I hsmall hpos hlen64 hwindow

theorem hashPaddedMessageMem_read_marker (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPaddedMessageMem I).readWithPadding (hashMarkerAddr I).toNat 1 = ⟨#[0x80]⟩ := by
  have hzero := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hiterations := hashZeroIterations_pos I
  have hmarkerSize := hashMarkerMem_size I hsmall
  have hdest : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
    rw [hashLengthAddr_toNat I hsmall, hmarkerSize]
    exact le_trans (by
      have := hashZeroIterations_exit I
      omega) hzero
  unfold hashPaddedMessageMem
  rw [write32_read_below_len _ _ (hashLengthAddr I).toNat
    (hashMarkerAddr I).toNat 1
    (by rw [toByteArray_size]) hdest
    (by
      rw [hashLengthAddr_toNat I hsmall, hashMarkerAddr_toNat I hsmall]
      have := (hashPaddedLength_bounds I.calldata.size).1
      omega)
    (by rw [hmarkerSize, hashMarkerAddr_toNat I hsmall]; omega)
    (by decide) (by decide)]
  exact hashMarkerMem_read_marker I hsmall

theorem hashPaddedMessageMem_read_zero_byte (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {p : Nat}
    (hnp : I.calldata.size < p)
    (hlength : p < Model.paddedLength I.calldata.size - 8) :
    (hashPaddedMessageMem I).readWithPadding ((hashPadPtr I).toNat + p) 1 = ⟨#[0]⟩ := by
  have hzero := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hfilled := hashZeroIterations_exit I
  have hmarkerSize := hashMarkerMem_size I hsmall
  have hdest : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
    rw [hashLengthAddr_toNat I hsmall, hmarkerSize]
    exact le_trans (by
      have := hashZeroIterations_exit I
      omega) hzero
  unfold hashPaddedMessageMem
  rw [write32_read_below_len _ _ (hashLengthAddr I).toNat
    ((hashPadPtr I).toNat + p) 1
    (by rw [toByteArray_size]) hdest
    (by rw [hashLengthAddr_toNat I hsmall]; omega)
    (by rw [hmarkerSize]; omega) (by decide) (by decide)]
  exact hashMarkerMem_read_zero_byte I hsmall hnp (by omega)

theorem hashPaddedMessageMem_read_length_byte (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {q : Nat} (hq : q < 8) :
    (hashPaddedMessageMem I).readWithPadding
        ((hashPadPtr I).toNat + Model.paddedLength I.calldata.size - 8 + q) 1 =
      ⟨#[UInt8.ofNat ((Model.bitLength I.calldata.size >>> (q * 8)) &&& 255)]⟩ := by
  have hzero := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hmarkerSize := hashMarkerMem_size I hsmall
  have hdest : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
    rw [hashLengthAddr_toNat I hsmall, hmarkerSize]
    exact le_trans (by
      have := hashZeroIterations_exit I
      omega) hzero
  have haddr :
      (hashPadPtr I).toNat + Model.paddedLength I.calldata.size - 8 + q =
        (hashLengthAddr I).toNat + q := by
    rw [hashLengthAddr_toNat I hsmall]
  rw [haddr]
  unfold hashPaddedMessageMem
  rw [toByteArray_write_read_window_of_gap
    (hashBitLengthWord I) (hashMarkerMem I) (hashLengthAddr I).toNat q 1
    (by omega) (by decide) (by decide)
    (by simp [Nat.sub_eq_zero_of_le hdest])]
  rw [toByteArray_extract_one (hashBitLengthWord I) q (by omega)]
  congr 3
  rw [← UInt8.toNat_inj]
  have hb := congrArg UInt256.toNat
    (hashBitLengthWord_byte (calldataSizeWord I) q hq)
  unfold hashBitLengthWord at hb
  rw [hashBitLengthByteValue I.calldata.size q hsmall hq] at hb
  rw [uland_toNat, show (⟨0xff⟩ : UInt256).toNat = 255 from by decide] at hb
  rw [show UInt256.shiftLeft
      (hashSwap64 (UInt256.shiftLeft (calldataSizeWord I) ⟨3⟩)) ⟨192⟩ =
      hashBitLengthWord I from rfl] at hb
  rw [ushr_ofNat_toNat _ _ (by omega)] at hb
  have hrlt : (Model.bitLength I.calldata.size >>> (q * 8)) &&& 255 < 256 :=
    lt_of_le_of_lt (nat_land_le_right _ 255) (by decide)
  calc
    (hashBitLengthWord I).toNat >>> ((31 - q) * 8) % 256 =
        (hashBitLengthWord I).toNat >>> ((31 - q) * 8) &&& 255 := by
      simpa using (nat_land_mask_eq_mod
        ((hashBitLengthWord I).toNat >>> ((31 - q) * 8)) 8).symm
    _ = (Model.bitLength I.calldata.size >>> (q * 8)) &&& 255 := hb
    _ = ((Model.bitLength I.calldata.size >>> (q * 8)) &&& 255) % 256 :=
      (Nat.mod_eq_of_lt hrlt).symm

theorem hashPaddedMessageMem_read_padded_byte (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {p : Nat}
    (hp : p < Model.paddedLength I.calldata.size) :
    (hashPaddedMessageMem I).readWithPadding ((hashPadPtr I).toNat + p) 1 =
      ⟨#[UInt8.ofNat (Model.paddedByte I.calldata p)]⟩ := by
  unfold Model.paddedByte
  dsimp only
  by_cases hdata : p < I.calldata.size
  · rw [dif_pos hdata]
    rw [hashPaddedMessageMem_read_data I hsmall (start := p) (len := 1)
      (by decide) (by decide) (by omega)]
    rw [byteArray_extract_one I.calldata p hdata]
    congr 3
    exact UInt8.ofNat_toNat.symm
  · rw [dif_neg hdata]
    by_cases hmarker : p = I.calldata.size
    · rw [if_pos hmarker]
      subst p
      rw [show (hashPadPtr I).toNat + I.calldata.size =
          (hashMarkerAddr I).toNat by rw [hashMarkerAddr_toNat I hsmall]]
      rw [hashPaddedMessageMem_read_marker I hsmall]
      congr 3
    · rw [if_neg hmarker]
      by_cases hlength : Model.paddedLength I.calldata.size - 8 ≤ p
      · rw [if_pos hlength]
        let q := p - (Model.paddedLength I.calldata.size - 8)
        have hq : q < 8 := by dsimp [q]; omega
        have hpq :
            (hashPadPtr I).toNat + p =
              (hashPadPtr I).toNat + Model.paddedLength I.calldata.size - 8 + q := by
          dsimp [q]
          rw [Nat.add_sub_assoc (by
            have := (hashPaddedLength_bounds I.calldata.size).1
            omega)]
          omega
        rw [hpq, hashPaddedMessageMem_read_length_byte I hsmall hq]
      · rw [if_neg hlength]
        have hnp : I.calldata.size < p := by omega
        rw [hashPaddedMessageMem_read_zero_byte I hsmall hnp (by omega)]
        congr 3

theorem hashScratchMem_read_padded_byte (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {p : Nat}
    (hp : p < Model.paddedLength I.calldata.size) :
    (hashScratchMem I).readWithPadding ((hashPadPtr I).toNat + p) 1 =
      ⟨#[UInt8.ofNat (Model.paddedByte I.calldata p)]⟩ := by
  have hzero := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hmarkerSize := hashMarkerMem_size I hsmall
  have hdest : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
    rw [hashLengthAddr_toNat I hsmall, hmarkerSize]
    exact le_trans (by
      have := hashZeroIterations_exit I
      omega) hzero
  have hbase : (hashLengthAddr I).toNat + 32 ≤ (hashPaddedMessageMem I).size := by
    unfold hashPaddedMessageMem
    exact toByteArray_write_size_ge_off_add32 _ _ _
      (by simp [Nat.sub_eq_zero_of_le hdest])
  unfold hashScratchMem
  rw [write32_read_above_len _ _ 64 ((hashPadPtr I).toNat + p) 1
    (by rw [toByteArray_size])
    (by
      rw [hashLengthAddr_toNat I hsmall, hashPadPtr_toNat I hsmall] at hbase
      have hplen := hashPaddedLength_pos I.calldata.size
      omega)
    (by rw [hashPadPtr_toNat I hsmall]; omega)
    (by
      rw [hashLengthAddr_toNat I hsmall] at hbase
      omega)
    (by decide) (by decide)]
  exact hashPaddedMessageMem_read_padded_byte I hsmall hp

/-- The cursor entering the compression loop retains the complete padded message. -/
theorem hashScratchMem_covers_message (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPadPtr I).toNat + Model.paddedLength I.calldata.size ≤
      (hashScratchMem I).size := by
  have hzero := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hmarkerSize := hashMarkerMem_size I hsmall
  have hdest : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
    rw [hashLengthAddr_toNat I hsmall, hmarkerSize]
    exact le_trans (by
      have := hashZeroIterations_exit I
      omega) hzero
  have hbase : (hashLengthAddr I).toNat + 32 ≤
      (hashPaddedMessageMem I).size := by
    unfold hashPaddedMessageMem
    exact toByteArray_write_size_ge_off_add32 _ _ _
      (by simp [Nat.sub_eq_zero_of_le hdest])
  have hbase96 : 96 ≤ (hashPaddedMessageMem I).size := by
    rw [hashLengthAddr_toNat I hsmall, hashPadPtr_toNat I hsmall] at hbase
    have hp := hashPaddedLength_pos I.calldata.size
    omega
  have hsize : (hashScratchMem I).size = (hashPaddedMessageMem I).size := by
    unfold hashScratchMem
    exact toByteArray_write32_size_of_le (hashPaddedMessageMem I)
      (hashScratchNewFreePtr I) 64 (hashPaddedMessageMem I).size
      (hashPaddedMessageMem I).size rfl (by omega) (by omega)
  rw [hsize]
  rw [hashLengthAddr_toNat I hsmall] at hbase
  omega

theorem hashPaddedMessageMem_read64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPaddedMessageMem I).readWithPadding 64 32 =
      (hashNewFreePtr I).toByteArray := by
  have hz := hashZeroMem_read64 I hsmall
    (le_refl (hashZeroIterations I))
  have hc := hashZeroMem_covers I hsmall
    (le_refl (hashZeroIterations I))
  have hmarker : (hashMarkerMem I).readWithPadding 64 32 =
      (hashNewFreePtr I).toByteArray := by
    unfold hashMarkerMem
    rw [write_read_below_gen_extend (⟨#[0x80]⟩ : ByteArray)
      (hashZeroMem I (hashZeroIterations I)) (hashMarkerAddr I).toNat 1 64
      (by decide) (by decide) (by
        rw [hashMarkerAddr_toNat I hsmall]
        exact le_trans (by omega) hc) (by
          rw [hashMarkerAddr_toNat I hsmall, hashPadPtr_toNat I hsmall]
          omega)]
    exact hz
  unfold hashPaddedMessageMem
  rw [toByteArray_write_read_below_of_gap (hashBitLengthWord I) (hashMarkerMem I)
    (hashLengthAddr I).toNat 64]
  · exact hmarker
  · rw [hashMarkerMem_size I hsmall]
    have hc' := hc
    rw [hashPadPtr_toNat I hsmall] at hc'
    omega
  · rw [hashLengthAddr_toNat I hsmall, hashPadPtr_toNat I hsmall]
    have hp := hashPaddedLength_pos I.calldata.size
    omega
  · have hlenle : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
      rw [hashMarkerMem_size I hsmall, hashLengthAddr_toNat I hsmall]
      have he := hashZeroIterations_exit I
      omega
    simp [Nat.sub_eq_zero_of_le hlenle]

theorem fallbackPaddedMem_read128 (I : ExecutionEnv) :
    (fallbackPaddedMem I).readWithPadding 128 32 =
      (calldataSizeWord I).toByteArray := by
  unfold fallbackPaddedMem
  rw [write32_read_below _ _ (160 + I.calldata.size) 128
    (by rw [toByteArray_size])
    (by rw [fallbackCalldataMem_size]) (by omega)]
  unfold fallbackCalldataMem
  have hlength :
      (fallbackLengthMem I).readWithPadding 128 32 =
        (calldataSizeWord I).toByteArray := by
    unfold fallbackLengthMem
    exact toByteArray_write_read_back_of_gap (calldataSizeWord I) (fallbackAllocMem I) 128
      (by rw [fallbackAllocMem_size]; native_decide)
  by_cases hn : I.calldata.size = 0
  · rw [hn, byteArray_write_len_zero, hlength]
  · rw [write_read_below_gen_extend I.calldata (fallbackLengthMem I) 160
      I.calldata.size 128 hn (by omega)
      (by rw [fallbackLengthMem_size]) (by omega), hlength]

theorem fallbackPaddedMem_mload128 (I : ExecutionEnv) :
    UInt256.ofNat
      (fromByteArrayBigEndian ((fallbackPaddedMem I).readWithPadding 128 32)) =
      calldataSizeWord I := by
  rw [fallbackPaddedMem_read128, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat _

theorem fallbackPaddedMem_read64 (I : ExecutionEnv) :
    (fallbackPaddedMem I).readWithPadding 64 32 =
      (fallbackFreePtr I).toByteArray := by
  unfold fallbackPaddedMem
  rw [write32_read_below _ _ (160 + I.calldata.size) 64
    (by rw [toByteArray_size])
    (by rw [fallbackCalldataMem_size]) (by omega)]
  unfold fallbackCalldataMem
  have hlength :
      (fallbackLengthMem I).readWithPadding 64 32 =
        (fallbackFreePtr I).toByteArray := by
    unfold fallbackLengthMem
    rw [toByteArray_write_read_below_of_gap (calldataSizeWord I) (fallbackAllocMem I)
      128 64 (by rw [fallbackAllocMem_size]) (by omega)
      (by rw [fallbackAllocMem_size]; native_decide)]
    unfold fallbackAllocMem
    exact toByteArray_write32_read_back solcFreePtrMem (fallbackFreePtr I) 64
      (by rw [solcFreePtrMem_size]; omega)
  by_cases hn : I.calldata.size = 0
  · rw [hn, byteArray_write_len_zero, hlength]
  · rw [write_read_below_gen_extend I.calldata (fallbackLengthMem I) 160
      I.calldata.size 64 hn (by omega)
      (by rw [fallbackLengthMem_size]) (by omega), hlength]

theorem fallbackPaddedMem_mload64 (I : ExecutionEnv) :
    UInt256.ofNat
      (fromByteArrayBigEndian ((fallbackPaddedMem I).readWithPadding 64 32)) =
      fallbackFreePtr I := by
  rw [fallbackPaddedMem_read64, fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat _

theorem fallbackPaddedAw_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (fallbackPaddedAw I).toNat = (I.calldata.size + 223) / 32 := by
  unfold fallbackPaddedAw fallbackCopyAw
  rw [show (UInt256.ofNat 5).toNat = 5 from by decide]
  have hcopyBound : MachineState.M 5 160 I.calldata.size < UInt256.size := by
    unfold maxFallbackCalldataSize at hsmall
    unfold MachineState.M
    rw [show UInt256.size = 2 ^ 256 from by decide]
    split <;> simp_all <;> omega
  rw [ulit_toNat' _ hcopyBound]
  have houterBound :
      MachineState.M (MachineState.M 5 160 I.calldata.size)
        (160 + I.calldata.size) 32 < UInt256.size := by
    unfold maxFallbackCalldataSize at hsmall
    unfold MachineState.M
    rw [show UInt256.size = 2 ^ 256 from by decide]
    simp only [OfNat.ofNat]
    split <;> simp_all <;> omega
  rw [ulit_toNat' _ houterBound]
  have hfive : 5 ≤ (I.calldata.size + 223) / 32 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 32)]
    omega
  have hprev :
      (I.calldata.size + 191) / 32 ≤ (I.calldata.size + 223) / 32 :=
    Nat.div_le_div_right (by omega)
  have hinnerEq :
      (160 + I.calldata.size + 31) / 32 = (I.calldata.size + 191) / 32 := by
    congr 1
    omega
  have houterEq :
      (160 + I.calldata.size + 32 + 31) / 32 =
        (I.calldata.size + 223) / 32 := by
    congr 1
    omega
  unfold MachineState.M
  simp only [OfNat.ofNat]
  rw [houterEq]
  split
  · rename_i hz
    rw [hz]
    norm_num
  · rename_i hn
    rw [hinnerEq]
    have hfivePrev : 5 ≤ (I.calldata.size + 191) / 32 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 32)]
      omega
    rw [max_eq_right hfivePrev, max_eq_right hprev]

theorem fallbackPaddedAw_ge_six (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    6 ≤ (fallbackPaddedAw I).toNat := by
  rw [fallbackPaddedAw_toNat I hsmall]
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 32)]
  omega

theorem fallbackPaddedAw_mul32_toNat (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (fallbackPaddedAw I * ⟨32⟩).toNat = 32 * (fallbackPaddedAw I).toNat := by
  rw [umul_toNat]
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    omega
  · rw [fallbackPaddedAw_toNat I hsmall,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      show UInt256.size = 2 ^ 256 from by decide]
    unfold maxFallbackCalldataSize at hsmall
    omega

theorem fallbackPaddedAw_covers128 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ¬ (⟨128⟩ : UInt256) ≥ fallbackPaddedAw I * ⟨32⟩ := by
  intro h
  change (fallbackPaddedAw I * ⟨32⟩).toNat ≤ 128 at h
  rw [fallbackPaddedAw_mul32_toNat I hsmall] at h
  have haw := fallbackPaddedAw_ge_six I hsmall
  omega

theorem fallbackPaddedAw_mload128 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    UInt256.ofNat (MachineState.M (fallbackPaddedAw I).toNat 128 32) =
      fallbackPaddedAw I := by
  change UInt256.ofNat (max (fallbackPaddedAw I).toNat 5) = fallbackPaddedAw I
  rw [max_eq_left (by have := fallbackPaddedAw_ge_six I hsmall; norm_num; omega)]
  exact u256_ofNat_toNat _

theorem fallbackPaddedMload128Value (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (if (⟨128⟩ : UInt256).toNat ≥ (fallbackPaddedMem I).size ∨
          (⟨128⟩ : UInt256) ≥ fallbackPaddedAw I * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((fallbackPaddedMem I).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      calldataSizeWord I := by
  rw [if_neg]
  · simpa using fallbackPaddedMem_mload128 I
  · push_neg
    constructor
    · rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        fallbackPaddedMem_size]
      omega
    · exact fallbackPaddedAw_covers128 I hsmall

theorem fallbackPaddedMload64Value (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (if (⟨64⟩ : UInt256).toNat ≥ (fallbackPaddedMem I).size ∨
          (⟨64⟩ : UInt256) ≥ fallbackPaddedAw I * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((fallbackPaddedMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      fallbackFreePtr I := by
  rw [if_neg]
  · simpa using fallbackPaddedMem_mload64 I
  · push_neg
    constructor
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        fallbackPaddedMem_size]
      omega
    · intro h
      apply fallbackPaddedAw_covers128 I hsmall
      exact le_trans h (by decide)

theorem fallbackPaddedAw_mload64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    UInt256.ofNat (MachineState.M (fallbackPaddedAw I).toNat 64 32) =
      fallbackPaddedAw I := by
  change UInt256.ofNat (max (fallbackPaddedAw I).toNat 3) = fallbackPaddedAw I
  rw [max_eq_left (by have := fallbackPaddedAw_ge_six I hsmall; norm_num; omega)]
  exact u256_ofNat_toNat _

theorem fallbackPaddedMload128Cost (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) (s : State)
    (haw : s.machineState.activeWords = fallbackPaddedAw I)
    (hstk : s.machineState.stack = (⟨128⟩ : UInt256) :: t) :
    memoryExpansionCost s .MLOAD = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    haw, fallbackPaddedAw_mload128 I hsmall]
  omega

theorem fallbackPaddedMload64Cost (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) (s : State)
    (haw : s.machineState.activeWords = fallbackPaddedAw I)
    (hstk : s.machineState.stack = (⟨64⟩ : UInt256) :: t) :
    memoryExpansionCost s .MLOAD = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk]
  rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
    haw, fallbackPaddedAw_mload64 I hsmall]
  omega

private theorem machineM_ofNat_lt_pow64 (aw : UInt256) (off len : Nat)
    (haw : aw.toNat < 2 ^ 64) (hbound : off + len + 31 < 32 * (2 ^ 64)) :
    (UInt256.ofNat (MachineState.M aw.toNat off len)).toNat < 2 ^ 64 := by
  have hm : MachineState.M aw.toNat off len < 2 ^ 64 := by
    cases len with
    | zero => simpa [MachineState.M] using haw
    | succ len =>
        simp only [MachineState.M]
        rw [max_lt_iff]
        refine ⟨haw, ?_⟩
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
        omega
  rw [ulit_toNat' _ (lt_trans hm (by
    rw [show UInt256.size = 2 ^ 256 from by decide]
    norm_num))]
  exact hm

theorem hashCopiedAw_ge_six (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    6 ≤ (hashCopiedAw I).toNat := by
  apply le_trans (fallbackPaddedAw_ge_six I hsmall)
  unfold hashCopiedAw
  apply machineM_ofNat_ge
  rw [max_eq_left (by rw [hashPadPtr_toNat I hsmall]; omega),
    hashPadPtr_toNat I hsmall, show UInt256.size = 2 ^ 256 from by decide]
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem hashCopiedAw_lt_pow64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashCopiedAw I).toNat < 2 ^ 64 := by
  unfold hashCopiedAw
  apply machineM_ofNat_lt_pow64
  · rw [fallbackPaddedAw_toNat I hsmall]
    unfold maxFallbackCalldataSize at hsmall
    omega
  · rw [max_eq_left (by rw [hashPadPtr_toNat I hsmall]; omega),
      hashPadPtr_toNat I hsmall]
    unfold maxFallbackCalldataSize at hsmall
    omega

theorem hashZeroAw_ge_six (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ hashZeroIterations I) : 6 ≤ (hashZeroAw I i).toNat := by
  induction i with
  | zero => simpa [hashZeroAw] using hashCopiedAw_ge_six I hsmall
  | succ i ih =>
      have hiPrev : i ≤ hashZeroIterations I := by omega
      have hi3 : i ≤ 3 := le_trans hiPrev (hashZeroIterations_le_three I)
      apply le_trans (ih hiPrev)
      simp only [hashZeroAw]
      apply machineM_ofNat_ge
      rw [hashZeroAddress_toNat I i hsmall hi3,
        hashPadPtr_toNat I hsmall, show UInt256.size = 2 ^ 256 from by decide]
      unfold maxFallbackCalldataSize at hsmall
      omega

theorem hashZeroAw_lt_pow64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ hashZeroIterations I) : (hashZeroAw I i).toNat < 2 ^ 64 := by
  induction i with
  | zero => simpa [hashZeroAw] using hashCopiedAw_lt_pow64 I hsmall
  | succ i ih =>
      have hiPrev : i ≤ hashZeroIterations I := by omega
      have hi3 : i ≤ 3 := le_trans hiPrev (hashZeroIterations_le_three I)
      simp only [hashZeroAw]
      apply machineM_ofNat_lt_pow64 _ _ _ (ih hiPrev)
      rw [hashZeroAddress_toNat I i hsmall hi3, hashPadPtr_toNat I hsmall]
      unfold maxFallbackCalldataSize at hsmall
      omega

theorem hashPaddedMessageAw_ge_six (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    6 ≤ (hashPaddedMessageAw I).toNat := by
  have hmarker : (hashZeroAw I (hashZeroIterations I)).toNat ≤
      (hashMarkerAw I).toNat := by
    unfold hashMarkerAw
    apply machineM_ofNat_ge
    rw [hashMarkerAddr_toNat I hsmall, hashPadPtr_toNat I hsmall,
      show UInt256.size = 2 ^ 256 from by decide]
    unfold maxFallbackCalldataSize at hsmall
    omega
  have hlength : (hashMarkerAw I).toNat ≤ (hashPaddedMessageAw I).toNat := by
    unfold hashPaddedMessageAw
    apply machineM_ofNat_ge
    rw [hashLengthAddr_toNat I hsmall, hashPadPtr_toNat I hsmall,
      show UInt256.size = 2 ^ 256 from by decide]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    unfold maxFallbackCalldataSize at hsmall
    omega
  exact le_trans (hashZeroAw_ge_six I hsmall (le_refl _))
    (le_trans hmarker hlength)

theorem hashPaddedMessageAw_lt_pow64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPaddedMessageAw I).toNat < 2 ^ 64 := by
  have hz := hashZeroAw_lt_pow64 I hsmall (le_refl (hashZeroIterations I))
  have hm : (hashMarkerAw I).toNat < 2 ^ 64 := by
    unfold hashMarkerAw
    apply machineM_ofNat_lt_pow64 _ _ _ hz
    rw [hashMarkerAddr_toNat I hsmall, hashPadPtr_toNat I hsmall]
    unfold maxFallbackCalldataSize at hsmall
    omega
  unfold hashPaddedMessageAw
  apply machineM_ofNat_lt_pow64 _ _ _ hm
  rw [hashLengthAddr_toNat I hsmall, hashPadPtr_toNat I hsmall]
  have hp := (hashPaddedLength_bounds I.calldata.size).2
  unfold maxFallbackCalldataSize at hsmall
  omega

/-- Active memory at hash entry covers every byte of the padded message. -/
theorem hashPaddedMessageAw_covers_message (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (hashPadPtr I).toNat + Model.paddedLength I.calldata.size ≤
      32 * (hashPaddedMessageAw I).toNat := by
  unfold hashPaddedMessageAw
  rw [ulit_toNat' _ (machineM_lt_uint256 (hashMarkerAw I)
    (hashLengthAddr I).toNat 32 (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      rw [hashLengthAddr_toNat I hsmall, hashPadPtr_toNat I hsmall]
      have hp := (hashPaddedLength_bounds I.calldata.size).2
      unfold maxFallbackCalldataSize at hsmall
      omega))]
  unfold MachineState.M
  simp only [OfNat.ofNat]
  apply le_trans
    (b := 32 * (((hashLengthAddr I).toNat + 32 + 31) / 32))
  · rw [hashLengthAddr_toNat I hsmall]
    have hmod := Nat.mod_lt ((hashLengthAddr I).toNat + 63)
      (by decide : 0 < 32)
    have hdecomp := Nat.mod_add_div ((hashLengthAddr I).toNat + 63) 32
    omega
  · exact Nat.mul_le_mul_left 32 (Nat.le_max_right _ _)

theorem hashPaddedMessageAw_mload64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    UInt256.ofNat (MachineState.M (hashPaddedMessageAw I).toNat 64 32) =
      hashPaddedMessageAw I := by
  change UInt256.ofNat (max (hashPaddedMessageAw I).toNat 3) =
    hashPaddedMessageAw I
  rw [max_eq_left (by have := hashPaddedMessageAw_ge_six I hsmall; omega)]
  exact u256_ofNat_toNat _

theorem hashPaddedMessageMload64Value (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (if (⟨64⟩ : UInt256).toNat ≥ (hashPaddedMessageMem I).size ∨
          (⟨64⟩ : UInt256) ≥ hashPaddedMessageAw I * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((hashPaddedMessageMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      hashNewFreePtr I := by
  rw [if_neg]
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      hashPaddedMessageMem_read64 I hsmall, fromByteArrayBigEndian_toByteArray]
    exact u256_ofNat_toNat _
  · push Not
    constructor
    · have hs := toByteArray_write_size_ge_off_add32 (hashBitLengthWord I)
        (hashMarkerMem I) (hashLengthAddr I).toNat (by
          have hle : (hashLengthAddr I).toNat ≤ (hashMarkerMem I).size := by
            rw [hashMarkerMem_size I hsmall, hashLengthAddr_toNat I hsmall]
            have hc := hashZeroMem_covers I hsmall (le_refl (hashZeroIterations I))
            have he := hashZeroIterations_exit I
            omega
          simp [Nat.sub_eq_zero_of_le hle])
      unfold hashPaddedMessageMem
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have ha : 96 ≤ (hashLengthAddr I).toNat := by
        rw [hashLengthAddr_toNat I hsmall, hashPadPtr_toNat I hsmall]
        have hp := hashPaddedLength_pos I.calldata.size
        omega
      omega
    · intro h
      change (hashPaddedMessageAw I * ⟨32⟩).toNat ≤ 64 at h
      rw [umul_toNat] at h
      · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide] at h
        have := hashPaddedMessageAw_ge_six I hsmall
        omega
      · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
          show UInt256.size = 2 ^ 256 from by decide]
        have := hashPaddedMessageAw_lt_pow64 I hsmall
        omega

theorem hashPaddedMessageMload64Cost (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) (s : State)
    (haw : s.machineState.activeWords = hashPaddedMessageAw I)
    (hstk : s.machineState.stack = (⟨64⟩ : UInt256) :: t) :
    memoryExpansionCost s .MLOAD = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk]
  rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
    haw, hashPaddedMessageAw_mload64 I hsmall]
  omega

end Ripemd160
