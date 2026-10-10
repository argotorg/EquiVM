import Benchmarks.UniswapV4PoolManager.Values
import Reasoning.ABIViews

/-! Fixed bytes4 ABI padding and EVM word comparisons. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV4PoolManager

abbrev bytes4Mask : UInt256 :=
  UInt256.ofNat (2^256 - 2^224)

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem bytes4Mask_toNat (w : UInt256) :
    (UInt256.land w bytes4Mask).toNat = w.toNat / 2^224 * 2^224 := by
  change (Nat.land w.toNat bytes4Mask.toNat) % UInt256.size = _
  rw [show bytes4Mask.toNat = 2^256 - 2^224 from by decide]
  rw [natLandClearLow224 w.toNat w.val.isLt]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (by
    simpa [Nat.mul_comm] using Nat.mul_div_le w.toNat (2^224)) w.val.isLt)

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem bytes4Mask_clean_iff (w : UInt256) :
    UInt256.land w bytes4Mask = w ↔ w.toNat % 2^224 = 0 := by
  constructor
  · intro h
    have ht := congrArg UInt256.toNat h
    rw [bytes4Mask_toNat] at ht
    have hd := Nat.div_add_mod w.toNat (2^224)
    omega
  · intro h
    apply u256_inj
    rw [bytes4Mask_toNat]
    have hd := Nat.div_add_mod w.toNat (2^224)
    omega

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem calldata_wordList32_length {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    ((cd.toList.drop 4).take 32).length = 32 := by
  rw [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
  change min 32 (cd.size - 4) = 32
  omega

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem calldataWord4_toNat {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    (calldataWord cd 4).toNat = fromBytesBigEndian ((cd.toList.drop 4).take 32) := by
  rw [calldataWord, ← decode_word_at_eq_any cd 4 hlen]
  exact bytesToWord_toNat_of_len _ (calldata_wordList32_length hlen)

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem bytes4Padding_iff {xs : List UInt8} (hlen : xs.length = 32) :
    zeroPadding? xs 4 28 = some () ↔ fromBytesBigEndian xs % 2^224 = 0 := by
  have htail : (xs.drop 4).length = 28 := by rw [List.length_drop, hlen]
  have htake : (xs.drop 4).take 28 = xs.drop 4 := List.take_of_length_le (by omega)
  have hmod : fromBytesBigEndian xs % 2^224 = fromBytesBigEndian (xs.drop 4) := by
    conv_lhs => rw [← List.take_append_drop 4 xs]
    rw [fromBytesBigEndian_append, htail]
    have hb : fromBytesBigEndian (xs.drop 4) < 2^224 := by
      simpa only [htail] using fromBytesBigEndian_bound (xs.drop 4)
    omega
  simp only [zeroPadding?, readBytes?, htake, htail, ↓reduceIte, bind, Option.bind,
    hmod, fromBytesBigEndian_zero_iff_all_zero]
  cases (xs.drop 4).all (· == 0) <;> simp

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem bytes4Padding_mask_iff {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    zeroPadding? ((cd.toList.drop 4).take 32) 4 28 = some () ↔
      UInt256.land (calldataWord cd 4) bytes4Mask = calldataWord cd 4 := by
  rw [bytes4Padding_iff (calldata_wordList32_length hlen), bytes4Mask_clean_iff,
    calldataWord4_toNat hlen]

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem calldataBytes4Arg_length {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    (calldataBytes4Arg cd).length = 4 := by
  simp only [calldataBytes4Arg, List.length_take, calldata_wordList32_length hlen]
  rfl

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem maskedBytes4_toNat {cd : ByteArray} (hlen : 36 ≤ cd.size) :
    (UInt256.land (calldataWord cd 4) bytes4Mask).toNat =
      fromBytesBigEndian (calldataBytes4Arg cd) * 2^224 := by
  rw [bytes4Mask_toNat, calldataWord4_toNat hlen]
  have htail : (((cd.toList.drop 4).take 32).drop 4).length = 28 := by
    rw [List.length_drop, calldata_wordList32_length hlen]
  congr 1
  conv_lhs => rw [← List.take_append_drop 4 ((cd.toList.drop 4).take 32)]
  rw [show (224 : Nat) = 8 * (((cd.toList.drop 4).take 32).drop 4).length by rw [htail]]
  exact fromBytesBigEndian_append_div _ _

-- LIBRARY CANDIDATE: bytes4 calldata, padding, and masked word correspondence.
theorem maskedBytes4_eq {cd : ByteArray} {bytes : List UInt8} {word : UInt256}
    (hlen : 36 ≤ cd.size) (hbytes : bytes.length = 4)
    (hword : word.toNat = fromBytesBigEndian bytes * 2^224) :
    UInt256.eq (UInt256.land (calldataWord cd 4) bytes4Mask) word =
      (calldataBytes4Arg cd == bytes).toUInt256 := by
  have heq : UInt256.land (calldataWord cd 4) bytes4Mask = word ↔ calldataBytes4Arg cd = bytes := by
    constructor
    · intro h
      apply fromBytesBigEndian_inj4 (calldataBytes4Arg_length hlen) hbytes
      have hn := congrArg UInt256.toNat h
      rw [maskedBytes4_toNat hlen, hword] at hn
      omega
    · intro h
      apply u256_inj
      rw [maskedBytes4_toNat hlen, hword, h]
  simp only [UInt256.eq, heq, UInt256.fromBool, listUInt8_decide_eq_beq]

end Benchmarks.UniswapV4PoolManager
