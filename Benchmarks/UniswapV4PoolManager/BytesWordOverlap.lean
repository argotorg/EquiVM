import Benchmarks.UniswapV4PoolManager.BytesReturnDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the natural value of an in-bounds ABI word.
theorem calldataWord_toNat_of_inBounds {out : ByteArray} {start : Nat}
    (h : start+32 ≤ out.size) :
    (calldataWord out start).toNat = fromBytesBigEndian ((out.toList.drop start).take 32) := by
  rw [calldataWord, ← decode_word_at_eq_any out start h]
  apply bytesToWord_toNat_of_len
  rw [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
  change min 32 (out.size-start) = 32
  omega

-- LIBRARY CANDIDATE: overlapping big-endian words share the same byte suffix/prefix.
theorem calldataWord_overlap {out : ByteArray} {off : Nat}
    (hoff : off ≤ 32) (hin : off+32 ≤ out.size) :
    (calldataWord out off).toNat / 2^(8*off) =
      (calldataWord out 0).toNat % 2^(8*(32-off)) := by
  let xs := out.toList
  have hs : 32 ≤ xs.length := by
    dsimp only [xs]
    rw [byteArray_toList_eq, Array.length_toList]
    change 32 ≤ out.size
    omega
  have ht : ((xs.drop 32).take off).length = off := by
    rw [List.length_take, List.length_drop]
    have : off+32 ≤ xs.length := by
      dsimp only [xs]
      rw [byteArray_toList_eq, Array.length_toList]
      exact hin
    omega
  have hd : ((xs.take 32).drop off).length = 32-off := by
    rw [List.length_drop, List.length_take, Nat.min_eq_left hs]
  have hp : (xs.drop off).take 32 =
      (xs.take 32).drop off ++ (xs.drop 32).take off := by
    conv_lhs => rw [show 32 = (32-off)+off by omega, List.take_add]
    rw [List.drop_take, List.drop_drop, show off+(32-off) = 32 by omega]
  rw [calldataWord_toNat_of_inBounds hin,
    calldataWord_toNat_of_inBounds (by omega : 0+32 ≤ out.size)]
  change fromBytesBigEndian ((xs.drop off).take 32) / 2^(8*off) =
    fromBytesBigEndian (xs.take 32) % 2^(8*(32-off))
  have hdiv : fromBytesBigEndian ((xs.take 32).drop off ++ (xs.drop 32).take off) /
      2^(8*off) = fromBytesBigEndian ((xs.take 32).drop off) := by
    simpa only [ht] using fromBytesBigEndian_append_div ((xs.take 32).drop off) ((xs.drop 32).take off)
  rw [hp, hdiv]
  conv_rhs => rw [← List.take_append_drop off (xs.take 32)]
  rw [fromBytesBigEndian_append, hd, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt (by simpa only [hd] using fromBytesBigEndian_bound ((xs.take 32).drop off))]

/-- A valid bytes reply with a large payload cannot place its length word inside its offset word. -/
theorem bytesReturn_large_offset {out : ByteArray} (hb : BytesReturnBounds out)
    (hl : 2^59 ≤ (calldataWord out (calldataWord out 0).toNat).toNat) :
    32 ≤ (calldataWord out 0).toNat := by
  by_contra hn
  have ho : (calldataWord out 0).toNat < 32 := by omega
  have hover := calldataWord_overlap (Nat.le_of_lt ho) hb.2.2.2.1
  have hlen := hb.2.2.2.2.1
  change (calldataWord out (calldataWord out 0).toNat).toNat ≤ 2^64-1 at hlen
  generalize h : (calldataWord out 0).toNat = off at ho hover hl hlen
  interval_cases off <;> norm_num at hover <;> omega

theorem bytesReturn_large_size {out : ByteArray} (hb : BytesReturnBounds out)
    (hl : 2^59 ≤ (calldataWord out (calldataWord out 0).toNat).toNat) :
    (calldataWord out (calldataWord out 0).toNat).toNat+64 ≤ out.size := by
  have := bytesReturn_large_offset hb hl
  have := hb.2.2.2.2.2
  omega

end Benchmarks.UniswapV4PoolManager
