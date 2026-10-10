import Benchmarks.UniswapV4PoolManager.UnlockAllocationBounds
import Benchmarks.UniswapV4PoolManager.MemoryFootprint

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the low byte of an in-bounds ABI word.
theorem calldataWord_lastByte {out : ByteArray} {start : Nat} (hs : start+32 ≤ out.size) :
    (calldataWord out start).toNat % 256 = (out[start+31]'(by omega)).toNat := by
  have hi : 31 < (out.toList.drop start).length := by
    rw [List.length_drop, byteArray_toList_eq, Array.length_toList]
    change 31 < out.size-start
    omega
  have he : (out.toList.drop start)[31]'hi = out[start+31]'(by omega) := by
    simp only [List.getElem_drop, byteArray_toList_eq, Array.getElem_toList]
    rfl
  rw [calldataWord_toNat_of_inBounds hs,
    show 32 = 31+1 from rfl, List.take_succ_eq_append_getElem hi, fromBytesBigEndian_append, he]
  change (_*256+out[start+31].toNat)%256 = out[start+31].toNat
  rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
  exact out[start+31].toFin.isLt

/-- A reply in the tight allocator range has nonzero bytes in two separated ABI words. -/
theorem unlockCriticalReplyFootprint {out : ByteArray} (hb : BytesReturnBounds out)
    (hl : 2^63-159 ≤ (unlockReturnLength out).toNat)
    (hu : (unlockReturnLength out).toNat ≤ 2^63-128)
    (ho : 32 ≤ (calldataWord out 0).toNat)
    (ho' : (calldataWord out 0).toNat ≤ 63) : memoryFootprint out = 14 := by
  have hs := hb.1
  have hlen := hb.2.2.2.1
  have hw0 := calldataWord_lastByte (show 0+32 ≤ out.size by omega)
  have hw1 := calldataWord_lastByte hlen
  have hn0 : out[31]'(by omega) ≠ 0 := by
    intro hn
    simp only [Nat.zero_add] at hw0
    rw [hn] at hw0
    change (calldataWord out 0).toNat % 256 = 0 at hw0
    omega
  have hn1 : out[(calldataWord out 0).toNat+31]'(by omega) ≠ 0 := by
    intro hn
    rw [hn] at hw1
    change (unlockReturnLength out).toNat % 256 = 0 at hw1
    omega
  exact memoryFootprint_of_separated (by omega) (by omega) (by omega) hn0 hn1

end Benchmarks.UniswapV4PoolManager
