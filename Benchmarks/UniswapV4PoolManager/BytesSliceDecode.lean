import Benchmarks.UniswapV4PoolManager.BytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

instance (cd : ByteArray) (start : Nat) : Decidable (BytesSliceBounds cd start) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- LIBRARY CANDIDATE: selector-relative bytes decoding at an arbitrary offset.
def calldataBytesSlice (cd : ByteArray) (start : Nat) : ByteArray :=
  cd.extract (start+32) (start+32+(calldataWord cd start).toNat)

theorem decodeABIValue_bytes_calldata {cd : ByteArray} (off : Nat) (h4 : 4 ≤ cd.size) (hhi : cd.size < 2^255) :
    decodeABIValue? .bytes (cd.toList.drop 4) off =
      if BytesSliceBounds cd (4+off) then
        some (.bytes (calldataBytesSlice cd (4+off)), off+32+paddedSize (calldataWord cd (4+off)).toNat)
      else none := by
  have ht : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeABIValue_bytes_eq]
  by_cases hlen : 4+off+32 ≤ cd.size
  · rw [readNat_drop4_at_eq_calldataWord off hlen]
    simp only [List.length_drop, ht, BytesSliceBounds, hhi, hlen, true_and]
    have he : off+32+(calldataWord cd (4+off)).toNat ≤ cd.size-4 ↔
        4+off+32+(calldataWord cd (4+off)).toNat ≤ cd.size := by omega
    simp only [he]
    split_ifs
    · simp only [List.drop_drop, calldataBytesSlice]
      rw [bytesSlice_eq_extract]
      congr 3 <;> omega
    · rfl
  · have hr : readNat? (cd.toList.drop 4) off = none := by
      unfold readNat? readWord? readBytes?
      rw [if_neg (by rw [List.length_take, List.length_drop, List.length_drop, ht]; omega)]
      rfl
    rw [hr, if_neg (fun hh => hlen hh.2.1)]

end Benchmarks.UniswapV4PoolManager
