import Benchmarks.Midnight.BytesCalldataDecode

/-! Padded calldata reads, including references outside the input. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the list and byte-array forms of a padded calldata read agree.
theorem readBytes_toList_eq (bytes : ByteArray) (start len : Nat) :
    (bytes.readBytes start len).toList =
      (bytes.toList.drop start).take len ++
        List.replicate (len - ((bytes.toList.drop start).take len).length) 0 := by
  have hc : (bytes.copySlice start ByteArray.empty 0 len).data.toList =
      (bytes.toList.drop start).take len := by
    rw [ByteArray.data_copySlice]
    simp [byteArray_toList_eq, Array.toList_extract, List.extract]
  have hs : (bytes.copySlice start ByteArray.empty 0 len).size =
      ((bytes.toList.drop start).take len).length := by
    change (bytes.copySlice start ByteArray.empty 0 len).data.size = _
    rw [← Array.length_toList, hc]
  unfold ByteArray.readBytes
  split
  · simp only [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append,
      byteArray_zeroes_toList, hc, hs]
  · simp only [byteArray_toList_eq, ByteArray.data_append, Array.toList_append,
      byteArray_zeroes_toList, ByteArray.size, List.toList_toArray]
    rfl

theorem solcReadNat_word (bytes : ByteArray) (start : UInt256) :
    solcReadNat bytes.toList start.toNat = (calldataWord bytes start.toNat).toNat := by
  rw [solcReadNat, solcReadBytes,
    Nat.mod_eq_of_lt (show start.toNat < EVM.wordModulus from start.val.isLt),
    ← readBytes_toList_eq]
  congr 1
  rw [calldataWord, uInt256OfByteArray_eq]
  unfold bytesToWord fromByteArrayBigEndian
  simp only [byteArray_toList_eq, List.toList_toArray]

theorem calldataWord_eq_zero_of_ge (bytes : ByteArray) (start : Nat)
    (h : bytes.size ≤ start) : calldataWord bytes start = ⟨0⟩ := by
  have hd : bytes.toList.drop start = [] := by
    apply List.drop_eq_nil_iff.mpr
    simpa only [byteArray_toList_eq, Array.length_toList] using h
  rw [calldataWord, uInt256OfByteArray_eq]
  unfold fromByteArrayBigEndian
  rw [readBytes_toList_eq, hd]
  simp only [List.take_nil, List.length_nil, Nat.sub_zero, List.nil_append,
    fromBytesBigEndian, List.reverse_replicate, fromBytes'_replicate_zero]
  rfl

theorem solcBytesPayload_empty {bytes : ByteArray} {start : UInt256}
    (hz : (calldataWord bytes start.toNat).toNat = 0) :
    (decodeABIValue? .bytes (solcReadBytes bytes.toList start.toNat 32) 0).map Prod.fst =
      some (.bytes ByteArray.empty) := by
  have hl : (solcReadBytes bytes.toList start.toNat 32).length = 32 := by
    simp only [solcReadBytes, List.length_append, List.length_replicate,
      List.length_take, List.length_drop]
    omega
  have hn : readNat? (solcReadBytes bytes.toList start.toNat 32) 0 = some 0 := by
    have hw := solcReadNat_word bytes start
    unfold solcReadNat at hw
    rw [hz] at hw
    simp only [readNat?, readWord?, readBytes?, List.drop_zero,
      List.take_of_length_le (by omega :
        (solcReadBytes bytes.toList start.toNat 32).length ≤ 32), hl, if_true,
      bind, Option.bind]
    change some (bytesToWord (solcReadBytes bytes.toList start.toNat 32)).toNat = some 0
    rw [hw]
  rw [decodeABIValue?, hn]
  simp only [bind, Option.bind, solcMaxLen_modern, solcMaxU64, Nat.not_lt_zero, if_false,
    Nat.zero_add, readBytes?, List.take_zero, List.length_nil, if_true, Option.map]
  rfl

end Benchmarks.Midnight
