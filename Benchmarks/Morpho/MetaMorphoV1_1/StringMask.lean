import Benchmarks.Morpho.MetaMorphoV1_1.StringBufferWords

/-! The masks used by metadata setters retain precisely the payload prefix of a word. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 4096

def stringMaskedWord (word : UInt256) (len : Nat) : UInt256 :=
  UInt256.land
    (UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
      (UInt256.shiftLeft (UInt256.ofNat len) ⟨3⟩))) word

theorem stringMaskedWord_bytes (word : UInt256) (len : Nat)
    (hpos : 0 < len) (hshort : len < 32) :
    (stringMaskedWord word len).toByteArray =
      ⟨((word.toByteArray.extract 0 len).toList ++ List.replicate (32 - len) 0).toArray⟩ := by
  have hm : UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
      (UInt256.shiftLeft (UInt256.ofNat len) ⟨3⟩)) =
      UInt256.lnot (UInt256.sub (UInt256.exp ⟨256⟩
        (UInt256.sub ⟨32⟩ (UInt256.ofNat len))) ⟨1⟩) := by
    interval_cases len <;> decide +kernel
  have hn : (UInt256.ofNat len).toNat = len :=
    UInt256.toNat_ofNat_of_lt (by norm_num [UInt256.size]; omega)
  unfold stringMaskedWord
  rw [hm, tailMask_toByteArray word (UInt256.ofNat len) (by omega) (by omega), hn]

theorem stringMaskedWord_zero (word : UInt256) : stringMaskedWord word 0 = ⟨0⟩ := by
  unfold stringMaskedWord
  change UInt256.land ⟨0⟩ word = ⟨0⟩
  exact uint256_land_zero_left word

theorem stringTailShift (len : UInt256) (hsmall : len.toNat < 2 ^ 64) :
    UInt256.land (UInt256.shiftLeft len ⟨3⟩) ⟨248⟩ =
      UInt256.shiftLeft (UInt256.ofNat (len.toNat % 32)) ⟨3⟩ := by
  apply u256_inj
  have hs : (UInt256.shiftLeft len ⟨3⟩).toNat = len.toNat <<< 3 := by
    change (len.toNat <<< 3) % UInt256.size = len.toNat <<< 3
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    norm_num [UInt256.size] at hsmall ⊢
    omega
  rw [u256_land_toNat, hs]
  change ((len.toNat <<< 3) &&& 248) % UInt256.size =
    (((len.toNat % 32) % UInt256.size) <<< 3) % UInt256.size
  have hr : len.toNat % 32 < UInt256.size := by
    have hmod := Nat.mod_lt len.toNat (by decide : 0 < 32)
    norm_num [UInt256.size] at hmod ⊢
    omega
  rw [Nat.mod_eq_of_lt hr, show 248 = (31 : Nat) <<< 3 from rfl,
    ← Nat.shiftLeft_and_distrib]
  change (Nat.land len.toNat 31) <<< 3 % UInt256.size = _
  rw [nat_land_31_eq_mod_32]

theorem stringTailReadList (bytes : ByteArray) (off : Nat)
    (hoff : off < bytes.size) (htail : bytes.size < off + 32) :
    (bytes.readWithPadding off 32).toList =
      (bytes.extract off bytes.size).toList ++ List.replicate (32 - (bytes.size - off)) 0 := by
  have hdrop : (bytes.toList.drop off).length = bytes.size - off := by
    rw [List.length_drop, byteArray_toList_eq, Array.length_toList, ByteArray.size_data]
  have he : bytes.extract off (off + min 32 bytes.size) = bytes.extract off bytes.size := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
    rw [List.take_of_length_le (by
      rw [← byteArray_toList_eq, hdrop]; omega), List.take_of_length_le (by
      rw [← byteArray_toList_eq, hdrop])]
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬ off ≥ bytes.size)]
  change (bytes.extract off (off + min 32 bytes.size) ++
    ByteArray.zeroes (32 - (bytes.extract off (off + min 32 bytes.size)).size)).toList = _
  rw [he, byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append,
    ← byteArray_toList_eq, byteArray_zeroes_toList,
    ByteArray.size_extract, min_self]

theorem StringBuffer.maskedTail {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (off : Nat)
    (hoff : off < bytes.size) (htail : bytes.size < off + 32)
    (hcover : off + 32 ≤ paddedSize bytes.size) :
    stringMaskedWord (memLoad (ptr + UInt256.ofNat (32 + off)) mem) (bytes.size - off) =
      uInt256OfByteArray (bytes.readWithPadding off 32) := by
  have hadd : (ptr + UInt256.ofNat (32 + off)).toNat = ptr.toNat + 32 + off := by
    rw [uadd_word_ofNat_toNat _ _ (by omega)]; omega
  have hmem : ptr.toNat + 32 + off + 32 ≤ mem.size := by
    have hs := buffer.size
    omega
  have hword : (memLoad (ptr + UInt256.ofNat (32 + off)) mem).toByteArray =
      mem.readWithPadding (ptr.toNat + 32 + off) 32 := by
    symm
    apply readWord_of_memLoad _ _ _ hmem (by omega)
    rw [← hadd, u256_ofNat_toNat]
  have hdata := buffer.data
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega)] at hdata
  have he := congrArg (fun b : ByteArray ↦ b.extract off bytes.size) hdata
  simp only [ByteArray.extract_extract] at he
  rw [Nat.min_eq_left (by omega)] at he
  have hprefix : (memLoad (ptr + UInt256.ofNat (32 + off)) mem).toByteArray.extract
      0 (bytes.size - off) = bytes.extract off bytes.size := by
    rw [hword, readWithPadding_eq_extract _ _ hmem, ByteArray.extract_extract]
    simp only [Nat.add_zero]
    rw [Nat.min_eq_left (by omega)]
    convert he using 1 <;> congr 1 <;> omega
  have hm := stringMaskedWord_bytes (memLoad (ptr + UInt256.ofNat (32 + off)) mem)
    (bytes.size - off) (by omega) (by omega)
  rw [hprefix] at hm
  have hp : (stringMaskedWord (memLoad (ptr + UInt256.ofNat (32 + off)) mem)
      (bytes.size - off)).toByteArray = bytes.readWithPadding off 32 := by
    rw [hm]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [List.toList_toArray, ← byteArray_toList_eq, stringTailReadList bytes off hoff htail]
  rw [← hp, uInt256OfByteArray_toByteArray]

def stringPackedHeader (word len : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩))) word)
    (UInt256.shiftLeft len ⟨1⟩)

theorem stringPackedHeader_empty : stringPackedHeader ⟨0⟩ ⟨0⟩ =
    solidityShortBytesWord ByteArray.empty := by
  decide +kernel

theorem StringBuffer.packedHeader {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hshort : bytes.size < 32) :
    stringPackedHeader (memLoad (ptr + ⟨32⟩) mem) (UInt256.ofNat bytes.size) =
      solidityShortBytesWord bytes := by
  have htag : UInt256.shiftLeft (UInt256.ofNat bytes.size) ⟨1⟩ =
      UInt256.ofNat (bytes.size * 2) := by
    rw [shiftLeft1_ofNat_eq (by norm_num [UInt256.size]; omega), Nat.mul_comm]
  change UInt256.lor (stringMaskedWord (memLoad (ptr + ⟨32⟩) mem) bytes.size)
    (UInt256.shiftLeft (UInt256.ofNat bytes.size) ⟨1⟩) = _
  rw [htag, solidityShortBytesWord]
  congr 1
  by_cases hz : bytes.size = 0
  · have he : bytes = ByteArray.empty := ByteArray.ext (Array.size_eq_zero_iff.mp hz)
    rw [hz, stringMaskedWord_zero, he, empty_readWithPadding32_eq_zeroWord,
      uInt256OfByteArray_toByteArray]
  · simpa only [Nat.add_zero, Nat.sub_zero] using buffer.maskedTail hfit 0 (by omega)
      (by omega) (by unfold paddedSize; omega)

def stringStorageTailWord (word len : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
      (UInt256.land (UInt256.shiftLeft len ⟨3⟩) ⟨248⟩))) word

theorem StringBuffer.storageTail {mem bytes : ByteArray} {ptr len : UInt256}
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hlen : len.toNat = bytes.size) (hsmall : bytes.size < 2 ^ 64)
    (htail : bytes.size % 32 ≠ 0) :
    stringStorageTailWord (memLoad (ptr + UInt256.ofNat (32 * (bytes.size / 32 + 1))) mem)
      len = uInt256OfByteArray (bytes.readWithPadding (bytes.size / 32 * 32) 32) := by
  unfold stringStorageTailWord
  rw [stringTailShift len (by omega), hlen]
  change stringMaskedWord _ (bytes.size % 32) = _
  have hmod := Nat.mod_lt bytes.size (by decide : 0 < 32)
  rw [show bytes.size % 32 = bytes.size - bytes.size / 32 * 32 by omega,
    show 32 * (bytes.size / 32 + 1) = 32 + bytes.size / 32 * 32 by omega]
  exact buffer.maskedTail hfit _ (by omega) (by omega) (by unfold paddedSize; omega)

end Benchmarks.Morpho.MetaMorphoV1_1
