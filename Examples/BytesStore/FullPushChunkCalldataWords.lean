import Examples.BytesStore.FullPushChunkLongTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStore

theorem bytesStoreCalldataLongDataTailMaskedWord_eq_decoded_tail
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hsize : (StringStoreLite.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0) :
    StringStoreLite.longDataTailMaskedWord
        (bytesStoreCalldataLongDataWord I payloadStart
          (UInt256.ofNat (32 * (len.toNat / 32))) 0) len =
      uInt256OfByteArray
        ((StringStoreLite.setDecodedValueBytes I).readWithPadding
          (32 * (len.toNat / 32)) 32) := by
  let q := len.toNat / 32
  let rem := len.toNat % 32
  let remWord := UInt256.land len ⟨31⟩
  have hremNat : remWord.toNat = rem := by
    dsimp [remWord, rem]
    rw [StringStoreLite.u256_land_31_toNat]
  have hremLt : rem < 32 := by
    dsimp [rem]
    exact Nat.mod_lt _ (by decide : 0 < 32)
  have hremWordLt : remWord.toNat < 32 := by
    rw [hremNat]
    exact hremLt
  have hsrcTail : payloadStart.toNat + 32 * q + rem ≤ I.calldata.size := by
    dsimp [q, rem]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hdecoded :
      StringStoreLite.setDecodedValueBytes I =
        I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat) :=
    StringStoreLite.setDecodedValueBytes_eq_extract
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax
  have htailList :
      (I.calldata.data.toList.drop (payloadStart.toNat + 32 * q)).take rem =
        (StringStoreLite.setDecodedValueBytes I).toList.drop (32 * q) := by
    rw [hdecoded]
    rw [StringStoreLite.byteArray_extract_toList]
    rw [byteArray_toList_eq]
    rw [List.drop_take]
    rw [List.drop_drop]
    rw [show payloadStart.toNat + len.toNat - payloadStart.toNat - 32 * q = rem by
      dsimp [q, rem]
      have hdiv := Nat.div_add_mod len.toNat 32
      omega]
  have hmask :
      UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
          (UInt256.mul ⟨8⟩ remWord)) =
        UInt256.ofNat (2 ^ 256 - 2 ^ (256 - 8 * rem)) := by
    have h := StringStoreLite.setShortPackedHeader_mask_of_short
      (len := remWord) hremWordLt
    simpa [hremNat, rem] using h
  have hleft :
      StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * (len.toNat / 32))) 0) len =
        UInt256.ofNat
          (fromBytesBigEndian
            ((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * q) ++
              List.replicate
                (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
                  (32 * q)).length) 0)) := by
    rw [bytesStoreCalldataLongDataWord, StringStoreLite.longDataWordsLoopStride]
    rw [haddr]
    dsimp [q] at *
    unfold StringStoreLite.longDataTailMaskedWord
    rw [show UInt256.land len ⟨31⟩ = remWord by rfl]
    rw [hmask]
    have htailLen :
        ((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * q)).length = rem := by
      dsimp [q, rem]
      exact StringStoreLite.setDecodedValueBytes_tail_length
        (I := I) (len := len) hsize
    have hpad := uInt256OfByteArray_readBytes_at_high_mask_eq_padded I.calldata
      (payloadStart.toNat + 32 * q) rem hremLt hsrcTail
    simpa [q, htailList, htailLen] using hpad
  have hright :
      uInt256OfByteArray
          ((StringStoreLite.setDecodedValueBytes I).readWithPadding
            (32 * (len.toNat / 32)) 32) =
        UInt256.ofNat
          (fromBytesBigEndian
            ((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * q) ++
              List.replicate
                (32 - ((StringStoreLite.setDecodedValueBytes I).toList.drop
                  (32 * q)).length) 0)) := by
    dsimp [q]
    exact StringStoreLite.setDecodedValueBytes_readWithPadding_tail_word
      (I := I) (len := len) hsize hlong hmod
  rw [hleft, hright]

end BytesStore
