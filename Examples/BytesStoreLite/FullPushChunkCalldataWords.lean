import Examples.BytesStoreLite.FullPushChunkLongTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStoreLite

theorem bytesStoreLiteCalldataLongDataWord_full_word_of_addr
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * i)).toNat = payloadStart.toNat + 32 * i)
    (hread : payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hdecoded :
      BytesStoreLiteCore.setDecodedValueBytes I =
        I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat))
    (hi : i < len.toNat / 32) :
    bytesStoreLiteCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
      uInt256OfByteArray
        ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (i * 32) 32) := by
  have hfull : 32 * i + 32 ≤ len.toNat := by
    have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
      Nat.mul_le_mul_left 32 hsucc
    have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hle := le_trans hmul hdiv
    omega
  have hwordDirect :
      uInt256OfByteArray
          ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (i * 32) 32) =
        UInt256.ofNat
          (fromBytesBigEndian
            (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
    simpa [Nat.mul_comm] using
      BytesStoreLiteCore.setDecodedValueBytes_readWithPadding_full_word
        (I := I) (len := len) (i := i) hsize hi
  have hleftList :
      (ByteArray.readBytes I.calldata (payloadStart.toNat + 32 * i) 32).data.toList =
        ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * i)).take 32 := by
    rw [hdecoded]
    rw [BytesStoreLiteCore.byteArray_extract_toList]
    rw [readBytes_at_toList_any I.calldata (payloadStart.toNat + 32 * i) hread]
    rw [byteArray_toList_eq]
    rw [List.drop_take]
    rw [List.drop_drop]
    rw [List.take_take]
    have hmin :
        min 32 (payloadStart.toNat + len.toNat - payloadStart.toNat - 32 * i) = 32 := by
      omega
    rw [hmin]
  have hleft :
      bytesStoreLiteCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
        UInt256.ofNat
          (fromBytesBigEndian
            (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
    have hleftToList :
        (ByteArray.readBytes I.calldata (payloadStart.toNat + 32 * i) 32).toList =
          ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * i)).take 32 := by
      rw [byteArray_toList_eq]
      exact hleftList
    rw [bytesStoreLiteCalldataLongDataWord, BytesStoreLiteCore.longDataWordsLoopStride]
    rw [haddr]
    rw [uInt256OfByteArray_eq]
    unfold fromByteArrayBigEndian
    rw [hleftToList]
  rw [hleft, hwordDirect]

theorem bytesStoreLiteCalldataLongDataWord_full_word
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * i)).toNat = payloadStart.toNat + 32 * i)
    (hread : payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hi : i < len.toNat / 32) :
    bytesStoreLiteCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
      uInt256OfByteArray
        ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (i * 32) 32) := by
  exact bytesStoreLiteCalldataLongDataWord_full_word_of_addr
    (I := I) (len := len) (payloadStart := payloadStart) (i := i)
    haddr hread hsize
    (BytesStoreLiteCore.setDecodedValueBytes_eq_extract
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax)
    hi

theorem bytesStoreLiteCalldataLongDataRead_full_bounds
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hi : i < len.toNat / 32) :
    payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size := by
  have hfull : 32 * i + 32 ≤ len.toNat := by
    have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
      Nat.mul_le_mul_left 32 hsucc
    have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hle := le_trans hmul hdiv
    omega
  omega

theorem bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
    {payloadStart : UInt256} {i : Nat}
    (hbound : payloadStart.toNat + 32 * i < UInt256.size) :
    (payloadStart + UInt256.ofNat (32 * i)).toNat =
      payloadStart.toNat + 32 * i := by
  rw [uadd_toNat]
  have hstride : (UInt256.ofNat (32 * i)).toNat = 32 * i :=
    ulit_toNat' _ (by omega)
  rw [hstride]
  exact Nat.mod_eq_of_lt hbound

theorem accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (haddr :
      ∀ i, i < len.toNat / 32 →
        (payloadStart + UInt256.ofNat (32 * i)).toNat =
          payloadStart.toNat + 32 * i)
    (hread :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size) :
    ∀ {τ : AccountMap} {i fuel : Nat},
      i + fuel ≤ len.toNat / 32 →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) i fuel)
        (bytesStoreLiteCalldataLongDataForwardFrom owner τ
          (bytesLikeDataBase baseSlot + UInt256.ofNat i) payloadStart
          (UInt256.ofNat (32 * i)) I fuel)
  | τ, i, 0, _hfuel => by
      simp [solidityDataWordsForwardFrom, bytesStoreLiteCalldataLongDataForwardFrom,
        accountMapEquiv_refl]
  | τ, i, fuel + 1, hfuel => by
      have hi : i < len.toNat / 32 := by omega
      have htailFuel : i + 1 + fuel ≤ len.toNat / 32 := by omega
      have hword :
          bytesStoreLiteCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
            uInt256OfByteArray
              ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (i * 32) 32) := by
        exact bytesStoreLiteCalldataLongDataWord_full_word
          (I := I) (len := len) (payloadStart := payloadStart) (i := i)
          (haddr i hi) (hread i hi) hsize hlenAbi hpayloadStart hoffMax hi
      have hstrideStep :
          (⟨32⟩ : UInt256) + UInt256.ofNat (32 * i) =
            UInt256.ofNat (32 * (i + 1)) := by
        rw [BytesStoreLiteCore.u256_32_add_ofNat]
        congr 1
      have ih :=
        accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full
          (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
          (baseSlot := baseSlot)
          hsize hlenAbi hpayloadStart hoffMax haddr hread
          (τ := sstoreAccountMap owner τ (bytesLikeDataBase baseSlot + UInt256.ofNat i)
            (bytesStoreLiteCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0))
          (i := i + 1) (fuel := fuel) htailFuel
      simpa [solidityDataWordsForwardFrom, bytesStoreLiteCalldataLongDataForwardFrom,
        hword.symm, solidityBytesDataSlot, bytesLikeDataBase, solidityBytesDataBaseSlot,
        BytesStoreLiteCore.u256_base_one_add_ofNat, hstrideStep, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih

theorem accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_of_bounds
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    ∀ {τ : AccountMap} {i fuel : Nat},
      i + fuel ≤ len.toNat / 32 →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) i fuel)
        (bytesStoreLiteCalldataLongDataForwardFrom owner τ
          (bytesLikeDataBase baseSlot + UInt256.ofNat i) payloadStart
          (UInt256.ofNat (32 * i)) I fuel) := by
  intro τ i fuel hfuel
  exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full
    (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
    (baseSlot := baseSlot) hsize hlenAbi hpayloadStart hoffMax
    (fun j hj => bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := j) (haddrBound j hj))
    (fun j hj => bytesStoreLiteCalldataLongDataRead_full_bounds
      (I := I) (len := len) (payloadStart := payloadStart) (i := j) hsrc hj)
    (τ := τ) (i := i) (fuel := fuel) hfuel

theorem accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    {τ : AccountMap} {fuel : Nat}
    (hfuel : fuel ≤ len.toNat / 32) :
    accountMapEquiv
      (solidityDataWordsForwardFrom owner τ baseSlot
        (BytesStoreLiteCore.setDecodedValueBytes I) 0 fuel)
      (bytesStoreLiteCalldataLongDataForwardFrom owner τ
        (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fuel) := by
  have h :=
    accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_of_bounds
      (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := τ) (i := 0) (fuel := fuel) (by simpa using hfuel)
  have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
  have hslot : bytesLikeDataBase baseSlot + (⟨0⟩ : UInt256) = bytesLikeDataBase baseSlot := by
    exact BytesStoreLiteCore.uint256_add_zero_right (bytesLikeDataBase baseSlot)
  simpa [hslot, hzero] using h

theorem bytesStoreLiteCalldataLongDataTailMaskedWord_eq_decoded_tail
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0) :
    BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (UInt256.ofNat (32 * (len.toNat / 32))) 0) len =
      uInt256OfByteArray
        ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding
          (32 * (len.toNat / 32)) 32) := by
  let q := len.toNat / 32
  let rem := len.toNat % 32
  let remWord := UInt256.land len ⟨31⟩
  have hremNat : remWord.toNat = rem := by
    dsimp [remWord, rem]
    rw [BytesStoreLiteCore.u256_land_31_toNat]
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
      BytesStoreLiteCore.setDecodedValueBytes I =
        I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat) :=
    BytesStoreLiteCore.setDecodedValueBytes_eq_extract
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax
  have htailList :
      (I.calldata.data.toList.drop (payloadStart.toNat + 32 * q)).take rem =
        (BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * q) := by
    rw [hdecoded]
    rw [BytesStoreLiteCore.byteArray_extract_toList]
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
    have h := BytesStoreLiteCore.setShortPackedHeader_mask_of_short
      (len := remWord) hremWordLt
    simpa [hremNat, rem] using h
  have hleft :
      BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * (len.toNat / 32))) 0) len =
        UInt256.ofNat
          (fromBytesBigEndian
            ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * q) ++
              List.replicate
                (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
                  (32 * q)).length) 0)) := by
    rw [bytesStoreLiteCalldataLongDataWord, BytesStoreLiteCore.longDataWordsLoopStride]
    rw [haddr]
    dsimp [q] at *
    unfold BytesStoreLiteCore.longDataTailMaskedWord
    rw [show UInt256.land len ⟨31⟩ = remWord by rfl]
    rw [hmask]
    have htailLen :
        ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * q)).length = rem := by
      dsimp [q, rem]
      exact BytesStoreLiteCore.setDecodedValueBytes_tail_length
        (I := I) (len := len) hsize
    have hpad := uInt256OfByteArray_readBytes_at_high_mask_eq_padded I.calldata
      (payloadStart.toNat + 32 * q) rem hremLt hsrcTail
    simpa [q, htailList, htailLen] using hpad
  have hright :
      uInt256OfByteArray
          ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding
            (32 * (len.toNat / 32)) 32) =
        UInt256.ofNat
          (fromBytesBigEndian
            ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * q) ++
              List.replicate
                (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
                  (32 * q)).length) 0)) := by
    dsimp [q]
    exact BytesStoreLiteCore.setDecodedValueBytes_readWithPadding_tail_word
      (I := I) (len := len) hsize hlong hmod
  rw [hleft, hright]

end BytesStoreLite
