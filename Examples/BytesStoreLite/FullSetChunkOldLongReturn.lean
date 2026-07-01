import Examples.BytesStoreLite.FullSetChunk

/-!
# BytesStoreLite — `setChunk(uint256,bytes)` old-long return path

This file keeps the old-long post-write return decoder separate from the main `setChunk` slice so
the already-proven write/body lemmas stay cheap to rebuild.
-/

namespace BytesStoreLite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

noncomputable def bytesStoreLiteSetChunkOldLongBodyMem (slot : UInt256) : ByteArray :=
  wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)

noncomputable def bytesStoreLiteSetChunkOldLongReturnMem (slot : UInt256) : ByteArray :=
  wordAt0Mem (⟨1⟩ : UInt256) (bytesStoreLiteSetChunkOldLongBodyMem slot)

/-- Trusted keccak disjointness consequence: clearing chunk data words does not touch `chunks.length`. -/
axiom bytesStoreLiteChunksLengthAfterClearChunkData
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex oldStoredLen : UInt256) :
    bytesStoreLiteChunksLengthWord
        (clearDataWordsForwardFrom I.codeOwner σ
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        I =
      bytesStoreLiteChunksLengthWord σ I

/-- Trusted keccak disjointness consequence: clearing any suffix of chunk data words does not touch
`chunks.length`. -/
axiom bytesStoreLiteChunksLengthAfterClearChunkDataSuffix
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex start count : UInt256) :
    bytesStoreLiteChunksLengthWord
        (clearDataWordsForwardFrom I.codeOwner σ
          (start + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩ count.toNat)
        I =
      bytesStoreLiteChunksLengthWord σ I

/-- Trusted keccak disjointness consequence: copying chunk data words does not touch
`chunks.length`. -/
axiom bytesStoreLiteChunksLengthAfterCalldataLongData
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex payloadStart : UInt256) (fuel : Nat) :
    bytesStoreLiteChunksLengthWord
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex)) payloadStart
          (⟨0⟩ : UInt256) I fuel) I =
      bytesStoreLiteChunksLengthWord σ I

/-- Trusted keccak disjointness consequence: the final partial chunk data word does not touch
`chunks.length`. -/
axiom bytesStoreLiteChunksLengthAfterLongDataTail
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex tailWord : UInt256) (fuel : Nat) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase (chunksDataBase + chunkIndex)) fuel)
          tailWord) I =
      bytesStoreLiteChunksLengthWord σ I

theorem bytesStoreLiteChunksLengthAfterSetChunkSlot
    (σ : AccountMap) (I : ExecutionEnv) (header : UInt256) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkSlot I) header) I =
      bytesStoreLiteChunksLengthWord σ I := by
  dsimp [bytesStoreLiteChunksLengthWord, bytesStoreLiteSetChunkSlot]
  exact sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨1⟩
    (chunksDataBase + bytesStoreLiteSetChunkIndexWord I) header
    (by exact (bytesStoreLiteChunksElemSlot_ne_length
      (bytesStoreLiteSetChunkIndexWord I)).symm)

theorem bytesStoreLiteSetChunkStartPlus31_toNat
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 36).toNat) :
    (((⟨4⟩ : UInt256) + calldataWord cd 36) + ⟨31⟩).toNat =
      4 + (calldataWord cd 36).toNat + 31 := by
  have hoffLeMax : (calldataWord cd 36).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord cd 36).toNat < 2 ^ 255 := by
    omega
  have hoffSize : (calldataWord cd 36).toNat < UInt256.size :=
    (calldataWord cd 36).val.isLt
  have hoffOfNat :
      (UInt256.ofNat (calldataWord cd 36).toNat).toNat =
        (calldataWord cd 36).toNat :=
    ulit_toNat' _ hoffSize
  rw [← u256_ofNat_toNat (calldataWord cd 36)]
  simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
    (b := (calldataWord cd 36).toNat)
    (c := 31)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign hoffSmall)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign (by omega : 4 + (calldataWord cd 36).toNat < 2 ^ 255))
    (lt_size_of_lt_sign (by omega :
      4 + (calldataWord cd 36).toNat + 31 < 2 ^ 255)))

theorem bytesStoreLiteSetChunkStart_slt_zero_of_size_high
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 36).toNat)
    (hsize : cd.size < UInt256.size)
    (hsizeSign : ¬ cd.size < 2 ^ 255) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 36) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨0⟩ := by
  have hoffLeMax : (calldataWord cd 36).toNat ≤ ABI.solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  apply BytesStoreLiteCore.slt_zero_of_left_low_right_high
  · rw [bytesStoreLiteSetChunkStartPlus31_toNat cd hoffMax]
    norm_num [ABI.solcMaxU64] at hoffLeMax ⊢
    omega
  · rw [ulit_toNat' cd.size hsize]
    omega

theorem bytesStoreLiteSetChunkStart_slt_zero_of_length_short
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 36).toNat)
    (hsizeSign : cd.size < 2 ^ 255)
    (hlenShort : cd.size < 4 + (calldataWord cd 36).toNat + 32) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 36) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨0⟩ := by
  apply slt_lit_zero hsizeSign
  · rw [bytesStoreLiteSetChunkStartPlus31_toNat cd hoffMax]
    omega
  · rw [bytesStoreLiteSetChunkStartPlus31_toNat cd hoffMax]
    have hoffLe : (calldataWord cd 36).toNat ≤ ABI.solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [ABI.solcMaxU64] at hoffLe ⊢
    omega

theorem bytesStoreLiteSetChunkStart_slt_one
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 36).toNat)
    (hlenWord : 4 + (calldataWord cd 36).toNat + 32 ≤ cd.size)
    (hsizeSign : cd.size < 2 ^ 255) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 36) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨1⟩ := by
  apply slt_lit_one_low hsizeSign
  rw [bytesStoreLiteSetChunkStartPlus31_toNat cd hoffMax]
  omega

theorem bytesStoreLiteSetChunkPayloadShort_size_lt
    (cd : ByteArray)
    (hlenWord : 4 + (calldataWord cd 36).toNat + 32 ≤ cd.size)
    (hpayloadList :
      ((((cd.toList.drop 4).drop ((calldataWord cd 36).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat)) :
    cd.size < 4 + (calldataWord cd 36).toNat + 32 +
      (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat := by
  let off := (calldataWord cd 36).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdropLen :
      ((cd.toList.drop 4).drop (off + 32)).length =
        cd.size - (4 + (off + 32)) := by
    rw [List.drop_drop, List.length_drop, htlen]
  have htakeLen :
      (((cd.toList.drop 4).drop (off + 32)).take n).length =
        min n (cd.size - (4 + (off + 32))) := by
    rw [List.length_take, hdropLen]
  have hltRemain : cd.size - (4 + (off + 32)) < n := by
    by_contra hnot
    have hge : n ≤ cd.size - (4 + (off + 32)) := Nat.le_of_not_gt hnot
    apply hpayloadList
    have : (((cd.toList.drop 4).drop (off + 32)).take n).length = n := by
      rw [htakeLen, min_eq_left hge]
    simpa [off, n] using this
  omega

theorem bytesStoreLiteSetChunkPayloadStartLen_le_of_payload_raw
    (cd : ByteArray)
    (hlenWord : 4 + (calldataWord cd 36).toNat + 32 ≤ cd.size)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 36).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat)) :
    4 + (calldataWord cd 36).toNat + 32 +
      (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat ≤ cd.size := by
  let off := (calldataWord cd 36).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdropLen :
      ((cd.toList.drop 4).drop (off + 32)).length =
        cd.size - (4 + (off + 32)) := by
    rw [List.drop_drop, List.length_drop, htlen]
  have htakeLen :
      (((cd.toList.drop 4).drop (off + 32)).take n).length =
        min n (cd.size - (4 + (off + 32))) := by
    rw [List.length_take, hdropLen]
  have hnLe : n ≤ cd.size - (4 + (off + 32)) := by
    by_contra hnot
    have hlt : cd.size - (4 + (off + 32)) < n := Nat.lt_of_not_ge hnot
    have htakeSmall :
        (((cd.toList.drop 4).drop (off + 32)).take n).length =
          cd.size - (4 + (off + 32)) := by
      rw [htakeLen, min_eq_right (Nat.le_of_lt hlt)]
    rw [htakeSmall] at hpayload
    omega
  omega

theorem bytesStoreLiteSetChunkPayloadWordFull_of_core {cd : ByteArray} {flag : UInt256}
    (hcore :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord cd 36) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (cd.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord cd 36)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat cd.size) = flag) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 36) +
        uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 36)).toNat) 32)) +
        ⟨32⟩))
      (UInt256.ofNat cd.size) = flag := by
  let len : UInt256 :=
    uInt256OfByteArray
      (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 36)).toNat) 32)
  let base : UInt256 := (⟨4⟩ : UInt256) + calldataWord cd 36
  have hmulOne : UInt256.mul len ⟨1⟩ = len := by
    apply u256_inj
    rw [u256_mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by native_decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt len.val.isLt
  have hendEq : (base + ⟨32⟩) + UInt256.mul len ⟨1⟩ = (base + len) + ⟨32⟩ := by
    rw [hmulOne]
    rw [u256_add_assoc base ⟨32⟩ len]
    rw [u256_add_comm (⟨32⟩ : UInt256) len]
    rw [← u256_add_assoc base len ⟨32⟩]
  simpa [base, len, hendEq] using hcore

theorem bytesStoreLiteSetChunkPayloadWord_zero_of_payload
    (I : ExecutionEnv)
    (hsize : I.calldata.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
        ⟨32⟩))
      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
  apply bytesStoreLiteSetChunkPayloadWordFull_of_core
  let off := (calldataWord I.calldata 36).toNat
  let n := (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
  have hpayloadLe :
      4 + off + 32 + n ≤ I.calldata.size := by
    simpa [off, n, Nat.add_assoc] using
      bytesStoreLiteSetChunkPayloadStartLen_le_of_payload_raw I.calldata hlenWord hpayload
  have hnLeMax : n ≤ ABI.solcMaxU64 := by
    simpa [n] using Nat.le_of_not_gt hlenMax
  have hmulToNat :
      (UInt256.mul
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) ⟨1⟩).toNat =
        n := by
    rw [← bytesStoreLiteCalldataWord36_add32 I]
    rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
    rw [u256_mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt (by
      have hmax : ABI.solcMaxU64 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      exact lt_of_le_of_lt hnLeMax hmax)
  have hpayloadEndToNat :
      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) ⟨1⟩)).toNat =
        4 + off + 32 + n := by
    rw [uadd_toNat]
    rw [bytesStoreLiteSetChunkPayloadStart_toNat
      (I := I)
      (payloadStart := (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
      (by rfl) hoffMax]
    rw [hmulToNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hpayloadLe hsize)
  apply ugt_zero
  rw [hpayloadEndToNat, ulit_toNat' I.calldata.size hsize]
  exact hpayloadLe

theorem bytesStoreLiteSetChunkPayloadWord_one_of_payload_short
    (I : ExecutionEnv)
    (hsize : I.calldata.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
        ⟨32⟩))
      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
  apply bytesStoreLiteSetChunkPayloadWordFull_of_core
  let off := (calldataWord I.calldata 36).toNat
  let n := (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
  have hpayloadShortNat :
      I.calldata.size < 4 + off + 32 + n := by
    simpa [off, n, Nat.add_assoc] using
      bytesStoreLiteSetChunkPayloadShort_size_lt I.calldata hlenWord hpayloadList
  have hoffLeMax : off ≤ ABI.solcMaxU64 := by
    simpa [off] using Nat.le_of_not_gt hoffMax
  have hnLeMax : n ≤ ABI.solcMaxU64 := by
    simpa [n] using Nat.le_of_not_gt hlenMax
  have hmulToNat :
      (UInt256.mul
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) ⟨1⟩).toNat =
        n := by
    rw [← bytesStoreLiteCalldataWord36_add32 I]
    rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
    rw [u256_mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt (by
      have hmax : ABI.solcMaxU64 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      exact lt_of_le_of_lt hnLeMax hmax)
  have hpayloadEndToNat :
      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) ⟨1⟩)).toNat =
        4 + off + 32 + n := by
    rw [uadd_toNat]
    rw [bytesStoreLiteSetChunkPayloadStart_toNat
      (I := I)
      (payloadStart := (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
      (by rfl) hoffMax]
    rw [hmulToNat]
    exact Nat.mod_eq_of_lt (by
      apply lt_size_of_lt_sign
      norm_num [ABI.solcMaxU64] at hoffLeMax hnLeMax ⊢
      omega)
  apply ugt_one
  rw [hpayloadEndToNat, ulit_toNat' I.calldata.size hsize]
  exact hpayloadShortNat

theorem bytesStoreLiteSetChunkValueBytes_eq_extract
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    bytesStoreLiteSetChunkValueBytes I =
      I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat) := by
  apply BytesStoreLiteCore.byteArray_eq_of_toList_eq
  rw [bytesStoreLiteSetChunkValueBytes_toList]
  rw [byteArray_toList_eq (I.calldata.extract payloadStart.toNat
    (payloadStart.toNat + len.toNat))]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq I.calldata]
  have hstart :
      payloadStart.toNat = 4 + (calldataWord I.calldata 36).toNat + 32 :=
    bytesStoreLiteSetChunkPayloadStart_toNat
      (I := I) (payloadStart := payloadStart) hpayloadStart hoffMax
  have hlen :
      len.toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
    rw [hlenAbi]
  rw [hstart, hlen]
  rw [List.drop_drop]
  rw [show 4 + ((calldataWord I.calldata 36).toNat + 32) =
      4 + (calldataWord I.calldata 36).toNat + 32 by omega]
  rw [show 4 + (calldataWord I.calldata 36).toNat + 32 +
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat -
        (4 + (calldataWord I.calldata 36).toNat + 32) =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat by omega]

theorem bytesStoreLiteSetChunkValueBytes_readWithPadding_full_word
    {I : ExecutionEnv} {len : UInt256} {i : Nat}
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hi : i < len.toNat / 32) :
    uInt256OfByteArray ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (32 * i) 32) =
      UInt256.ofNat
        (fromBytesBigEndian (((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * i)).take
          32)) := by
  have hread : 32 * i + 32 ≤ (bytesStoreLiteSetChunkValueBytes I).size := by
    rw [hsize]
    have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hsucc
    have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hle := le_trans hmul hdiv
    omega
  rw [uInt256OfByteArray_eq]
  unfold fromByteArrayBigEndian
  rw [readWithPadding_eq_extract _ (32 * i) hread]
  rw [BytesStoreLiteCore.byteArray_extract_toList]
  have hwidth : 32 * i + 32 - 32 * i = 32 := by omega
  simp [hwidth]

theorem bytesStoreLiteSetChunkCalldataLongDataWord_full_word_of_addr
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * i)).toNat = payloadStart.toNat + 32 * i)
    (hread : payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size)
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hdecoded :
      bytesStoreLiteSetChunkValueBytes I =
        I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat))
    (hi : i < len.toNat / 32) :
    bytesStoreLiteCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
      uInt256OfByteArray
        ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (i * 32) 32) := by
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
          ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (i * 32) 32) =
        UInt256.ofNat
          (fromBytesBigEndian
            (((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * i)).take 32)) := by
    simpa [Nat.mul_comm] using
      bytesStoreLiteSetChunkValueBytes_readWithPadding_full_word
        (I := I) (len := len) (i := i) hsize hi
  have hleftList :
      (ByteArray.readBytes I.calldata (payloadStart.toNat + 32 * i) 32).data.toList =
        ((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * i)).take 32 := by
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
            (((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * i)).take 32)) := by
    have hleftToList :
        (ByteArray.readBytes I.calldata (payloadStart.toNat + 32 * i) 32).toList =
          ((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * i)).take 32 := by
      rw [byteArray_toList_eq]
      exact hleftList
    rw [bytesStoreLiteCalldataLongDataWord, BytesStoreLiteCore.longDataWordsLoopStride]
    rw [haddr]
    rw [uInt256OfByteArray_eq]
    unfold fromByteArrayBigEndian
    rw [hleftToList]
  rw [hleft, hwordDirect]

theorem bytesStoreLiteSetChunkCalldataLongDataWord_full_word
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * i)).toNat = payloadStart.toNat + 32 * i)
    (hread : payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size)
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hi : i < len.toNat / 32) :
    bytesStoreLiteCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
      uInt256OfByteArray
        ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (i * 32) 32) := by
  exact bytesStoreLiteSetChunkCalldataLongDataWord_full_word_of_addr
    (I := I) (len := len) (payloadStart := payloadStart) (i := i)
    haddr hread hsize
    (bytesStoreLiteSetChunkValueBytes_eq_extract
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax)
    hi

theorem accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
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
          (bytesStoreLiteSetChunkValueBytes I) i fuel)
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
              ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (i * 32) 32) := by
        exact bytesStoreLiteSetChunkCalldataLongDataWord_full_word
          (I := I) (len := len) (payloadStart := payloadStart) (i := i)
          (haddr i hi) (hread i hi) hsize hlenAbi hpayloadStart hoffMax hi
      have hstrideStep :
          (⟨32⟩ : UInt256) + UInt256.ofNat (32 * i) =
            UInt256.ofNat (32 * (i + 1)) := by
        rw [BytesStoreLiteCore.u256_32_add_ofNat]
        congr 1
      have ih :=
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full
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

theorem accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    {τ : AccountMap} {fuel : Nat}
    (hfuel : fuel ≤ len.toNat / 32) :
    accountMapEquiv
      (solidityDataWordsForwardFrom owner τ baseSlot
        (bytesStoreLiteSetChunkValueBytes I) 0 fuel)
      (bytesStoreLiteCalldataLongDataForwardFrom owner τ
        (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fuel) := by
  have h :=
    accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full
      (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
      (baseSlot := baseSlot) hsize hlenAbi hpayloadStart hoffMax
      (fun j hj => bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
        (payloadStart := payloadStart) (i := j) (haddrBound j hj))
      (fun j hj => bytesStoreLiteCalldataLongDataRead_full_bounds
        (I := I) (len := len) (payloadStart := payloadStart) (i := j) hsrc hj)
      (τ := τ) (i := 0) (fuel := fuel) (by simpa using hfuel)
  have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
  have hslot : bytesLikeDataBase baseSlot + (⟨0⟩ : UInt256) = bytesLikeDataBase baseSlot := by
    exact BytesStoreLiteCore.uint256_add_zero_right (bytesLikeDataBase baseSlot)
  simpa [hslot, hzero] using h

theorem bytesStoreLiteSetChunkValueBytes_readWithPadding_tail_word
    {I : ExecutionEnv} {len : UInt256}
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0) :
    uInt256OfByteArray
        ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (32 * (len.toNat / 32)) 32) =
      UInt256.ofNat
        (fromBytesBigEndian
          (((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((bytesStoreLiteSetChunkValueBytes I).toList.drop
                (32 * (len.toNat / 32))).length) 0)) := by
  have hsize32 : 32 ≤ (bytesStoreLiteSetChunkValueBytes I).size := by
    rw [hsize]
    omega
  have haddr : 32 * (len.toNat / 32) < (bytesStoreLiteSetChunkValueBytes I).size := by
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hrem : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  have htail : (bytesStoreLiteSetChunkValueBytes I).size < 32 * (len.toNat / 32) + 32 := by
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    omega
  rw [uInt256OfByteArray_eq]
  unfold fromByteArrayBigEndian
  rw [BytesStoreLiteCore.readWithPadding_tail32_toList
    (bytesStoreLiteSetChunkValueBytes I) hsize32 haddr htail]

theorem bytesStoreLiteSetChunkValueBytes_tail_length {I : ExecutionEnv} {len : UInt256}
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat) :
    ((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * (len.toNat / 32))).length =
      len.toNat % 32 := by
  rw [List.length_drop]
  have hlist : (bytesStoreLiteSetChunkValueBytes I).toList.length = len.toNat := by
    rw [byteArray_toList_eq (bytesStoreLiteSetChunkValueBytes I), Array.length_toList,
      ByteArray.size_data, hsize]
  rw [hlist]
  have hdiv := Nat.div_add_mod len.toNat 32
  omega

theorem bytesStoreLiteSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0) :
    BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (UInt256.ofNat (32 * (len.toNat / 32))) 0) len =
      uInt256OfByteArray
        ((bytesStoreLiteSetChunkValueBytes I).readWithPadding
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
      bytesStoreLiteSetChunkValueBytes I =
        I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat) :=
    bytesStoreLiteSetChunkValueBytes_eq_extract
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax
  have htailList :
      (I.calldata.data.toList.drop (payloadStart.toNat + 32 * q)).take rem =
        (bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * q) := by
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
            ((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * q) ++
              List.replicate
                (32 - ((bytesStoreLiteSetChunkValueBytes I).toList.drop
                  (32 * q)).length) 0)) := by
    rw [bytesStoreLiteCalldataLongDataWord, BytesStoreLiteCore.longDataWordsLoopStride]
    rw [haddr]
    dsimp [q] at *
    unfold BytesStoreLiteCore.longDataTailMaskedWord
    rw [show UInt256.land len ⟨31⟩ = remWord by rfl]
    rw [hmask]
    have htailLen :
        ((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * q)).length = rem := by
      dsimp [q, rem]
      exact bytesStoreLiteSetChunkValueBytes_tail_length
        (I := I) (len := len) hsize
    have hpad := uInt256OfByteArray_readBytes_at_high_mask_eq_padded I.calldata
      (payloadStart.toNat + 32 * q) rem hremLt hsrcTail
    simpa [q, htailList, htailLen] using hpad
  have hright :
      uInt256OfByteArray
          ((bytesStoreLiteSetChunkValueBytes I).readWithPadding
            (32 * (len.toNat / 32)) 32) =
        UInt256.ofNat
          (fromBytesBigEndian
            ((bytesStoreLiteSetChunkValueBytes I).toList.drop (32 * q) ++
              List.replicate
                (32 - ((bytesStoreLiteSetChunkValueBytes I).toList.drop
                  (32 * q)).length) 0)) := by
    dsimp [q]
    exact bytesStoreLiteSetChunkValueBytes_readWithPadding_tail_word
      (I := I) (len := len) hsize hlong hmod
  rw [hleft, hright]

set_option maxHeartbeats 1200000 in
theorem accountMapEquiv_setChunkLongTailDataStorage
    {I : ExecutionEnv} {len payloadStart : UInt256}
    {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      (solidityDataWordsForwardFrom I.codeOwner σ_solm (bytesStoreLiteSetChunkSlot I)
        (bytesStoreLiteSetChunkValueBytes I) 0
        (solidityBytesDataWordCount (bytesStoreLiteSetChunkValueBytes I).size)) := by
  let baseSlot : UInt256 := bytesStoreLiteSetChunkSlot I
  let fullFuel : Nat := len.toNat / 32
  have hdataFuelEq :
      solidityBytesDataWordCount (bytesStoreLiteSetChunkValueBytes I).size =
        fullFuel + 1 := by
    unfold solidityBytesDataWordCount
    dsimp [fullFuel]
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  have hbridgeEvm :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot
          (bytesStoreLiteSetChunkValueBytes I) 0 fullFuel)
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
    exact accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
      (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := σ_evm) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
  have hcong :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot
          (bytesStoreLiteSetChunkValueBytes I) 0 fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
          (bytesStoreLiteSetChunkValueBytes I) 0 fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom
      (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
      (baseSlot := baseSlot) (bytes := bytesStoreLiteSetChunkValueBytes I)
      (idx := 0) fullFuel hAccounts
  have hdataFull :
      accountMapEquiv
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
          (bytesStoreLiteSetChunkValueBytes I) 0 fullFuel) :=
    accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
  have htailWord :
      BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len =
        uInt256OfByteArray
          ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (fullFuel * 32) 32) := by
    simpa [fullFuel, Nat.mul_comm] using
      bytesStoreLiteSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
        (I := I) (len := len) (payloadStart := payloadStart)
        htailAddr hsrc hsize hlenAbi hpayloadStart hoffMax hlong hmod
  have hslotEq :
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
        solidityBytesDataSlot baseSlot fullFuel := by
    exact bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
  have htailStore :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len))
        (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
          (bytesStoreLiteSetChunkValueBytes I) 0 (fullFuel + 1)) := by
    have hsplit :
        solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
            (bytesStoreLiteSetChunkValueBytes I) 0 (fullFuel + 1) =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
              (bytesStoreLiteSetChunkValueBytes I) 0 fullFuel)
            (solidityBytesDataSlot baseSlot fullFuel)
            (uInt256OfByteArray
              ((bytesStoreLiteSetChunkValueBytes I).readWithPadding (fullFuel * 32) 32)) := by
      have happ := solidityDataWordsForwardFrom_append I.codeOwner σ_solm baseSlot
        (bytesStoreLiteSetChunkValueBytes I) 0 fullFuel 1
      rw [happ]
      simp [solidityDataWordsForwardFrom]
    rw [hsplit]
    simpa [hslotEq, htailWord] using
      accountMapEquiv_sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        hdataFull
  simpa [baseSlot, fullFuel, hdataFuelEq,
    bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using htailStore

theorem bytesStoreLiteSetChunkLengthAfterShortStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {len payloadStart : UInt256} {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetChunkSlot I) storedWord
    readStorageBytesLength? bytesStoreLiteConfig evmData
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetChunkSlot I) storedWord
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreLiteSetChunkIndexWord I).toNat : Int)) =
          some (bytesStoreLiteSetChunkSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteSetChunkSlot,
      u256_ofNat_toNat]
  have hheader :
      ((evmData.accountMap.find? I.codeOwner).option (default : UInt256)
          (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I)
            (default : UInt256))) = storedWord := by
    have hbeq : (storedWord == (default : UInt256)) = false := by
      simpa [storedWord] using
        bytesStoreLiteSetChunkShortStoredWord_beq_zero_false
          (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simp [evmData, storageStore_accountMap]
    unfold sstoreAccountMap
    simp [hacc, hbeq, Option.option, accountMap_find_insert_self,
      storage_findD_insert_self]
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord] using
          bytesStoreLiteSetChunkShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord] using
          bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord] using
            bytesStoreLiteSetChunkShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  simp [readStorageBytesLength?, bytesStoreLiteConfig,
    bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
    bytesStoreLiteLayout, bytesStoreLiteSetChunkRefOf, hslotChunk, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, storageStore_executionEnv, howner]
  change storageNatResultToEval
      (solidityDecodeBytesLengthHeader
        ((evmData.accountMap.find? I.codeOwner).option (default : UInt256)
          (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I)
            (default : UInt256)))) = .ok len.toNat
  rw [hheader]
  rw [hdecode]
  rfl

theorem bytesStoreLiteSetChunkLengthAfterEmptyStoreOfState
    {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩
    readStorageBytesLength? bytesStoreLiteConfig evmData
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) = .ok 0 := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreLiteSetChunkIndexWord I).toNat : Int)) =
          some (bytesStoreLiteSetChunkSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteSetChunkSlot,
      u256_ofNat_toNat]
  have hheader :
      ((evmData.accountMap.find? I.codeOwner).option (default : UInt256)
          (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I)
            (default : UInt256))) = ⟨0⟩ := by
    simp [evmData, storageStore_accountMap]
    unfold sstoreAccountMap
    cases hacc : evm.accountMap.find? I.codeOwner with
    | none =>
        simp [hacc, Option.option]
        rfl
    | some acc =>
        have hzero : ((⟨0⟩ : UInt256) = (default : UInt256)) := rfl
        simp [Option.option, accountMap_find_insert_self, hzero, storage_findD_erase_self]
  simp [readStorageBytesLength?, bytesStoreLiteConfig,
    bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
    bytesStoreLiteLayout, bytesStoreLiteSetChunkRefOf, hslotChunk, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, storageStore_executionEnv, howner]
  change storageNatResultToEval
      (solidityDecodeBytesLengthHeader
        ((evmData.accountMap.find? I.codeOwner).option (default : UInt256)
          (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I)
            (default : UInt256)))) = .ok 0
  rw [hheader]
  rfl

theorem bytesStoreLiteSetChunkLengthAfterLongStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {len header : UInt256} {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
      (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetChunkSlot I) header
    readStorageBytesLength? bytesStoreLiteConfig evmData
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) = .ok len.toNat := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetChunkSlot I) header
  have hslotChunk :
      chunksElemSlot?
        (.int ((bytesStoreLiteSetChunkIndexWord I).toNat : Int)) =
          some (bytesStoreLiteSetChunkSlot I) := by
    simp [chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteSetChunkSlot,
      u256_ofNat_toNat]
  have hheaderLoad :
      ((evmData.accountMap.find? I.codeOwner).option (default : UInt256)
          (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I)
            (default : UInt256))) = header := by
    have hbeq : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      exact hflag (by rw [hzero]; native_decide)
    simp [evmData, storageStore_accountMap]
    unfold sstoreAccountMap
    simp [hacc, hbeq, Option.option, accountMap_find_insert_self,
      storage_findD_insert_self]
  have hdecode :
      solidityDecodeBytesLengthHeader header = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_long_valid
      (header := header) (len := len) hflag hlen (by simpa [← hlen] using hvalid)
  simp [readStorageBytesLength?, bytesStoreLiteConfig,
    bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
    bytesStoreLiteLayout, bytesStoreLiteSetChunkRefOf, hslotChunk, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, storageStore_executionEnv, howner]
  change storageNatResultToEval
      (solidityDecodeBytesLengthHeader
        ((evmData.accountMap.find? I.codeOwner).option (default : UInt256)
          (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I)
            (default : UInt256)))) = .ok len.toNat
  rw [hheaderLoad, hdecode]
  rfl

theorem bytesStoreLiteSetChunkWriteShortOldLongPrepared
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len oldStoredLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩) :
    let value := bytesStoreLiteSetChunkValueBytes I
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
      (bytesStoreLiteSetChunkSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
    let evmData := Solm.EVM.storageStore evmClear I.codeOwner
      (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord value)
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
      (.bytes value) = .ok evmData := by
  dsimp only
  let value := bytesStoreLiteSetChunkValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetChunkSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner
    (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord value)
  have hvalueSize : value.size < 32 := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayload, ← hlenAbi]
    exact hshort
  have hword :
      bytesStoreLiteSetChunkHeaderWord σ_evm I =
        bytesStoreLiteSetChunkHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetChunkHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkSlot I) =
        bytesStoreLiteSetChunkHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteSetChunkHeaderWord, hslot]
  have hwrite := bytesStoreLiteWriteChunkShortFromLongPrepared
    (evm := evmSolm0)
    (oldLen := bytesStoreLiteSetChunkIndexWord I)
    (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
    (len := oldStoredLen)
    (value := value)
    hvalueSize
    (by simpa [bytesStoreLiteSetChunkSlot] using hload)
    hflag holdStoredLen hvalid
  simpa [evmSolm0, evmClear, evmData, value, bytesStoreLiteSetChunkRefOf,
    bytesStoreLiteSetChunkSlot, clearSolidityBytesDataWordsFrom_executionEnv]
    using hwrite

theorem bytesStoreLiteSetChunkWriteLongOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreLiteSetChunkValueBytes I
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
      (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I) value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreLiteSetChunkSlot I) (solidityBytesHeaderWord value.size)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreLiteSetChunkValueBytes I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : ¬ value.size < 32 := by
    rw [show value.size = len.toNat by
      dsimp [value]
      rw [bytesStoreLiteSetChunkValueBytes_size hpayload, ← hlenAbi]]
    exact hlong
  have hword :
      bytesStoreLiteSetChunkHeaderWord σ_evm I =
        bytesStoreLiteSetChunkHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetChunkHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkSlot I) =
        bytesStoreLiteSetChunkHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteSetChunkHeaderWord, hslot]
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := bytesStoreLiteWriteChunkLongPacked (evm := evmSolm0)
    (oldLen := bytesStoreLiteSetChunkIndexWord I)
    (header := bytesStoreLiteSetChunkHeaderWord σ_evm I) (len := oldLen)
    (value := value)
    hvalueSize
    (by simpa [bytesStoreLiteSetChunkSlot] using hload)
    (by simpa [bytesStoreLiteSetChunkSlot] using hpacked)
    hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, value, bytesStoreLiteSetChunkRefOf, bytesStoreLiteSetChunkSlot]
    using hwrite

theorem bytesStoreLiteSetChunkWriteLongOldLongPrepared
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len oldStoredLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreLiteSetChunkValueBytes I
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
      (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldStoredLen.toNat -
                solidityBytesDataWordCount value.size))
            (bytesStoreLiteSetChunkSlot I) value 0 (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldStoredLen.toNat -
                solidityBytesDataWordCount value.size))
            (bytesStoreLiteSetChunkSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreLiteSetChunkSlot I) (solidityBytesHeaderWord value.size)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreLiteSetChunkValueBytes I
  have hvalueSize : ¬ value.size < 32 := by
    rw [show value.size = len.toNat by
      dsimp [value]
      rw [bytesStoreLiteSetChunkValueBytes_size hpayload, ← hlenAbi]]
    exact hlong
  have hword :
      bytesStoreLiteSetChunkHeaderWord σ_evm I =
        bytesStoreLiteSetChunkHeaderWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I) ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I) ⟨0⟩)) := by
    simpa [bytesStoreLiteSetChunkHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkSlot I) =
        bytesStoreLiteSetChunkHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteSetChunkHeaderWord, hslot]
  have hwrite := bytesStoreLiteWriteChunkLongFromLongPrepared (evm := evmSolm0)
    (oldLen := bytesStoreLiteSetChunkIndexWord I)
    (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
    (len := oldStoredLen)
    (value := value)
    hvalueSize
    (by simpa [bytesStoreLiteSetChunkSlot] using hload)
    hflag holdStoredLen hvalid
  simpa [evmSolm0, value, bytesStoreLiteSetChunkRefOf, bytesStoreLiteSetChunkSlot,
    clearSolidityBytesDataWordsFrom_executionEnv]
    using hwrite

theorem bytesStoreLiteX_setChunkLongNoTailOldShortWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  have hbranch := bytesStoreLiteX_setChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound hlenMax hflag hvalid
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkLongTailOldShortWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  have hbranch := bytesStoreLiteX_setChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound hlenMax hflag hvalid
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkLongHeaderNoClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hdecoder := bytesStoreLiteX_setChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) hreach hbound hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header, slot] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, slot, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩,
      len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header, slot] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩, slot,
          ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩,
        slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header, slot] using hflag)
      (by simpa [header, slot] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  simpa [slot] using
    bytesStoreLiteX_writeBytesCleanupOldLongNoClear
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
      (len := len) (ret := ⟨2643⟩)
      (tail := [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
      (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
      hcleanupReach holdLong hgtOldNew (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkLongNoTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  have hbranch := bytesStoreLiteX_setChunkLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hreach hbound hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkLongTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  have hbranch := bytesStoreLiteX_setChunkLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hreach hbound hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkLongHeaderClearReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)) =
        ⟨0⟩) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hdecoder := bytesStoreLiteX_setChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) hreach hbound hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header, slot] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, slot, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩,
      len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header, slot] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩, slot,
          ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩,
        slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header, slot] using hflag)
      (by simpa [header, slot] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hlongWord : UInt256.lt len ⟨32⟩ = ⟨0⟩ :=
    ult_zero (by
      have hle : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hle)
  have hloopEntry := bytesStoreLiteX_writeBytesCleanupOldLongLongToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
      chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hcleanupReach holdLong hgtOldNew hlongWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))
    (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
      chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [slot] using hloop

theorem bytesStoreLiteX_setChunkLongHeaderClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
    (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreLiteX_setChunkLongHeaderClearReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hbound hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
      hcontinue hdone

theorem bytesStoreLiteX_setChunkLongNoTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
      (BytesStoreLiteCore.clearCurrentHashAw
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreLiteX_setChunkLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [slot, σClear] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkLongTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
      (BytesStoreLiteCore.clearCurrentHashAw
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreLiteX_setChunkLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [slot, σClear] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteSetChunkEmptyFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (bytesStoreLiteSetChunkSlot I) ⟨0⟩)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (bytesStoreLiteSetChunkSlot I) 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩).accountMap := by
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hstored : (⟨0⟩ : UInt256) = solidityShortBytesWord ByteArray.empty := hshortEmpty.symm
  simpa [initState, hshortEmpty] using
    bytesStoreLiteSetChunkShortFromLongPostAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (oldLen := oldLen) (storedWord := (⟨0⟩ : UInt256))
      (value := ByteArray.empty) hAccounts hstored holdLenLt

theorem bytesStoreLiteX_setChunkReturnLengthDecoderOldLongFrom1194
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1194⟩
      [bytesStoreLiteChunksLengthWord σ I, chunkIndex, ⟨1⟩, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (bytesStoreLiteSetChunkOldLongBodyMem slot) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
        ⟨1002⟩, chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (bytesStoreLiteSetChunkOldLongReturnMem slot) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1194⟩ := hreach
  have hlt : UInt256.lt chunkIndex (bytesStoreLiteChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd1207 := evm_run rd1194 with [
    dup2, lt, push2 ⟨1207⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have hslotHash :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((bytesStoreLiteSetChunkOldLongReturnMem slot).readWithPadding 0 32))) =
        chunksDataBase := by
    dsimp [bytesStoreLiteSetChunkOldLongReturnMem, bytesStoreLiteSetChunkOldLongBodyMem]
    rw [wordAt0Mem_read0]
    simpa [chunksDataBase, bytesLikeDataBase]
      using keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))
  have rd1214 := evm_run rd1207 with [
    jumpdest, swap1, push0,
    raw mstore 0
      (bytesStoreLiteSetChunkOldLongReturnMem slot)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by
        dsimp [bytesStoreLiteSetChunkOldLongReturnMem,
          bytesStoreLiteSetChunkOldLongBodyMem]
        rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 chunksDataBase (UInt256.ofNat 3)
      (by native_decide) mem_cost hslotHash
      (by native_decide) (by evm_ov),
    add, dup1]
  obtain ⟨_, _, rd1218₀⟩ := rd1214.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1218⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1218⟩
        [(σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
          chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
          bytesStoreLiteSelWord I]
        (bytesStoreLiteSetChunkOldLongReturnMem slot) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [initState] using rd1218₀⟩
  exact ⟨_, _, evm_run rd1218 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setChunkReachReturnLengthDecoderOldLong
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (bytesStoreLiteSetChunkOldLongBodyMem slot) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
        ⟨1002⟩, chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (bytesStoreLiteSetChunkOldLongReturnMem slot) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1187⟩ := hreach
  have rd1193 := evm_run rd1187 with [
    jumpdest, pop, push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1194₀⟩ := rd1193.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1194⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1194⟩
        [bytesStoreLiteChunksLengthWord σ I, chunkIndex, ⟨1⟩, ⟨0⟩, len, payloadStart,
          chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
        (bytesStoreLiteSetChunkOldLongBodyMem slot) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1194₀⟩
  exact bytesStoreLiteX_setChunkReturnLengthDecoderOldLongFrom1194
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (chunkIndex := chunkIndex) ⟨_, _, rd1194⟩ hbound

theorem bytesStoreLiteX_setChunkReachReturnLengthDecoderFromMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart chunkIndex : UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      mem (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
      ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
        ⟨1002⟩, chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1187⟩ := hreach
  have rd1193 := evm_run rd1187 with [
    jumpdest, pop, push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1194₀⟩ := rd1193.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1194⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1194⟩
        [bytesStoreLiteChunksLengthWord σ I, chunkIndex, ⟨1⟩, ⟨0⟩, len, payloadStart,
          chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
        mem (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1194₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreLiteChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd1207 := evm_run rd1194 with [
    dup2, lt, push2 ⟨1207⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have hslotHash :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((wordAt0Mem (⟨1⟩ : UInt256) mem).readWithPadding 0 32))) =
        chunksDataBase := by
    rw [wordAt0Mem_read0]
    simpa [chunksDataBase, bytesLikeDataBase]
      using keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))
  have rd1214 := evm_run rd1207 with [
    jumpdest, swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256) mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 chunksDataBase
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
      (by native_decide) mem_cost hslotHash
      (by native_decide) (by evm_ov),
    add, dup1]
  obtain ⟨_, _, rd1218₀⟩ := rd1214.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1218⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1218⟩
        [(σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
          chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
          bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) mem)
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [initState] using rd1218₀⟩
  exact ⟨_, _, evm_run rd1218 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setChunkLongNoTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (chunksDataBase + chunkIndex)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 :=
    ((σData.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hbody := bytesStoreLiteX_setChunkLongNoTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hperm hreach hbound hlenMaxWord hflag hvalid hlong hnoTailMod
  have hchunksLoop :
      bytesStoreLiteChunksLengthWord σLoop I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σLoop, slot] using
      bytesStoreLiteChunksLengthAfterCalldataLongData σ I chunkIndex payloadStart
        (len.toNat / 32)
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σData I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksLoop]
    dsimp [σData, bytesStoreLiteChunksLengthWord, slot]
    exact sstoreAccountMap_storage_findD_ne σLoop I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) header
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σData I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (by simpa [σLoop, σData, slot, header] using hbody) hbound'
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256)))) = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, slot, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        (chunksDataBase + chunkIndex) header
        (by simpa [σLoop, slot] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, slot] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, slot] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)
        (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setChunkLongTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (chunksDataBase + chunkIndex)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (BytesStoreLiteCore.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 :=
    ((σData.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hbody := bytesStoreLiteX_setChunkLongTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hperm hreach hbound hlenMaxWord hflag hvalid hlong htailMod
  have hchunksLoop :
      bytesStoreLiteChunksLengthWord σLoop I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σLoop, slot] using
      bytesStoreLiteChunksLengthAfterCalldataLongData σ I chunkIndex payloadStart
        (len.toNat / 32)
  have hchunksTail :
      bytesStoreLiteChunksLengthWord σTail I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksLoop]
    simpa [σTail, tailSlot, tailWord, slot] using
      bytesStoreLiteChunksLengthAfterLongDataTail σLoop I chunkIndex tailWord
        (len.toNat / 32)
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σData I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksTail]
    dsimp [σData, bytesStoreLiteChunksLengthWord, slot]
    exact sstoreAccountMap_storage_findD_ne σTail I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) header
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σData I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header] using hbody)
    hbound'
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256)))) = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, tailSlot, tailWord, slot, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        (chunksDataBase + chunkIndex) header
        (by simpa [σTail, σLoop, tailSlot, tailWord, slot] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, slot] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, slot] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)
        (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setChunkLongNoTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (chunksDataBase + chunkIndex)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 :=
    ((σData.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hbody := bytesStoreLiteX_setChunkLongNoTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  have hchunksLoop :
      bytesStoreLiteChunksLengthWord σLoop I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σLoop, slot] using
      bytesStoreLiteChunksLengthAfterCalldataLongData σ I chunkIndex payloadStart
        (len.toNat / 32)
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σData I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksLoop]
    dsimp [σData, bytesStoreLiteChunksLengthWord, slot]
    exact sstoreAccountMap_storage_findD_ne σLoop I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) header
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σData I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (by simpa [σLoop, σData, slot, header] using hbody) hbound'
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256)))) = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, slot, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        (chunksDataBase + chunkIndex) header
        (by simpa [σLoop, slot] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, slot] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, slot] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)
        (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setChunkLongTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (chunksDataBase + chunkIndex)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (BytesStoreLiteCore.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 :=
    ((σData.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hbody := bytesStoreLiteX_setChunkLongTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  have hchunksLoop :
      bytesStoreLiteChunksLengthWord σLoop I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σLoop, slot] using
      bytesStoreLiteChunksLengthAfterCalldataLongData σ I chunkIndex payloadStart
        (len.toNat / 32)
  have hchunksTail :
      bytesStoreLiteChunksLengthWord σTail I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksLoop]
    simpa [σTail, tailSlot, tailWord, slot] using
      bytesStoreLiteChunksLengthAfterLongDataTail σLoop I chunkIndex tailWord
        (len.toNat / 32)
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σData I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksTail]
    dsimp [σData, bytesStoreLiteChunksLengthWord, slot]
    exact sstoreAccountMap_storage_findD_ne σTail I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) header
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σData I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header] using hbody)
    hbound'
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256)))) = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, tailSlot, tailWord, slot, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        (chunksDataBase + chunkIndex) header
        (by simpa [σTail, σLoop, tailSlot, tailWord, slot] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, slot] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, slot] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)
        (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setChunkLongNoTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
            bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
        (bytesLikeDataBase (chunksDataBase + chunkIndex)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let start : UInt256 := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩
  let count : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ (start + bytesLikeDataBase slot) ⟨0⟩ count.toNat
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 :=
    ((σData.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hbody := bytesStoreLiteX_setChunkLongNoTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  have hchunksClear :
      bytesStoreLiteChunksLengthWord σClear I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σClear, start, count, slot] using
      bytesStoreLiteChunksLengthAfterClearChunkDataSuffix σ I chunkIndex start count
  have hchunksLoop :
      bytesStoreLiteChunksLengthWord σLoop I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksClear]
    simpa [σLoop, slot] using
      bytesStoreLiteChunksLengthAfterCalldataLongData σClear I chunkIndex payloadStart
        (len.toNat / 32)
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σData I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksLoop]
    dsimp [σData, bytesStoreLiteChunksLengthWord, slot]
    exact sstoreAccountMap_storage_findD_ne σLoop I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) header
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σData I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem slot
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by
      simpa [σClear, σLoop, σData, slot, header, start, count,
        BytesStoreLiteCore.clearCurrentHashAw] using hbody)
    hbound'
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256)))) = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, σClear, slot, header, start, count] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        (chunksDataBase + chunkIndex) header
        (by simpa [σLoop, σClear, slot, start, count] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, slot] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot
        (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, slot] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot
        (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot
        (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)
          (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setChunkLongTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
              bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
            (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
              (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
          (bytesLikeDataBase (chunksDataBase + chunkIndex)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (chunksDataBase + chunkIndex)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (BytesStoreLiteCore.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let start : UInt256 := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩
  let count : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ (start + bytesLikeDataBase slot) ⟨0⟩ count.toNat
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 :=
    ((σData.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hbody := bytesStoreLiteX_setChunkLongTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  have hchunksClear :
      bytesStoreLiteChunksLengthWord σClear I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σClear, start, count, slot] using
      bytesStoreLiteChunksLengthAfterClearChunkDataSuffix σ I chunkIndex start count
  have hchunksLoop :
      bytesStoreLiteChunksLengthWord σLoop I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksClear]
    simpa [σLoop, slot] using
      bytesStoreLiteChunksLengthAfterCalldataLongData σClear I chunkIndex payloadStart
        (len.toNat / 32)
  have hchunksTail :
      bytesStoreLiteChunksLengthWord σTail I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksLoop]
    simpa [σTail, tailSlot, tailWord, slot] using
      bytesStoreLiteChunksLengthAfterLongDataTail σLoop I chunkIndex tailWord
        (len.toNat / 32)
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σData I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksTail]
    dsimp [σData, bytesStoreLiteChunksLengthWord, slot]
    exact sstoreAccountMap_storage_findD_ne σTail I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) header
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σData I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem slot
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by
      simpa [σClear, σLoop, tailSlot, tailWord, σTail, σData, slot, header,
        start, count, BytesStoreLiteCore.clearCurrentHashAw] using hbody)
    hbound'
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256)))) = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, σClear, tailSlot, tailWord, slot, header,
      start, count] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        (chunksDataBase + chunkIndex) header
        (by simpa [σTail, σLoop, σClear, tailSlot, tailWord, slot, start, count]
          using haccTail)
        hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, slot] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot
        (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, slot] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot
        (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem slot
        (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)
          (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongNoTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag :
      UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreLiteSetChunkSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σLoop, bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkLongNoTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (acc := accLoop)
        hperm hreach hboundChunk hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hlong hnoTailMod
        (by simpa [σLoop, bytesStoreLiteSetChunkSlot, hchunkIndex] using haccLoop)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetChunkWriteLongOldShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header] using hwrite₀
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    unfold solidityBytesDataWordCount
    rw [hsizeDecoded]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreLiteSetChunkSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreLiteSetChunkSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := bytesStoreLiteSetChunkSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    have hAccountsData :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner σLoop (bytesStoreLiteSetChunkSlot I)
            (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          evmData.accountMap := by
      simpa [evmData, evmLoop, hheaderEq, storageStore_accountMap,
        writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using
        accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetChunkSlot I)
          header hAccountsLoop
    simpa [σFinal] using hAccountsData
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hloop := bytesStoreLiteChunksLengthAfterCalldataLongData
      σ_evm I (bytesStoreLiteSetChunkIndexWord I) payloadStart (len.toNat / 32)
    have hstore :
        bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σLoop I := by
      simpa [σFinal] using
        bytesStoreLiteChunksLengthAfterSetChunkSlot σLoop I
          (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    rw [hstore]
    simpa [σLoop, bytesStoreLiteSetChunkSlot] using hloop
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmLoop, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    simpa [evmData, evmLoop, evmSolm0, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, initState, bytesStoreLiteChunksLengthWord]
      using hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag :
      UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreLiteSetChunkSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
      using
      bytesStoreLiteX_setChunkLongTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (acc := accTail)
        hperm hreach hboundChunk hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hlong htailMod
        (by simpa [σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using haccTail)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetChunkWriteLongOldShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header] using hwrite₀
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    unfold solidityBytesDataWordCount
    rw [hsizeDecoded]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailMod
    omega
  have hdataFuelCount :
      solidityBytesDataWordCount (bytesStoreLiteSetChunkValueBytes I).size =
        len.toNat / 32 + 1 := by
    simpa [dataFuel, value] using hdataFuelEq
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    have hbridge := accountMapEquiv_setChunkLongTailDataStorage
      (I := I) (len := len) (payloadStart := payloadStart)
      (σ_evm := σ_evm) (σ_solm := σ_solm)
      hAccounts hsrc haddrBound htailAddr hsizeDecoded hlenAbi hpayloadStart
      hoffMax hlong htailMod
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      hdataFuelEq, hdataFuelCount, writeSolidityBytesDataWordsFrom_accountMap] using hbridge
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetChunkSlot I)
        header hAccountsTail
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using hlen₀
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hloop := bytesStoreLiteChunksLengthAfterCalldataLongData
      σ_evm I (bytesStoreLiteSetChunkIndexWord I) payloadStart (len.toNat / 32)
    have htail := bytesStoreLiteChunksLengthAfterLongDataTail
      σLoop I (bytesStoreLiteSetChunkIndexWord I) tailWord (len.toNat / 32)
    have hstore := bytesStoreLiteChunksLengthAfterSetChunkSlot σTail I
      (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    rw [show bytesStoreLiteChunksLengthWord σFinal I =
        bytesStoreLiteChunksLengthWord σTail I by simpa [σFinal] using hstore]
    rw [show bytesStoreLiteChunksLengthWord σTail I =
        bytesStoreLiteChunksLengthWord σLoop I by
          simpa [σTail, tailSlot, tailWord, bytesStoreLiteSetChunkSlot] using htail]
    simpa [σLoop, bytesStoreLiteSetChunkSlot] using hloop
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmLoop, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    simpa [evmData, evmLoop, evmSolm0, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, initState, bytesStoreLiteChunksLengthWord]
      using hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongNoTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreLiteSetChunkSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σLoop, bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkLongNoTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen) (acc := accLoop)
        hperm hreach hboundChunk hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using holdStoredLen)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hgtOldNew hlong hnoTailMod
        (by simpa [σLoop, bytesStoreLiteSetChunkSlot, hchunkIndex] using haccLoop)
  have hOldLeLen : oldStoredLen.toNat ≤ len.toNat := by
    by_contra hle
    have hone : UInt256.gt oldStoredLen len = ⟨1⟩ :=
      ugt_one (Nat.lt_of_not_ge hle)
    rw [hone] at hgtOldNew
    have hbad : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by native_decide
    exact hbad hgtOldNew
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    unfold solidityBytesDataWordCount
    rw [hsizeDecoded]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hclearCountZero :
      solidityBytesDataWordCount oldStoredLen.toNat -
          solidityBytesDataWordCount value.size = 0 := by
    have hcountLe :
        solidityBytesDataWordCount oldStoredLen.toNat ≤
          solidityBytesDataWordCount value.size := by
      unfold solidityBytesDataWordCount
      rw [hsizeDecoded]
      exact BytesStoreLiteCore.nat_ceil32_le_ceil32 hOldLeLen
    exact Nat.sub_eq_zero_of_le hcountLe
  have hdataCountEq : solidityBytesDataWordCount value.size = len.toNat / 32 := by
    simpa [dataFuel] using hdataFuelEq
  have hclearCountZeroLen :
      solidityBytesDataWordCount oldStoredLen.toNat - len.toNat / 32 = 0 := by
    simpa [hdataCountEq] using hclearCountZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetChunkWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq] using hwrite₀
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreLiteSetChunkSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreLiteSetChunkSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := bytesStoreLiteSetChunkSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetChunkSlot I)
        header hAccountsLoop
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hloop := bytesStoreLiteChunksLengthAfterCalldataLongData
      σ_evm I (bytesStoreLiteSetChunkIndexWord I) payloadStart (len.toNat / 32)
    have hstore := bytesStoreLiteChunksLengthAfterSetChunkSlot σLoop I
      (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    rw [show bytesStoreLiteChunksLengthWord σFinal I =
        bytesStoreLiteChunksLengthWord σLoop I by simpa [σFinal] using hstore]
    simpa [σLoop, bytesStoreLiteSetChunkSlot] using hloop
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmLoop, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    simpa [evmData, evmLoop, evmSolm0, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, initState, bytesStoreLiteChunksLengthWord]
      using hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreLiteSetChunkSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetChunkSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
      using
      bytesStoreLiteX_setChunkLongTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen) (acc := accTail)
        hperm hreach hboundChunk hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using holdStoredLen)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hgtOldNew hlong htailMod
        (by simpa [σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using haccTail)
  have hOldLeLen : oldStoredLen.toNat ≤ len.toNat := by
    by_contra hle
    have hone : UInt256.gt oldStoredLen len = ⟨1⟩ :=
      ugt_one (Nat.lt_of_not_ge hle)
    rw [hone] at hgtOldNew
    have hbad : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by native_decide
    exact hbad hgtOldNew
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    unfold solidityBytesDataWordCount
    rw [hsizeDecoded]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailMod
    omega
  have hclearCountZero :
      solidityBytesDataWordCount oldStoredLen.toNat -
          solidityBytesDataWordCount value.size = 0 := by
    have hcountLe :
        solidityBytesDataWordCount oldStoredLen.toNat ≤
          solidityBytesDataWordCount value.size := by
      unfold solidityBytesDataWordCount
      rw [hsizeDecoded]
      exact BytesStoreLiteCore.nat_ceil32_le_ceil32 hOldLeLen
    exact Nat.sub_eq_zero_of_le hcountLe
  have hdataCountEq :
      solidityBytesDataWordCount value.size = len.toNat / 32 + 1 := by
    simpa [dataFuel] using hdataFuelEq
  have hclearCountZeroLen :
      solidityBytesDataWordCount oldStoredLen.toNat - (len.toNat / 32 + 1) = 0 := by
    simpa [hdataCountEq] using hclearCountZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetChunkWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq] using hwrite₀
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    have hbridge := accountMapEquiv_setChunkLongTailDataStorage
      (I := I) (len := len) (payloadStart := payloadStart)
      (σ_evm := σ_evm) (σ_solm := σ_solm)
      hAccounts hsrc haddrBound htailAddr hsizeDecoded hlenAbi hpayloadStart
      hoffMax hlong htailMod
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      hdataFuelEq, hdataCountEq, writeSolidityBytesDataWordsFrom_accountMap] using hbridge
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetChunkSlot I)
        header hAccountsTail
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using hlen₀
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hloop := bytesStoreLiteChunksLengthAfterCalldataLongData
      σ_evm I (bytesStoreLiteSetChunkIndexWord I) payloadStart (len.toNat / 32)
    have htail := bytesStoreLiteChunksLengthAfterLongDataTail
      σLoop I (bytesStoreLiteSetChunkIndexWord I) tailWord (len.toNat / 32)
    have hstore := bytesStoreLiteChunksLengthAfterSetChunkSlot σTail I
      (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    rw [show bytesStoreLiteChunksLengthWord σFinal I =
        bytesStoreLiteChunksLengthWord σTail I by simpa [σFinal] using hstore]
    rw [show bytesStoreLiteChunksLengthWord σTail I =
        bytesStoreLiteChunksLengthWord σLoop I by
          simpa [σTail, tailSlot, tailWord, bytesStoreLiteSetChunkSlot] using htail]
    simpa [σLoop, bytesStoreLiteSetChunkSlot] using hloop
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmLoop, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    simpa [evmData, evmLoop, evmSolm0, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv, initState, bytesStoreLiteChunksLengthWord]
      using hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongNoTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let oldFuel : Nat := (oldStoredLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let tailFuel : Nat := oldFuel - clearFuel
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreLiteSetChunkSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetChunkSlot I) clearFuel tailFuel
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmClear (bytesStoreLiteSetChunkSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  have holdGtNat : len.toNat < oldStoredLen.toNat :=
    BytesStoreLiteCore.ugt_eq_one_toNat_lt hgtOldNew
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    unfold solidityBytesDataWordCount
    rw [hsizeDecoded]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hclearFuelEq : clearFuel = len.toNat / 32 := by
    rw [hclearFuelCeil]
    exact BytesStoreLiteCore.nat_ceil32_eq_div_of_mod_zero hnoTailMod
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact BytesStoreLiteCore.nat_ceil32_le_ceil32 (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMax
  have hnewShiftEq :
      UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ = UInt256.ofNat clearFuel := by
    apply u256_inj
    rw [hnewShiftClear]
    exact (ulit_toNat' clearFuel (by
      have hlt : clearFuel < 2 ^ 251 := by
        rw [hclearFuelCeil]
        apply Nat.div_lt_of_lt_mul
        have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
          norm_num [ABI.solcMaxU64]
        omega
      have hsize' : (2 : Nat) ^ 251 < UInt256.size := by
        norm_num [UInt256.size]
      omega)).symm
  have holdShiftNat :
      (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign (x := oldStoredLen) holdLenLt
  have hcountNat : clearCount.toNat = tailFuel := by
    dsimp [clearCount, tailFuel]
    rw [usub_toNat]
    · rw [holdShiftNat, hnewShiftClear]
    · rw [holdShiftNat, hnewShiftClear]
      exact hclearLeOld
  have hcountNatShift :
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewShiftEq]
    simpa [clearCount] using hcountNat
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetChunkSlot I))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I)
      (by simpa [σClear, clearCount] using haccClear) (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σLoop, σClear, clearCount, bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkLongNoTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen) (acc := accLoop)
        hperm hreach hboundChunk hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using holdStoredLen)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hgtOldNew hlong hnoTailMod
        (by simpa [σLoop, σClear, clearCount, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using haccLoop)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetChunkWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount] using hwrite₀
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := bytesStoreLiteSetChunkSlot I) clearFuel (⟨0⟩ : UInt256) tailFuel
      hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I))]
      using hshift
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreLiteSetChunkSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreLiteSetChunkSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σClear) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (bytesStoreLiteSetChunkSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner evmClear.accountMap
            (bytesStoreLiteSetChunkSlot I) value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σClear) (σ := evmClear.accountMap)
        (baseSlot := bytesStoreLiteSetChunkSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccountsClear
    simpa [evmLoop, evmClear, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv, initState, hdataFuelEq] using
      accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState, header] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetChunkSlot I)
        header hAccountsLoop
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hclear := bytesStoreLiteChunksLengthAfterClearChunkDataSuffix
      σ_evm I (bytesStoreLiteSetChunkIndexWord I)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩) clearCount
    have hloop := bytesStoreLiteChunksLengthAfterCalldataLongData
      σClear I (bytesStoreLiteSetChunkIndexWord I) payloadStart (len.toNat / 32)
    have hstore := bytesStoreLiteChunksLengthAfterSetChunkSlot σLoop I
      (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    rw [show bytesStoreLiteChunksLengthWord σFinal I =
        bytesStoreLiteChunksLengthWord σLoop I by simpa [σFinal] using hstore]
    have hloop' :
        bytesStoreLiteChunksLengthWord σLoop I =
          bytesStoreLiteChunksLengthWord σClear I := by
      simpa [σLoop, bytesStoreLiteSetChunkSlot] using hloop
    rw [hloop']
    simpa [σClear, clearCount, bytesStoreLiteSetChunkSlot] using hclear
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmLoop, evmClear, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    simpa [evmData, evmLoop, evmClear, evmSolm0, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, initState, bytesStoreLiteChunksLengthWord]
      using hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmClear, evmSolm0,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let oldFuel : Nat := (oldStoredLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let tailFuel : Nat := oldFuel - clearFuel
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreLiteSetChunkSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetChunkSlot I) clearFuel tailFuel
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmClear (bytesStoreLiteSetChunkSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  have holdGtNat : len.toNat < oldStoredLen.toNat :=
    BytesStoreLiteCore.ugt_eq_one_toNat_lt hgtOldNew
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    unfold solidityBytesDataWordCount
    rw [hsizeDecoded]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailMod
    omega
  have hdataCountEq :
      solidityBytesDataWordCount (bytesStoreLiteSetChunkValueBytes I).size =
        len.toNat / 32 + 1 := by
    simpa [dataFuel, value] using hdataFuelEq
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact BytesStoreLiteCore.nat_ceil32_le_ceil32 (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMax
  have hnewShiftEq :
      UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ = UInt256.ofNat clearFuel := by
    apply u256_inj
    rw [hnewShiftClear]
    exact (ulit_toNat' clearFuel (by
      have hlt : clearFuel < 2 ^ 251 := by
        rw [hclearFuelCeil]
        apply Nat.div_lt_of_lt_mul
        have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
          norm_num [ABI.solcMaxU64]
        omega
      have hsize' : (2 : Nat) ^ 251 < UInt256.size := by
        norm_num [UInt256.size]
      omega)).symm
  have holdShiftNat :
      (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign (x := oldStoredLen) holdLenLt
  have hcountNat : clearCount.toNat = tailFuel := by
    dsimp [clearCount, tailFuel]
    rw [usub_toNat]
    · rw [holdShiftNat, hnewShiftClear]
    · rw [holdShiftNat, hnewShiftClear]
      exact hclearLeOld
  have hcountNatShift :
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewShiftEq]
    simpa [clearCount] using hcountNat
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetChunkSlot I))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I)
      (by simpa [σClear, clearCount] using haccClear) (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord)
      (by simpa [σLoop, σClear, clearCount] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σTail, σLoop, σClear, clearCount, tailSlot, tailWord,
      bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkLongTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen) (acc := accTail)
        hperm hreach hboundChunk hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using holdStoredLen)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hgtOldNew hlong htailMod
        (by simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord,
          bytesStoreLiteSetChunkSlot, hchunkIndex] using haccTail)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetChunkWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount] using hwrite₀
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := bytesStoreLiteSetChunkSlot I) clearFuel (⟨0⟩ : UInt256) tailFuel
      hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (bytesStoreLiteSetChunkSlot I))]
      using hshift
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    have hbridge := accountMapEquiv_setChunkLongTailDataStorage
      (I := I) (len := len) (payloadStart := payloadStart)
      (σ_evm := σClear) (σ_solm := evmClear.accountMap)
      hAccountsClear hsrc haddrBound htailAddr hsizeDecoded hlenAbi hpayloadStart
      hoffMax hlong htailMod
    simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord, evmLoop, evmClear,
      evmSolm0, initState, value, hdataFuelEq, hdataCountEq,
      writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv] using hbridge
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState, header] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetChunkSlot I)
        header hAccountsTail
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState] using hlen₀
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hclear := bytesStoreLiteChunksLengthAfterClearChunkDataSuffix
      σ_evm I (bytesStoreLiteSetChunkIndexWord I)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩) clearCount
    have hloop := bytesStoreLiteChunksLengthAfterCalldataLongData
      σClear I (bytesStoreLiteSetChunkIndexWord I) payloadStart (len.toNat / 32)
    have htail := bytesStoreLiteChunksLengthAfterLongDataTail
      σLoop I (bytesStoreLiteSetChunkIndexWord I) tailWord (len.toNat / 32)
    have hstore := bytesStoreLiteChunksLengthAfterSetChunkSlot σTail I
      (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    rw [show bytesStoreLiteChunksLengthWord σFinal I =
        bytesStoreLiteChunksLengthWord σTail I by simpa [σFinal] using hstore]
    rw [show bytesStoreLiteChunksLengthWord σTail I =
        bytesStoreLiteChunksLengthWord σLoop I by
          simpa [σTail, tailSlot, tailWord, bytesStoreLiteSetChunkSlot] using htail]
    have hloop' :
        bytesStoreLiteChunksLengthWord σLoop I =
          bytesStoreLiteChunksLengthWord σClear I := by
      simpa [σLoop, bytesStoreLiteSetChunkSlot] using hloop
    rw [hloop']
    simpa [σClear, clearCount, bytesStoreLiteSetChunkSlot] using hclear
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmLoop, evmClear, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    simpa [evmData, evmLoop, evmClear, evmSolm0, storageStore_accountMap,
      writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_accountMap,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, initState, bytesStoreLiteChunksLengthWord]
      using hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmClear, evmSolm0,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

theorem bytesStoreLiteX_setChunkShortNonemptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (haccClear :
      (clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat).find?
          I.codeOwner = some acc) :
    let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
    let σClear :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σClear (chunksDataBase + chunkIndex) storedWord
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray len) := by
  dsimp only
  let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σClear (chunksDataBase + chunkIndex) storedWord
  let header : UInt256 :=
    σ'.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)
  have hbody := bytesStoreLiteX_setChunkShortNonemptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hnz hshort
  have hchunksPreserveClear :
      bytesStoreLiteChunksLengthWord σClear I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σClear] using
      bytesStoreLiteChunksLengthAfterClearChunkData σ I chunkIndex oldStoredLen
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σ' I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksPreserveClear]
    dsimp [σ', bytesStoreLiteChunksLengthWord]
    exact sstoreAccountMap_storage_findD_ne σClear I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) storedWord
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ' I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have haw3 :
      BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3) = UInt256.ofNat 3 :=
    BytesStoreLiteCore.clearCurrentHashAw_eq_self_of_ge1 (by native_decide)
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderOldLong
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (by
      dsimp [bytesStoreLiteSetChunkOldLongBodyMem]
      simpa [σClear, σ', storedWord, haw3] using hbody)
    hbound'
  have hdata :
      (σ'.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) =
        storedWord := by
    have hnzStored := bytesStoreLiteSetChunkShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simpa [σ', storedWord] using
      sstoreAccountMap_storage_findD_self_of_find_some σClear I.codeOwner acc
        (chunksDataBase + chunkIndex) storedWord
        (by simpa [σClear] using haccClear) hnzStored
  have hheader : header = storedWord := by
    simpa [header] using hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    exact bytesStoreLiteSetChunkShortStoredWord_flag_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader,
      bytesStoreLiteSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := bytesStoreLiteSetChunkOldLongReturnMem (chunksDataBase + chunkIndex))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    exact bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len)
    (slot := chunksDataBase + chunkIndex) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex)
    (mem := bytesStoreLiteSetChunkOldLongReturnMem (chunksDataBase + chunkIndex))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := bytesStoreLiteSetChunkOldLongReturnMem (chunksDataBase + chunkIndex))
    (by
      dsimp [bytesStoreLiteSetChunkOldLongReturnMem, bytesStoreLiteSetChunkOldLongBodyMem]
      exact wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
    (by
      dsimp [bytesStoreLiteSetChunkOldLongReturnMem, bytesStoreLiteSetChunkOldLongBodyMem]
      exact bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)
          (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)))
    h263

theorem bytesStoreLiteX_setChunkEmptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σClear :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σClear (chunksDataBase + chunkIndex) ⟨0⟩
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  dsimp only
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σClear (chunksDataBase + chunkIndex) ⟨0⟩
  have hbody := bytesStoreLiteX_setChunkEmptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hlenZero
  have hchunksPreserveClear :
      bytesStoreLiteChunksLengthWord σClear I = bytesStoreLiteChunksLengthWord σ I := by
    simpa [σClear] using
      bytesStoreLiteChunksLengthAfterClearChunkData σ I chunkIndex oldStoredLen
  have hchunksPreserve :
      bytesStoreLiteChunksLengthWord σ' I = bytesStoreLiteChunksLengthWord σ I := by
    rw [← hchunksPreserveClear]
    dsimp [σ', bytesStoreLiteChunksLengthWord]
    exact sstoreAccountMap_storage_findD_ne σClear I.codeOwner ⟨1⟩
      (chunksDataBase + chunkIndex) ⟨0⟩
      (by exact (bytesStoreLiteChunksElemSlot_ne_length chunkIndex).symm)
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ' I).toNat := by
    rw [hchunksPreserve]
    exact hbound
  have haw3 :
      BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3) = UInt256.ofNat 3 :=
    BytesStoreLiteCore.clearCurrentHashAw_eq_self_of_ge1 (by native_decide)
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoderOldLong
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (by
      dsimp [bytesStoreLiteSetChunkOldLongBodyMem]
      simpa [σClear, σ', haw3] using hbody)
    hbound'
  have hheader :
      (σ'.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) = ⟨0⟩ := by
    simpa [σ'] using bytesStoreLiteSetChunkEmptyHeaderAfterWrite σClear I chunkIndex
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := bytesStoreLiteSetChunkOldLongReturnMem (chunksDataBase + chunkIndex))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := (⟨0⟩ : UInt256))
    (slot := chunksDataBase + chunkIndex) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex)
    (mem := bytesStoreLiteSetChunkOldLongReturnMem (chunksDataBase + chunkIndex))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := (⟨0⟩ : UInt256))
    (mem := bytesStoreLiteSetChunkOldLongReturnMem (chunksDataBase + chunkIndex))
    (by
      dsimp [bytesStoreLiteSetChunkOldLongReturnMem, bytesStoreLiteSetChunkOldLongBodyMem]
      exact wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
    (by
      dsimp [bytesStoreLiteSetChunkOldLongReturnMem, bytesStoreLiteSetChunkOldLongBodyMem]
      exact bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)
          (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)))
    h263

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkShortNonemptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal := sstoreAccountMap I.codeOwner σClear
    (bytesStoreLiteSetChunkSlot I) storedWord
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetChunkSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner
    (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord value)
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)))
      (idx := ⟨0⟩) haccEvm
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σClear, storedWord, bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkShortNonemptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen) (acc := accClear)
        hperm hreach hboundChunk hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using holdStoredLen)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hnz hshort
        (by simpa [σClear, bytesStoreLiteSetChunkSlot, hchunkIndex] using haccClear)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    simpa [evmSolm0, evmClear, evmData, value] using
      bytesStoreLiteSetChunkWriteShortOldLongPrepared
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        (oldStoredLen := oldStoredLen)
        hAccounts hpayloadList hlenAbi hshort hflag holdStoredLen hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using
      bytesStoreLiteSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  obtain ⟨accSolmClear, haccSolmClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_solm) (owner := I.codeOwner) (acc := accSolm)
      (base := solidityBytesDataBaseSlot (bytesStoreLiteSetChunkSlot I))
      (idx := UInt256.ofNat 0) haccSolm ((oldStoredLen.toNat + 31) / 32)
  have haccEvmClear :
      evmClear.accountMap.find? I.codeOwner = some accSolmClear := by
    simpa [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_accountMap]
      using haccSolmClear
  have hvalueSize : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterShortStoreOfState
      (evm := evmClear) (I := I) (len := len) (payloadStart := payloadStart)
      (acc := accSolmClear)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
      haccEvmClear hnz hshort
    simpa [evmClear, evmData, storedWord, hstored, hvalueSize] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, σClear, evmData, evmClear, evmSolm0, value, storedWord, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreLiteSetChunkShortFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) (storedWord := storedWord) (value := value)
        hAccounts hstored holdLenLt
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hclear := bytesStoreLiteChunksLengthAfterClearChunkData
      σ_evm I (bytesStoreLiteSetChunkIndexWord I) oldStoredLen
    have hstore :
        bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σClear I := by
      dsimp [σFinal, bytesStoreLiteChunksLengthWord]
      exact sstoreAccountMap_storage_findD_ne σClear I.codeOwner ⟨1⟩
        (bytesStoreLiteSetChunkSlot I) storedWord
        (by exact (bytesStoreLiteChunksElemSlot_ne_length
          (bytesStoreLiteSetChunkIndexWord I)).symm)
    rw [hstore]
    simpa [σClear, bytesStoreLiteSetChunkSlot] using hclear
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmClear, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    exact hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmClear, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hvalueSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkEmptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetChunkLocals I))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal := sstoreAccountMap I.codeOwner σClear (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetChunkSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, σClear, bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkEmptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen)
        hperm hreach hboundChunk hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using holdStoredLen)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hlenZero
  have hvalueSize0 : value.size = 0 := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, hlenZeroAbi]
    rfl
  have hvalueEmpty : value = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero value hvalueSize0
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmData := by
    have hshort : len.toNat < 32 := by
      rw [hlenZero]
      native_decide
    have hwrite₀ := bytesStoreLiteSetChunkWriteShortOldLongPrepared
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        (oldStoredLen := oldStoredLen)
        hAccounts hpayloadList (by rw [hlenZero, hlenZeroAbi]) hshort
        hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmData, value, hvalueEmpty, hshortEmpty] using hwrite₀
  have hchunksWord :
      bytesStoreLiteChunksLengthWord σ_evm I =
        bytesStoreLiteChunksLengthWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hchunksSlot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) := by
    simpa [bytesStoreLiteChunksLengthWord] using hchunksWord.symm
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, bytesStoreLiteChunksLengthWord, hchunksSlot]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) = .ok 0 := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterEmptyStoreOfState
      (evm := evmClear) (I := I)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
    simpa [evmClear, evmData] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, σClear, evmData, evmClear, evmSolm0, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreLiteSetChunkEmptyFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) hAccounts holdLenLt
  have hchunksFinal :
      bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σ_evm I := by
    have hclear := bytesStoreLiteChunksLengthAfterClearChunkData
      σ_evm I (bytesStoreLiteSetChunkIndexWord I) oldStoredLen
    have hstore :
        bytesStoreLiteChunksLengthWord σFinal I = bytesStoreLiteChunksLengthWord σClear I := by
      dsimp [σFinal, bytesStoreLiteChunksLengthWord]
      exact sstoreAccountMap_storage_findD_ne σClear I.codeOwner ⟨1⟩
        (bytesStoreLiteSetChunkSlot I) ⟨0⟩
        (by exact (bytesStoreLiteChunksElemSlot_ne_length
          (bytesStoreLiteSetChunkIndexWord I)).symm)
    rw [hstore]
    simpa [σClear, bytesStoreLiteSetChunkSlot] using hclear
  have hloadAfter :
      Solm.EVM.storageLoad evmData evmData.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    have hwordPost :
        bytesStoreLiteChunksLengthWord σFinal I =
          bytesStoreLiteChunksLengthWord evmData.accountMap I :=
      accountMapEquiv_storage_findD hAccountsPost I.codeOwner ⟨1⟩ ⟨0⟩
    simp [evmData, evmClear, evmSolm0, Solm.EVM.storageLoad, initState,
      State.lookupAccount, Account.lookupStorage, storageStore_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, bytesStoreLiteChunksLengthWord]
    exact hwordPost.symm.trans hchunksFinal
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmData (some (.int 0))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmData)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := 0)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
        evmData (some (.int 0)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmClear, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkShortNonemptyOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let chunkIndex : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreLiteX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreLiteSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  exact bytesStoreLiteSetChunkShortNonemptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen) (accEvm := accEvm)
    hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen hbound
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    hnzLen hshortLen

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkEmptyOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let chunkIndex : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreLiteX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_gt_max I hoffMax hlenMaxAbiWord
  have hlenZeroLen : len = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_zero I hoffMax hlenZero
  have hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreLiteSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  exact bytesStoreLiteSetChunkEmptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts hreach hchunkIndex hd hdec hpayloadList hlenMaxLen
    hbound hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    hlenZeroLen hlenZero

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongNoTailOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let chunkIndex : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreLiteX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hlenMaxNat : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreLiteSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  exact bytesStoreLiteSetChunkLongNoTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec hlenAbi
    hpayloadStart hoffMax hsrc haddrBound hpayloadList hlenMaxLen hlenMaxNat hbound
    hflag hvalid hlongLen (by simpa [hlenAbi] using hnoTailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongTailOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let chunkIndex : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreLiteX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hlenMaxNat : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreLiteSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddrBound :
      payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
    have htailModLen : len.toNat % 32 ≠ 0 := by
      simpa [hlenAbi] using htailMod
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
    have hdiv := Nat.div_add_mod len.toNat 32
    have hltLen : 32 * (len.toNat / 32) < len.toNat := by
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32) :=
    bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
  exact bytesStoreLiteSetChunkLongTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec hlenAbi
    hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
    hbound hflag hvalid hlongLen (by simpa [hlenAbi] using htailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let chunkIndex : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreLiteX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hlenMaxNat : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreLiteSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  by_cases hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩
  · by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
    · exact bytesStoreLiteSetChunkLongNoTailOldLongClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound hpayloadList hlenMaxLen hlenMaxNat hbound
        hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew hlongLen (by simpa [hlenAbi] using hnoTailMod)
    · have htailAddrBound :
        payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
        have htailModLen : len.toNat % 32 ≠ 0 := by
          simpa [hlenAbi] using hnoTailMod
        have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
        have hdiv := Nat.div_add_mod len.toNat 32
        have hltLen : 32 * (len.toNat / 32) < len.toNat := by
          omega
        exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
      have htailAddr :
          (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
            payloadStart.toNat + 32 * (len.toNat / 32) :=
        bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
          (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
      exact bytesStoreLiteSetChunkLongTailOldLongClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
        hbound hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew hlongLen (by simpa [hlenAbi] using hnoTailMod)
  · have hgtOldNew0 : UInt256.gt oldStoredLen len = ⟨0⟩ := by
      by_cases hle : oldStoredLen.toNat ≤ len.toNat
      · exact ugt_zero hle
      · exact False.elim (hgtOldNew (ugt_one (Nat.lt_of_not_ge hle)))
    by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
    · exact bytesStoreLiteSetChunkLongNoTailOldLongNoClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound hpayloadList hlenMaxLen hlenMaxNat hbound
        hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew0 hlongLen (by simpa [hlenAbi] using hnoTailMod)
    · have htailAddrBound :
        payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
        have htailModLen : len.toNat % 32 ≠ 0 := by
          simpa [hlenAbi] using hnoTailMod
        have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
        have hdiv := Nat.div_add_mod len.toNat 32
        have hltLen : 32 * (len.toNat / 32) < len.toNat := by
          omega
        exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
      have htailAddr :
          (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
            payloadStart.toNat + 32 * (len.toNat / 32) :=
        bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
          (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
      exact bytesStoreLiteSetChunkLongTailOldLongNoClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
        hbound hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew0 hlongLen (by simpa [hlenAbi] using hnoTailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkLongNewRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat
  · obtain ⟨accEvm, haccEvm⟩ :=
      bytesStoreLiteSetChunkAccountExistsOfBound
        (σ := σ_evm) (I := I) hbound
    by_cases hflagShort : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalidShort :
        UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
              ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
      · by_cases hnoTailMod :
          (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
        · exact bytesStoreLiteSetChunkLongNoTailOldShortRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
            hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
            hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound
            hflagShort hvalidShort hnewLong hnoTailMod
        · exact bytesStoreLiteSetChunkLongTailOldShortRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
            hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
            hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound
            hflagShort hvalidShort hnewLong hnoTailMod
      · exact bytesStoreLiteSetChunkShortMalformedRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflagShort
          (not_ne_iff.mp hvalidShort)
    · have hflagLong :
        UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := hflagShort
      by_cases hvalidLong :
        UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreLiteSetChunkLongOldLongRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
          hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
          hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound
          hflagLong hvalidLong hnewLong
      · exact bytesStoreLiteSetChunkLongMalformedRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflagLong
          (not_ne_iff.mp hvalidLong)
  · exact bytesStoreLiteSetChunkOobRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkShortNewRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat
  · by_cases hflagShort : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalidShort :
        UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
              ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreLiteSetChunkShortOldShortRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflagShort
          hvalidShort hshort
      · exact bytesStoreLiteSetChunkShortMalformedRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflagShort
          (not_ne_iff.mp hvalidShort)
    · have hflagLong :
        UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := hflagShort
      by_cases hvalidLong :
        UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · by_cases hzero :
          calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩
        · exact bytesStoreLiteSetChunkEmptyOldLongRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
            hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflagLong
            hvalidLong hzero
        · have hnz :
            (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠
              0 := by
            intro hnat
            apply hzero
            apply u256_inj
            rw [hnat]
            native_decide
          obtain ⟨accEvm, haccEvm⟩ :=
            bytesStoreLiteSetChunkAccountExistsOfBound
              (σ := σ_evm) (I := I) hbound
          exact bytesStoreLiteSetChunkShortNonemptyOldLongRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
            hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
            hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound
            hflagLong hvalidLong hnz hshort
      · exact bytesStoreLiteSetChunkLongMalformedRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflagLong
          (not_ne_iff.mp hvalidLong)
  · exact bytesStoreLiteSetChunkOobRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound

theorem bytesStoreLiteSetChunkDecodeTotalHighRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk_none_totalHuge (I := I)
    (Nat.le_of_not_gt hsizeHigh)
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    bytesStoreLiteSetChunkStart_slt_zero_of_size_high I.calldata hoffMax hsize hsizeHigh
  exact (bytesStoreLiteX_setChunkDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart)
    |>.reEquivDecodingFailed hcode hd hdec

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkDecodedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32
  · exact bytesStoreLiteSetChunkShortNewRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hshort
  · exact bytesStoreLiteSetChunkLongNewRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hshort

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 68
  · exact bytesStoreLiteSetChunkDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hshort
  · have hsz68 : 68 ≤ I.calldata.size := Nat.le_of_not_gt hshort
    by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact bytesStoreLiteSetChunkDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hbig
    · have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hbig
      by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat
      · exact bytesStoreLiteSetChunkDecodeOffsetHugeRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoff
      · have hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat := hoff
        by_cases hsizeSign : I.calldata.size < 2 ^ 255
        · by_cases hlenShort :
            I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32
          · have hstart :
                UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
              bytesStoreLiteSetChunkStart_slt_zero_of_length_short
                I.calldata hoffMax hsizeSign hlenShort
            exact bytesStoreLiteSetChunkDecodeLengthShortRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
              hlenShort hstart
          · have hlenWord :
              4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size :=
              Nat.le_of_not_gt hlenShort
            have hstart :
                UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
              bytesStoreLiteSetChunkStart_slt_one I.calldata hoffMax hlenWord hsizeSign
            by_cases hlenHuge :
                ABI.solcMaxU64 <
                  (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
            · have hlenMaxWord :
                  UInt256.gt
                      (uInt256OfByteArray
                        (I.calldata.readBytes
                          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
                      ⟨18446744073709551615⟩ = ⟨1⟩ := by
                rw [← bytesStoreLiteCalldataWord36_add32 I]
                rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
                apply ugt_one
                rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
                    ABI.solcMaxU64 by native_decide]
                exact hlenHuge
              exact bytesStoreLiteSetChunkDecodeLengthHugeRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                hlenWord hlenHuge hstart hlenMaxWord
            · by_cases hpayloadList :
                ((((I.calldata.toList.drop 4).drop
                  ((calldataWord I.calldata 36).toNat + 32)).take
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 36).toNat)).toNat)
              · have hlenMaxWord :
                    UInt256.gt
                        (uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
                        ⟨18446744073709551615⟩ = ⟨0⟩ := by
                  rw [← bytesStoreLiteCalldataWord36_add32 I]
                  rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
                  apply ugt_zero
                  rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
                      ABI.solcMaxU64 by native_decide]
                  exact Nat.le_of_not_gt hlenHuge
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                  bytesStoreLiteSetChunkPayloadWord_zero_of_payload
                    I hsize hoffMax hlenWord hlenHuge hpayloadList
                exact bytesStoreLiteSetChunkDecodedRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign
                  hoffMax hlenWord hlenHuge hpayloadList hstart hlenMaxWord hpayloadWord
              · have hpayloadListNe :
                  ((((I.calldata.toList.drop 4).drop
                    ((calldataWord I.calldata 36).toNat + 32)).take
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 36).toNat)).toNat).length ≠
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 36).toNat)).toNat) := hpayloadList
                have hlenMaxWord :
                    UInt256.gt
                        (uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
                        ⟨18446744073709551615⟩ = ⟨0⟩ := by
                  rw [← bytesStoreLiteCalldataWord36_add32 I]
                  rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
                  apply ugt_zero
                  rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
                      ABI.solcMaxU64 by native_decide]
                  exact Nat.le_of_not_gt hlenHuge
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
                  bytesStoreLiteSetChunkPayloadWord_one_of_payload_short
                    I hsize hoffMax hlenWord hlenHuge hpayloadListNe
                exact bytesStoreLiteSetChunkDecodePayloadShortRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                  hlenWord hlenHuge hpayloadListNe hstart hlenMaxWord hpayloadWord
        · exact bytesStoreLiteSetChunkDecodeTotalHighRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoffMax hsizeSign

end BytesStoreLite
