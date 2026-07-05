import Examples.BytesStore.FullSetPacket

/-!
# BytesStore — `setChunk(uint256,bytes)` runtime slice

This module starts the full-contract `setChunk(uint256,bytes)` selector arm.  The first layer pins
the mixed static/dynamic ABI decoding facts used by both `setChunk` and the analogous mapped bytes
setter.
-/

namespace BytesStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

def bytesStoreSetChunkIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreSetChunkValueBytes (I : ExecutionEnv) : ByteArray :=
  ByteArray.mk
    ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).toArray)

theorem bytesStoreSetChunkValueBytes_toList {I : ExecutionEnv} :
    (bytesStoreSetChunkValueBytes I).toList =
      (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) := by
  simp [bytesStoreSetChunkValueBytes, byteArray_toList_eq]

theorem bytesStoreSetChunkValueBytes_size {I : ExecutionEnv}
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    (bytesStoreSetChunkValueBytes I).size =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
  let payload :=
    (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
  change payload.toArray.size =
    (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
  rw [show payload.toArray.size = payload.length by simp]
  simpa [payload] using hpayload

@[simp] theorem bytesStoreCalldataWord36_add32 (I : ExecutionEnv) :
    uInt256OfByteArray
      (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) =
        calldataWord I.calldata 36 := by
  have h : (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) = 36 := by
    native_decide
  simp [calldataWord, h]

theorem bytesStoreSetChunkRawLengthWord_eq (I : ExecutionEnv)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32) =
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
  rw [bytesStoreCalldataWord36_add32]
  rw [calldataWord]
  have haddr :
      (((⟨4⟩ : UInt256) + calldataWord I.calldata 36).toNat) =
        4 + (calldataWord I.calldata 36).toNat := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by native_decide]
    rw [Nat.mod_eq_of_lt]
    have hoffLe : (calldataWord I.calldata 36).toNat ≤ ABI.solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    have hroom : 4 + ABI.solcMaxU64 < UInt256.size := by native_decide
    omega
  rw [haddr]

theorem bytesStoreSetChunkRawLengthWord_gt_max
    (I : ExecutionEnv)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenMax :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
        ⟨18446744073709551615⟩ = ⟨0⟩) :
    UInt256.gt
        (uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
            32))
        ⟨18446744073709551615⟩ = ⟨0⟩ := by
  rw [bytesStoreSetChunkRawLengthWord_eq I hoffMax]
  exact hlenMax

theorem bytesStoreSetChunkRawLengthWord_zero
    (I : ExecutionEnv)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    uInt256OfByteArray
        (I.calldata.readBytes
          (((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
          32) = ⟨0⟩ := by
  rw [bytesStoreSetChunkRawLengthWord_eq I hoffMax]
  exact hlenZero

def bytesStoreSetChunkShortStoredWord (I : ExecutionEnv)
    (len payloadStart : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
    (UInt256.land
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
      (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))

theorem bytesStoreSetChunkShortStoredWord_flag_eq {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    UInt256.land (bytesStoreSetChunkShortStoredWord I len payloadStart) ⟨1⟩ =
      ⟨0⟩ := by
  simpa [bytesStoreSetChunkShortStoredWord, bytesStoreSetPacketShortStoredWord] using
    bytesStoreSetPacketShortStoredWord_flag_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort

theorem bytesStoreSetChunkShortStoredWord_shortLen_eq {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    UInt256.land
        (UInt256.div (bytesStoreSetChunkShortStoredWord I len payloadStart) ⟨2⟩)
        ⟨127⟩ = len := by
  simpa [bytesStoreSetChunkShortStoredWord, bytesStoreSetPacketShortStoredWord] using
    bytesStoreSetPacketShortStoredWord_shortLen_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort

theorem bytesStoreSetChunkShortStoredWord_beq_zero_false {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    (bytesStoreSetChunkShortStoredWord I len payloadStart == (default : UInt256)) =
      false := by
  simpa [bytesStoreSetChunkShortStoredWord, bytesStoreSetPacketShortStoredWord] using
    bytesStoreSetPacketShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort

theorem bytesStoreSetChunkPayloadStart_toNat {I : ExecutionEnv} {payloadStart : UInt256}
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    payloadStart.toNat = 4 + (calldataWord I.calldata 36).toNat + 32 := by
  rw [hpayloadStart]
  rw [uadd_toNat, uadd_toNat]
  rw [show (⟨4⟩ : UInt256).toNat = 4 by native_decide]
  rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
  have hoffLe : (calldataWord I.calldata 36).toNat ≤ ABI.solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  have hinner : 4 + (calldataWord I.calldata 36).toNat < UInt256.size := by
    have hroom : 4 + ABI.solcMaxU64 < UInt256.size := by native_decide
    omega
  have houter : 4 + (calldataWord I.calldata 36).toNat + 32 < UInt256.size := by
    have hroom : 4 + ABI.solcMaxU64 + 32 < UInt256.size := by native_decide
    omega
  rw [Nat.mod_eq_of_lt hinner, Nat.mod_eq_of_lt houter]

theorem bytesStoreSetChunkShortValueReadWithPadding_toList {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    ((bytesStoreSetChunkValueBytes I).readWithPadding 0 32).toList =
      (I.calldata.toList.drop payloadStart.toNat).take len.toNat ++
        List.replicate (32 - len.toNat) 0 := by
  have hsize :
      (bytesStoreSetChunkValueBytes I).size = len.toNat := by
    rw [bytesStoreSetChunkValueBytes_size hpayload, ← hlenAbi]
  rw [readWithPadding_zero_toList_of_size_lt32
    (bytesStoreSetChunkValueBytes I)
    (by rw [hsize]; exact hnz)
    (by rw [hsize]; exact hshort)]
  rw [hsize]
  rw [bytesStoreSetChunkValueBytes_toList]
  rw [← hlenAbi]
  have hpayloadNat :=
    bytesStoreSetChunkPayloadStart_toNat
      (I := I) (payloadStart := payloadStart) hpayloadStart hoffMax
  rw [hpayloadNat]
  rw [List.drop_drop]
  rw [show 4 + ((calldataWord I.calldata 36).toNat + 32) =
      4 + (calldataWord I.calldata 36).toNat + 32 by omega]

theorem bytesStoreSetChunkPayloadStartLen_le_of_payload {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hnz : len.toNat ≠ 0)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    payloadStart.toNat + len.toNat ≤ I.calldata.size := by
  have hpayloadNat :=
    bytesStoreSetChunkPayloadStart_toNat
      (I := I) (payloadStart := payloadStart) hpayloadStart hoffMax
  have htake :
      len.toNat ≤ ((I.calldata.toList.drop 4).drop
        ((calldataWord I.calldata 36).toNat + 32)).length := by
    rw [← hlenAbi] at hpayload
    rw [List.length_take] at hpayload
    by_contra hle
    have hlt :
        ((I.calldata.toList.drop 4).drop
          ((calldataWord I.calldata 36).toNat + 32)).length < len.toNat :=
      Nat.lt_of_not_ge hle
    rw [Nat.min_eq_right (Nat.le_of_lt hlt)] at hpayload
    omega
  rw [List.length_drop, List.length_drop] at htake
  have hcdLen : I.calldata.toList.length = I.calldata.size := by
    simp [byteArray_toList_eq]
  rw [hcdLen] at htake
  rw [Nat.sub_sub] at htake
  have hlenPos : 0 < len.toNat := Nat.pos_of_ne_zero hnz
  have hdropPos :
      0 < I.calldata.size - (4 + ((calldataWord I.calldata 36).toNat + 32)) :=
    lt_of_lt_of_le hlenPos htake
  have hdropBase :
      4 + ((calldataWord I.calldata 36).toNat + 32) ≤ I.calldata.size := by
    omega
  rw [Nat.le_sub_iff_add_le hdropBase] at htake
  rw [hpayloadNat]
  omega

theorem bytesStoreSetChunkShortPayloadMaskedCallDataWord_eq_decodedWord
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    UInt256.land
        (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32))
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ len))) =
      uInt256OfByteArray
        ((bytesStoreSetChunkValueBytes I).readWithPadding 0 32) := by
  rw [StringStoreLite.setShortPackedHeader_mask_of_short hshort]
  rw [uInt256OfByteArray_readBytes_at_high_mask_eq_padded
    I.calldata payloadStart.toNat len.toNat hshort hsrc]
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq]
  rw [← byteArray_toList_eq
    ((bytesStoreSetChunkValueBytes I).readWithPadding 0 32)]
  rw [bytesStoreSetChunkShortValueReadWithPadding_toList
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hpayload]
  rw [byteArray_toList_eq]

theorem bytesStoreSetChunkShortStoredWord_eq_solidityShortBytesWord
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    bytesStoreSetChunkShortStoredWord I len payloadStart =
      solidityShortBytesWord (bytesStoreSetChunkValueBytes I) := by
  rw [bytesStoreSetChunkShortStoredWord]
  rw [bytesStoreOptimizedShortStoredWord_eq_setShortPackedHeader
    (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)) len hshort]
  have hpayloadWord :=
    bytesStoreSetChunkShortPayloadMaskedCallDataWord_eq_decodedWord
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload
  have hsize : (bytesStoreSetChunkValueBytes I).size = len.toNat := by
    rw [bytesStoreSetChunkValueBytes_size hpayload, ← hlenAbi]
  have htag :
      UInt256.mul ⟨2⟩ len =
        UInt256.ofNat ((bytesStoreSetChunkValueBytes I).size * 2) := by
    apply u256_inj
    rw [u256_mul_toNat]
    change (2 * len.toNat) % UInt256.size =
      ((bytesStoreSetChunkValueBytes I).size * 2) % UInt256.size
    rw [hsize, Nat.mul_comm]
  rw [StringStoreLite.setShortPackedHeader, solidityShortBytesWord]
  rw [hpayloadWord]
  rw [htag]

def bytesStoreSetChunkLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreSetChunkIndexWord I).toNat))).insert "value"
    (.bytes (bytesStoreSetChunkValueBytes I)))

def bytesStoreSetChunkLocalsOf (chunkIndex : UInt256) (value : ByteArray) : Store :=
  ((∅ : Store).insert "chunkIndex" (.int (Int.ofNat chunkIndex.toNat))).insert "value"
    (.bytes value)

def bytesStoreSetChunkFrameOf (chunkIndex : UInt256) (value : ByteArray) : Frame :=
  { contract := bytesStoreContract,
    locals := bytesStoreSetChunkLocalsOf chunkIndex value }

def bytesStoreSetChunkRefOf (chunkIndex : UInt256) : EvaledStorageRef :=
  { base := "chunks", steps := [.aindex (.int (Int.ofNat chunkIndex.toNat))] }

def bytesStoreSetChunkRef (I : ExecutionEnv) : EvaledStorageRef :=
  bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)

def bytesStoreSetChunkSlot (I : ExecutionEnv) : UInt256 :=
  chunksDataBase + bytesStoreSetChunkIndexWord I

theorem bytesStoreSetChunkLocalsOf_get_chunkIndex (chunkIndex : UInt256)
    (value : ByteArray) :
    (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
      some (.int (Int.ofNat chunkIndex.toNat)) := by
  unfold bytesStoreSetChunkLocalsOf
  rw [store_get_ne]
  · exact store_get_self (∅ : Store) "chunkIndex" (.int (Int.ofNat chunkIndex.toNat))
  · native_decide

theorem bytesStoreSetChunkLocalsOf_getElem_chunkIndex (chunkIndex : UInt256)
    (value : ByteArray) :
    (bytesStoreSetChunkLocalsOf chunkIndex value)["chunkIndex"]? =
      some (.int (Int.ofNat chunkIndex.toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreSetChunkLocalsOf_get_chunkIndex chunkIndex value

theorem bytesStoreSetChunkLocalsOf_get_chunks_none (chunkIndex : UInt256)
    (value : ByteArray) :
    (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunks" = none := by
  unfold bytesStoreSetChunkLocalsOf
  rw [store_get_ne]
  · rw [store_get_ne]
    · simp
    · native_decide
  · native_decide

theorem bytesStoreSetChunk_storageTypeAt {chunkIndex : UInt256} :
    storageTypeAt? bytesStoreContract.storage (bytesStoreSetChunkRefOf chunkIndex) =
      some .bytes := by
  simp [bytesStoreSetChunkRefOf, storageTypeAt?,
    bytesStoreContract, storageDecls, bytesSt, storageTypeStep?]

theorem accountMapEquiv_setChunkHeaderStore {σ : AccountMap} {evm : EVM.State}
    (I : ExecutionEnv) (owner : AccountAddress) (header : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
  accountMapEquiv
      (sstoreAccountMap owner σ (bytesStoreSetChunkSlot I) header)
      (Solm.EVM.storageStore evm owner (bytesStoreSetChunkSlot I) header).accountMap := by
  exact accountMapEquiv_bytesHeaderStore owner (bytesStoreSetChunkSlot I) header hAccounts

theorem bytesStoreSetChunkRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLayout
        { bytesStoreSetChunkRef I with
          steps := (bytesStoreSetChunkRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreSetChunkSlot I := by
  refine ⟨bytesLikeLengthLoc (bytesStoreSetChunkSlot I) evm, ?_, ?_⟩
  · have hnonneg : ¬ ((bytesStoreSetChunkIndexWord I).toNat : Int) < 0 := by
      omega
    simp [bytesStoreLayout, bytesStoreSetChunkRef, bytesStoreSetChunkRefOf,
      chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreSetChunkSlot, u256_ofNat_toNat]
    simp [hnonneg]
  · simp [bytesLikeLengthLoc]

theorem bytesStoreSetChunkEvalStorageRefOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value)
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreSetChunkRefOf chunkIndex) := by
  have hgetIndex :
      (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
        some (.int (Int.ofNat chunkIndex.toNat)) :=
    bytesStoreSetChunkLocalsOf_get_chunkIndex chunkIndex value
  have hkey :
      valueToKey? (.int (Int.ofNat chunkIndex.toNat)) =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetChunkFrameOf chunkIndex value).contract.storage "chunks" []
        (.int (Int.ofNat chunkIndex.toNat)) = .ok () := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreSetChunkFrameOf, bytesStoreContract, storageDecls, bytesSt,
      bytesStoreStorageLayout, solidityStorageLayout, bytesStoreLayout,
      bytesStoreStorageLocLoad_uint256, hload] using hbound
  simpa [chunkRef, bytesStoreSetChunkFrameOf, bytesStoreSetChunkRefOf] using
    (evalStorageRef_aindex_var_of_get?_ok
      (cfg := bytesStoreConfig)
      (solm := bytesStoreSetChunkFrameOf chunkIndex value)
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

theorem bytesStoreSetChunkEvalStorageRefRevertsOfChunksLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    evalStorageRef bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value)
      evm (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetIndex :
      (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
        some (.int (Int.ofNat chunkIndex.toNat)) :=
    bytesStoreSetChunkLocalsOf_get_chunkIndex chunkIndex value
  have hkey :
      valueToKey? (.int (Int.ofNat chunkIndex.toNat)) =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreConfig evm
        (bytesStoreSetChunkFrameOf chunkIndex value).contract.storage "chunks" []
        (.int (Int.ofNat chunkIndex.toNat)) = .revert := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreConfig,
      bytesStoreSetChunkFrameOf, bytesStoreContract, storageDecls, bytesSt,
      bytesStoreStorageLayout, solidityStorageLayout, bytesStoreLayout,
      bytesStoreStorageLocLoad_uint256, hload] using Nat.le_of_not_gt hbound
  simpa [chunkRef, bytesStoreSetChunkFrameOf] using
    (evalStorageRef_aindex_var_of_get?_revert
      (cfg := bytesStoreConfig)
      (solm := bytesStoreSetChunkFrameOf chunkIndex value)
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

def bytesStoreSetChunkHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreSetChunkSlot I) ⟨0⟩)

theorem bytesStoreSetChunkHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreSetChunkHeaderWord σ_evm I =
      bytesStoreSetChunkHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreSetChunkSlot I) ⟨0⟩

theorem bytesStoreStorageLoadSetChunkHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreSetChunkSlot I) =
      bytesStoreSetChunkHeaderWord σ_evm I := by
  simpa [bytesStoreSetChunkHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreSetChunkSlot I) hAccounts

theorem bytesStoreSetChunkAccountExistsOfBound {σ : AccountMap} {I : ExecutionEnv}
    (hbound :
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    ∃ acc, σ.find? I.codeOwner = some acc := by
  cases hacc : σ.find? I.codeOwner with
  | none =>
      have hzero : bytesStoreChunksLengthWord σ I = ⟨0⟩ := by
        unfold bytesStoreChunksLengthWord
        rw [hacc]
        rfl
      rw [hzero] at hbound
      exact False.elim (Nat.not_lt_zero _ hbound)
  | some acc =>
      exact ⟨acc, rfl⟩

theorem bytesStoreSetChunkResolveOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value) evm
      (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreSetChunkRefOf chunkIndex, .bytes) := by
  have hgetChunks :
      (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunks" = none :=
    bytesStoreSetChunkLocalsOf_get_chunks_none chunkIndex value
  have her'' :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetChunkLocalsOf chunkIndex value }
        evm { base := "chunks", steps := [.aindex (.var "chunkIndex")] } =
          .ok (bytesStoreSetChunkRefOf chunkIndex) := by
    simpa [chunkRef, bytesStoreSetChunkFrameOf] using
      (bytesStoreSetChunkEvalStorageRefOfLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact resolveStorageRef?_ok hgetChunks her'' bytesStoreSetChunk_storageTypeAt

theorem bytesStoreSetChunkResolveRevertsOfChunksLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value) evm
      (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunks" = none :=
    bytesStoreSetChunkLocalsOf_get_chunks_none chunkIndex value
  have herInline :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetChunkLocalsOf chunkIndex value }
        evm (chunkRef (.var "chunkIndex")) = .revert := by
    simpa [bytesStoreSetChunkFrameOf] using
      (bytesStoreSetChunkEvalStorageRefRevertsOfChunksLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks herInline

theorem bytesStoreSetChunkAssignOfLength {evm evm' : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreConfig evm
        (bytesStoreSetChunkRefOf chunkIndex) .bytes (.bytes value) = .ok evm') :
    assignStorageRef? bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value)
      evm .storage (chunkRef (.var "chunkIndex")) (.bytes value) =
        .ok (bytesStoreSetChunkFrameOf chunkIndex value, evm') := by
  have hresolve :=
    bytesStoreSetChunkResolveOfLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  exact assignStorageRef_storage_bytes_ok_of_write hresolve hwrite

theorem bytesStoreSetChunkLengthAfterWrite {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray} {n : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hlen :
      readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreSetChunkRefOf chunkIndex) = .ok n) :
    evalExpr? bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value)
      evm (.arrayLength .storage (chunkRef (.var "chunkIndex"))) =
        .ok (.int n) := by
  have hgetIndex :
      (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    unfold bytesStoreSetChunkLocalsOf
    rw [store_get_ne]
    · exact store_get_self (∅ : Store) "chunkIndex" (.int (Int.ofNat chunkIndex.toNat))
    · native_decide
  have hgetIndexElem :
      (bytesStoreSetChunkLocalsOf chunkIndex value)["chunkIndex"]? =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetIndex
  have hresolve :=
    bytesStoreSetChunkResolveOfLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  rw [evalExpr?]
  rw [hresolve]
  simp [readStorageArrayLength?, hlen, EvalResult.bind, bind, pure]

theorem bytesStoreSetChunkLengthRevertsOfChunksLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    evalExpr? bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value)
      evm (.arrayLength .storage (chunkRef (.var "chunkIndex"))) = .revert := by
  have hresolve :=
    bytesStoreSetChunkResolveRevertsOfChunksLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  rw [evalExpr?]
  rw [hresolve]
  simp [EvalResult.bind, bind]

theorem bytesStoreSetChunkBodyReturnsOfWrite {evm evm' : EVM.State}
    {chunkIndex chunksLen chunksLenPost : UInt256} {value : ByteArray} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreConfig evm
        (bytesStoreSetChunkRefOf chunkIndex) .bytes (.bytes value) = .ok evm')
    (hloadAfter :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hboundPost : chunkIndex.toNat < chunksLenPost.toNat)
    (hlenChunk :
      readStorageBytesLength? bytesStoreConfig evm'
        (bytesStoreSetChunkRefOf chunkIndex) = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body
      (.returned (bytesStoreSetChunkFrameOf chunkIndex value)
        evm' (some (.int n))) := by
  let solm0 := bytesStoreSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreSetChunkFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) =
          .ok (solm0, evm') := by
    simpa [solm0] using
      bytesStoreSetChunkAssignOfLength
        (evm := evm) (evm' := evm') (chunkIndex := chunkIndex) (value := value)
        hload hbound hwrite
  have hret :
      evalExpr? bytesStoreConfig solm0 evm'
        (.arrayLength .storage (chunkRef (.var "chunkIndex"))) =
          .ok (.int n) := by
    simpa [solm0] using
      bytesStoreSetChunkLengthAfterWrite
        (evm := evm') (chunkIndex := chunkIndex) (chunksLen := chunksLenPost) (value := value)
        hloadAfter hboundPost hlenChunk
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreSetChunkBodyReturnRevertsOfPostChunksLength {evm evm' : EVM.State}
    {chunkIndex chunksLen chunksLenPost : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreConfig evm
        (bytesStoreSetChunkRefOf chunkIndex) .bytes (.bytes value) = .ok evm')
    (hloadAfter :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hboundPost : ¬ chunkIndex.toNat < chunksLenPost.toNat) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body .reverted := by
  let solm0 := bytesStoreSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreSetChunkFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) =
          .ok (solm0, evm') := by
    simpa [solm0] using
      bytesStoreSetChunkAssignOfLength
        (evm := evm) (evm' := evm') (chunkIndex := chunkIndex) (value := value)
        hload hbound hwrite
  have hret :
      evalExpr? bytesStoreConfig solm0 evm'
        (.arrayLength .storage (chunkRef (.var "chunkIndex"))) = .revert := by
    simpa [solm0] using
      bytesStoreSetChunkLengthRevertsOfChunksLength
        (evm := evm') (chunkIndex := chunkIndex) (chunksLen := chunksLenPost)
        (value := value) hloadAfter hboundPost
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem bytesStoreSetChunkBodyRevertsOfWrite {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreConfig evm
        (bytesStoreSetChunkRefOf chunkIndex) .bytes (.bytes value) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body .reverted := by
  let solm0 := bytesStoreSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreSetChunkFrameOf] using hlookup)
  have hresolve :=
    bytesStoreSetChunkResolveOfLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  have hresolve0 :
      resolveStorageRef? bytesStoreConfig solm0 evm
        (chunkRef (.var "chunkIndex")) =
          .ok (bytesStoreSetChunkRefOf chunkIndex, .bytes) := by
    simpa [solm0] using hresolve
  have hassign :
      assignStorageRef? bytesStoreConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) = .revert := by
    exact assignStorageRef_storage_bytes_revert_of_write hresolve0 hwrite
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetChunkResolveRevertsOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetChunkFrameOf chunkIndex value) evm
      (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetChunksGet :
      (bytesStoreSetChunkLocalsOf chunkIndex value).get? "chunks" = none :=
    bytesStoreSetChunkLocalsOf_get_chunks_none chunkIndex value
  have her'' :
      evalStorageRef bytesStoreConfig
        { contract := bytesStoreContract, locals := bytesStoreSetChunkLocalsOf chunkIndex value }
        evm { base := "chunks", steps := [.aindex (.var "chunkIndex")] } = .revert := by
    simpa [chunkRef, bytesStoreSetChunkFrameOf] using
      (bytesStoreSetChunkEvalStorageRefRevertsOfChunksLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunksGet her''

theorem bytesStoreSetChunkBodyBoundsRevertsOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body .reverted := by
  let solm0 := bytesStoreSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreSetChunkFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreSetChunkResolveRevertsOfLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetChunkWriteEmptyOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetChunkSlot I) ⟨0⟩
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
      (.bytes (bytesStoreSetChunkValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize0 : (bytesStoreSetChunkValueBytes I).size = 0 := by
    rw [bytesStoreSetChunkValueBytes_size hpayload, hlenZero]
    rfl
  have hvalueEmpty : bytesStoreSetChunkValueBytes I = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero (bytesStoreSetChunkValueBytes I) hvalueSize0
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetChunkSlot I) =
        bytesStoreSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreSetChunkSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := bytesStoreWriteEmptyChunkShortPacked
    (evm := evmSolm0)
    (oldLen := bytesStoreSetChunkIndexWord I)
    (header := bytesStoreSetChunkHeaderWord σ_evm I)
    (len := oldLen)
    (by simpa [bytesStoreSetChunkSlot] using hload)
    (by simpa [bytesStoreSetChunkSlot] using hpacked)
    hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreSetChunkRefOf, bytesStoreSetChunkSlot, hvalueEmpty]
    using hwrite

theorem bytesStoreSetChunkWriteShortOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetChunkSlot I) (solidityShortBytesWord (bytesStoreSetChunkValueBytes I))
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
      (.bytes (bytesStoreSetChunkValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : (bytesStoreSetChunkValueBytes I).size < 32 := by
    rw [bytesStoreSetChunkValueBytes_size hpayload, ← hlenAbi]
    exact hshort
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetChunkSlot I) =
        bytesStoreSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreSetChunkSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := bytesStoreWriteChunkShortPacked
    (evm := evmSolm0)
    (oldLen := bytesStoreSetChunkIndexWord I)
    (header := bytesStoreSetChunkHeaderWord σ_evm I)
    (len := oldLen)
    (value := bytesStoreSetChunkValueBytes I)
    hvalueSize
    (by simpa [bytesStoreSetChunkSlot] using hload)
    (by simpa [bytesStoreSetChunkSlot] using hpacked)
    hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreSetChunkRefOf, bytesStoreSetChunkSlot]
    using hwrite

theorem bytesStoreSetChunkShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetChunkSlot I)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (bytesStoreSetChunkSlot I) storedWord)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (bytesStoreSetChunkSlot I) 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner (bytesStoreSetChunkSlot I)
          (solidityShortBytesWord value)).accountMap := by
  exact accountMapEquiv_setBytesShortFromLongPostAccountMapEquiv
    (baseSlot := bytesStoreSetChunkSlot I)
    (oldLen := oldLen) (storedWord := storedWord) (value := value)
    hAccounts hstored holdLenLt

theorem bytesStoreSetChunkLengthAfterEmptyWrite
    {cA gh bl σ_solm σ₀ A I} {g : UInt256} :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetChunkSlot I) ⟨0⟩
    readStorageBytesLength? bytesStoreConfig evmSolm1
      (bytesStoreSetChunkRef I) = .ok 0 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetChunkSlot I) ⟨0⟩
  exact bytesStoreReadLengthAfterHeaderStoreZero
    (er := bytesStoreSetChunkRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreSetChunkSlot I) (by rfl)
    (by simpa [evmSolm1] using bytesStoreSetChunkRef_length_slot evmSolm1 I)

theorem bytesStoreSetChunkLengthAfterShortWrite
    {cA gh bl σ_solm σ₀ A I} {g len payloadStart : UInt256} {acc : Account}
    (hacc : σ_solm.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreSetChunkShortStoredWord I len payloadStart
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetChunkSlot I) storedWord
    readStorageBytesLength? bytesStoreConfig evmSolm1
      (bytesStoreSetChunkRef I) = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreSetChunkShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetChunkSlot I) storedWord
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord] using
          bytesStoreSetChunkShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord] using
          bytesStoreSetChunkShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord] using
            bytesStoreSetChunkShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  exact bytesStoreReadLengthAfterHeaderStorePresent
    (er := bytesStoreSetChunkRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreSetChunkSlot I) (header := storedWord) (len := len.toNat)
    (by rfl)
    (by simpa [evmSolm1] using bytesStoreSetChunkRef_length_slot evmSolm1 I)
    (by simpa [evmSolm0, initState] using hacc)
    hdecode

theorem bytesStoreSetChunkSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreReachSetChunkDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2154⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨409⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreReachSetChunk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, by
    simpa [bytesStoreSetChunkEntryPc] using
      (evm_run hreach with [
        jumpdest, push2 ⟨263⟩, push2 ⟨409⟩, calldatasize, push1 ⟨4⟩,
        push2 ⟨2154⟩, jump (by native_decide)])⟩

theorem bytesStoreX_setChunkDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiNT (by rw [hgt']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    simpa [calldataWord] using hstart
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart'),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hlenMax
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiNT (by rw [hlenMax']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setChunkDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hpayload
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  exact evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiNT (by rw [hpayload']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem bytesStoreX_setChunkDecodeValidRaw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
            32),
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
          ⟨32⟩),
        uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32),
        ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    simpa [calldataWord] using hpayload
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  have rd1876 := evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiT (by rw [hpayload']; decide) (by native_decide)]
  have rd2213 := evm_run rd1876 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump (by native_decide)]
  have rd409 := evm_run rd2213 with [
    jumpdest, swap5, swap8, swap1, swap7, pop, swap4, swap5, pop, pop, pop, pop,
    jump (by native_decide)]
  exact ⟨_, _, evm_run rd409 with [jumpdest, push2 ⟨1144⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setChunkOobFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1144⟩ := hreach
  have rd1152 := evm_run rd1144 with [
    jumpdest, push0, dup3, dup3, push1 ⟨1⟩, dup7, dup2]
  obtain ⟨_, _, rd1153₀⟩ := rd1152.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1153⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1153⟩
        [bytesStoreChunksLengthWord σ I, chunkIndex, ⟨1⟩, len, payloadStart, ⟨0⟩,
          len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1153₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1153 with [
    dup2, lt, push2 ⟨1166⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨1166⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkReachWriteHelperFromBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩, chunksDataBase + chunkIndex,
        ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1144⟩ := hreach
  have rd1152 := evm_run rd1144 with [
    jumpdest, push0, dup3, dup3, push1 ⟨1⟩, dup7, dup2]
  obtain ⟨_, _, rd1153₀⟩ := rd1152.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1153⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1153⟩
        [bytesStoreChunksLengthWord σ I, chunkIndex, ⟨1⟩, len, payloadStart, ⟨0⟩,
          len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1153₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd1166 := evm_run rd1153 with [
    dup2, lt, push2 ⟨1166⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1173 := evm_run rd1166 with [
    jumpdest, swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 chunksDataBase (UInt256.ofNat 3)
      (by native_decide) mem_cost bytesStoreChunkLengthSlotHash
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd1173 with [
    add, swap2, dup3, push2 ⟨1187⟩, swap3, swap2, swap1, push2 ⟨2599⟩,
    jump (by native_decide)]⟩

theorem bytesStoreX_setChunkReachWriteHeaderDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      ((σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: (chunksDataBase + chunkIndex) ::
        payloadStart :: len :: ⟨1187⟩ :: (chunksDataBase + chunkIndex) ::
        ⟨0⟩ :: len :: payloadStart :: chunkIndex :: ⟨263⟩ ::
        bytesStoreSelWord I :: [])
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreX_setChunkReachWriteHelperFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound
  exact bytesStoreX_writeBytesHelperReachHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
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
            ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩, chunksDataBase + chunkIndex,
        ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreX_setChunkReachWriteHelperFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound
  exact bytesStoreX_writeBytesHelperShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax hflag hvalid
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkLongMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.div
              (σ.find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
              ⟨2⟩)
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let header : UInt256 :=
    σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)
  have hdecoder := bytesStoreX_setChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) hreach hbound hlenMax
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩,
      chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    hdecoder
    (by simpa [header] using hflag)
    (by simpa [header] using hbad)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkShortMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hbad :
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
            ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let header : UInt256 :=
    σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)
  have hdecoder := bytesStoreX_setChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) hreach hbound hlenMax
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩,
      chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    hdecoder
    (by simpa [header] using hflag)
    (by simpa [header] using hbad)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkShortOldLongReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
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
    (hshort : len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩) =
        ⟨0⟩) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let header : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD slot ⟨0⟩))
  have hdecoder := bytesStoreX_setChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) hreach hbound hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header, slot] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, slot, hstoredEq] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩,
      len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header, slot] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩, slot,
          ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1187⟩,
        slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header, slot] using hflag)
      (by simpa [header, slot] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have holdGtNat : 31 < oldStoredLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩ :=
    ugt_one (by omega)
  have hshortWord : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hloopEntry := bytesStoreX_writeBytesCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
      chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := (⟨0⟩ : UInt256) + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
      chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [slot] using hloop

theorem bytesStoreX_setChunkShortOldLongReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
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
    (hshort : len.toNat < 32) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreX_setChunkShortOldLongReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hbound hlenMax hflag holdStoredLen hvalid hshort hcontinue hdone

theorem bytesStoreX_setChunkShortNonemptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
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
    (hshort : len.toNat < 32) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear slot
        (bytesStoreSetChunkShortStoredWord I len payloadStart)) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hbranch := bytesStoreX_setChunkShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hshort
  have hwrite := bytesStoreX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [slot, σClear] using hbranch) hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot
      (bytesStoreSetChunkShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [bytesStoreSetChunkShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkEmptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
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
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear slot ⟨0⟩) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hshort : len.toNat < 32 := by
    rw [hlenZero]
    decide
  have hbranch := bytesStoreX_setChunkShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hshort
  have hpacked := bytesStoreX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [slot, σClear] using hbranch) hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hwrite
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkEmptyWriteReturnsToBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
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
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩)
      k C := by
  have hbranch := bytesStoreX_setChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound hlenMax hflag hvalid
  have hpacked := bytesStoreX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hbranch hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hwrite (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkShortNonemptyWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
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
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) storedWord) k C := by
  dsimp only
  have hbranch := bytesStoreX_setChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound hlenMax hflag hvalid
  have hwrite := bytesStoreX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hbranch hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex)
      (UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))))
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    (by simpa using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkReturnFromDecodedLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {chunkLen slot len payloadStart chunkIndex : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1002⟩
      [chunkLen, slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [chunkLen, bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd1002⟩ := hreach
  exact ⟨_, _, evm_run rd1002 with [
    jumpdest, swap6, swap5, pop, pop, pop, pop, pop, jump (by native_decide)]⟩

theorem bytesStoreSetChunkEmptyHeaderAfterWrite
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex : UInt256) :
    (((sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩).find?
        I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) (default : UInt256))) =
      ⟨0⟩ := by
  have h := sstoreAccountMap_storage_findD_eq_if σ I.codeOwner
    (chunksDataBase + chunkIndex) (chunksDataBase + chunkIndex) (⟨0⟩ : UInt256)
  rw [h]
  cases σ.find? I.codeOwner with
  | none =>
      simp [Option.option]
      rfl
  | some _ =>
      simp [Option.option]

theorem bytesStoreX_setChunkReachReturnLengthDecoder
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
        ⟨1002⟩, chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1187⟩ := hreach
  have rd1193 := evm_run rd1187 with [
    jumpdest, pop, push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1194₀⟩ := rd1193.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1194⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1194⟩
        [bytesStoreChunksLengthWord σ I, chunkIndex, ⟨1⟩, ⟨0⟩, len, payloadStart,
          chunkIndex, ⟨263⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1194₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreChunksLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd1207 := evm_run rd1194 with [
    dup2, lt, push2 ⟨1207⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have hslotHash :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((wordAt0Mem (⟨1⟩ : UInt256)
                (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)).readWithPadding 0 32))) =
        chunksDataBase := by
    rw [wordAt0Mem_read0]
    simpa [chunksDataBase, bytesLikeDataBase]
      using keccakSlot_eq (UInt256.toByteArray (⟨1⟩ : UInt256))
  have rd1214 := evm_run rd1207 with [
    jumpdest, swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 chunksDataBase (UInt256.ofNat 3)
      (by native_decide) mem_cost hslotHash
      (by native_decide) (by evm_ov),
    add, dup1]
  obtain ⟨_, _, rd1218₀⟩ := rd1214.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1218⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1218⟩
        [(σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
          chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
          bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [initState] using rd1218₀⟩
  exact ⟨_, _, evm_run rd1218 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_panic32MemFromReachSetChunk
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2579⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2579⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreFullPanicSelectorWord := by
    decide
  have rd2591₀ := evm_run rd2579 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2591 := rd2591₀
  rw [hsel] at rd2591
  exact evm_run rd2591 with [
    raw mstore 0 (bytesStoreFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreFullPanicMemFrom ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreX_setChunkReturnOobChunksLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : ¬ chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd1187⟩ := hreach
  have rd1193 := evm_run rd1187 with [
    jumpdest, pop, push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1194₀⟩ := rd1193.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1194⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1194⟩
        [bytesStoreChunksLengthWord σ I, chunkIndex, ⟨1⟩, ⟨0⟩, len, payloadStart,
          chunkIndex, ⟨263⟩, bytesStoreSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreChunksLengthWord, initState] using rd1194₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1194 with [
    dup2, lt, push2 ⟨1207⟩, jumpiNT (by simpa using hlt),
    push2 ⟨1207⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreX_panic32MemFromReachSetChunk ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setChunkEmptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
    (hboundPost :
      chunkIndex.toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩) I).toNat)
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
    (hlenZero : len = ⟨0⟩) :
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  dsimp only
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩
  have hbody := bytesStoreX_setChunkEmptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hperm hreach hbound hlenMax hflag hvalid hlenZero
  have hbound' : chunkIndex.toNat < (bytesStoreChunksLengthWord σ' I).toNat := by
    simpa [σ'] using hboundPost
  have hdecoder := bytesStoreX_setChunkReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (by simpa [σ'] using hbody) hbound'
  have hheader : (σ'.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) = ⟨0⟩ := by
    simpa [σ'] using bytesStoreSetChunkEmptyHeaderAfterWrite σ I chunkIndex
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := (⟨0⟩ : UInt256))
    (slot := chunksDataBase + chunkIndex) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
      (bytesStoreWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)
        (bytesStoreWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

theorem bytesStoreX_setChunkShortNonemptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreChunksLengthWord σ I).toNat)
    (hboundPost :
      chunkIndex.toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex)
            (bytesStoreSetChunkShortStoredWord I len payloadStart)) I).toNat)
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
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hacc : σ.find? I.codeOwner = some acc) :
    let storedWord := bytesStoreSetChunkShortStoredWord I len payloadStart
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) storedWord
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray len) := by
  dsimp only
  let storedWord := bytesStoreSetChunkShortStoredWord I len payloadStart
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) storedWord
  let header : UInt256 :=
    σ'.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)
  have hbody := bytesStoreX_setChunkShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hperm hreach hbound hlenMax hflag hvalid hnz hshort
  have hbound' : chunkIndex.toNat < (bytesStoreChunksLengthWord σ' I).toNat := by
    simpa [σ', storedWord] using hboundPost
  have hdecoder := bytesStoreX_setChunkReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (by
      simpa [σ', storedWord, bytesStoreSetChunkShortStoredWord] using hbody)
    hbound'
  have hdata :
      (σ'.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) =
        storedWord := by
    have hnzStored := bytesStoreSetChunkShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simpa [σ', storedWord] using
      sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc
        (chunksDataBase + chunkIndex) storedWord hacc hnzStored
  have hheader : header = storedWord := by
    simpa [header] using hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    exact bytesStoreSetChunkShortStoredWord_flag_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader,
      bytesStoreSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    exact bytesStoreSetChunkShortStoredWord_shortLen_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len)
    (slot := chunksDataBase + chunkIndex) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex)
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

set_option maxHeartbeats 1200000 in
theorem bytesStoreX_setChunkOob {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hbound :
      ¬ (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ I).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := bytesStoreX_setChunkDecodeValidRaw
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMax hpayload
  exact bytesStoreX_setChunkOobFromBody (g := g) hreach (by
    simpa [bytesStoreSetChunkIndexWord, calldataWord] using hbound)

theorem bytesStoreDecode_setChunk_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_short (cd := I.calldata) (x := "chunkIndex")
      (y := "value") hshort

theorem bytesStoreDecode_setChunk_none_totalHuge {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_total_huge (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hbig

theorem bytesStoreDecode_setChunk_none_offsetHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_offset_huge (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hsz68 hsizeSign hoff

theorem bytesStoreDecode_setChunk_none_lengthShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_length_short (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hsz68 hsizeSign hoffMax hshort

theorem bytesStoreDecode_setChunk_none_lengthHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_length_huge (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenHuge

theorem bytesStoreDecode_setChunk_none_payloadShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_payload_short (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenMax
      hpayload

theorem bytesStoreDecode_setChunk {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (_hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreSetChunkLocals I) := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata =
    some (bytesStoreSetChunkLocals I)
  simpa [uint256, abiUInt256, bytesStoreSetChunkLocals,
    bytesStoreSetChunkIndexWord, bytesStoreSetChunkValueBytes] using
    decodeCalldata_uint256_bytes_some (cd := I.calldata) (x := "chunkIndex")
      (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem bytesStoreSetChunkDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkSelector_size hsel
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk_none_short (I := I) hshort
  exact (bytesStoreX_setChunkDecodeShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hshort hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetChunkSelector_size hsel
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk_none_totalHuge (I := I) (by omega)
  exact (bytesStoreX_setChunkDecodeHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hbig hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setChunkTransition.params.map Param.name)
        (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · exact bytesStoreDecode_setChunk_none_offsetHuge (I := I)
        hsz68 hsizeSign hoff
    · exact bytesStoreDecode_setChunk_none_totalHuge (I := I)
        (Nat.le_of_not_gt hsizeSign)
  exact (bytesStoreX_setChunkDecodeOffsetHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk_none_lengthShort (I := I)
    hsz68 hsizeSign hoffMax hlenShort
  exact (bytesStoreX_setChunkDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk_none_lengthHuge (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenHuge
  exact (bytesStoreX_setChunkDecodeLengthHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length ≠
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
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk_none_payloadShort (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenMax hpayloadList
  exact (bytesStoreX_setChunkDecodePayloadShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetChunkEmptyOldShortRuntimeOfReach_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreSetChunkLocals I))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hbound :
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hboundPost :
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) ⟨0⟩) I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetChunkSlot I) ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) ⟨0⟩
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, bytesStoreSetChunkSlot, hchunkIndex] using
      bytesStoreX_setChunkEmptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart)
        (chunkIndex := chunkIndex)
        hperm hreach hboundChunk (by simpa [σFinal, bytesStoreSetChunkSlot, hchunkIndex]
          using hboundPost) hlenMax
        (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
          using hvalid)
        hlenZero
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreSetChunkValueBytes I)) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreSetChunkWriteEmptyOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hAccounts hpayloadList hlenZeroAbi hflag hvalid
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetChunkSlot I) ⟨0⟩
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σFinal I := by
    exact bytesStoreStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  have hlenChunk :
      readStorageBytesLength? bytesStoreConfig evmSolm1
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) = .ok 0 := by
    simpa [evmSolm0, evmSolm1, bytesStoreSetChunkRef, bytesStoreSetChunkRefOf]
      using bytesStoreSetChunkLengthAfterEmptyWrite
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreSetChunkFrameOf (bytesStoreSetChunkIndexWord I)
          (bytesStoreSetChunkValueBytes I)) evmSolm1 (some (.int 0))) := by
    simpa [evmSolm0, evmSolm1, bytesStoreSetChunkLocals,
      bytesStoreSetChunkLocalsOf, bytesStoreSetChunkIndexWord] using
      bytesStoreSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreSetChunkIndexWord I)
        (chunksLen := bytesStoreChunksLengthWord σ_evm I)
        (value := bytesStoreSetChunkValueBytes I)
        (n := 0)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hboundPost hlenChunk
  have hCreated : (cA, σFinal).1 = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts]
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
        setChunkTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

theorem bytesStoreSetChunkEmptyOldShortRuntimeOfReach_post_oob
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreSetChunkLocals I))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hbound :
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hboundPost :
      ¬ (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) ⟨0⟩) I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetChunkSlot I) ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) ⟨0⟩
  have hrev :
      RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    have hbodyReach := bytesStoreX_setChunkEmptyWriteReturnsToBody
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
      hperm hreach hboundChunk hlenMax
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
        using hflag)
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
        using hvalid)
      hlenZero
    exact bytesStoreX_setChunkReturnOobChunksLength
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm) (σ := σFinal)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (slot := bytesStoreSetChunkSlot I) (len := len) (payloadStart := payloadStart)
      (chunkIndex := chunkIndex)
      (by simpa [σFinal, bytesStoreSetChunkSlot, hchunkIndex] using hbodyReach)
      (by simpa [σFinal, bytesStoreSetChunkSlot, hchunkIndex] using hboundPost)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreSetChunkValueBytes I)) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreSetChunkWriteEmptyOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hAccounts hpayloadList hlenZeroAbi hflag hvalid
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetChunkSlot I) ⟨0⟩
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σFinal I := by
    exact bytesStoreStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, bytesStoreSetChunkLocals,
      bytesStoreSetChunkLocalsOf, bytesStoreSetChunkIndexWord] using
      bytesStoreSetChunkBodyReturnRevertsOfPostChunksLength
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreSetChunkIndexWord I)
        (chunksLen := bytesStoreChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreChunksLengthWord σFinal I)
        (value := bytesStoreSetChunkValueBytes I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter
        (by simpa [σFinal] using hboundPost)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetChunkShortNonemptyOldShortRuntimeOfReach_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreSetChunkLocals I))
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hboundPost :
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I)
            (bytesStoreSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetChunkValueBytes I
  let storedWord := bytesStoreSetChunkShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetChunkSlot I) (solidityShortBytesWord value)
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) storedWord
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, storedWord, bytesStoreSetChunkSlot, hchunkIndex] using
      bytesStoreX_setChunkShortNonemptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (acc := accEvm)
        hperm hreach hboundChunk
        (by simpa [σFinal, storedWord, bytesStoreSetChunkSlot, hchunkIndex]
          using hboundPost) hlenMax
        (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
          using hvalid)
        hnz hshort haccEvm
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value] using
      bytesStoreSetChunkWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using
      bytesStoreSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState, hstored] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetChunkSlot I) (solidityShortBytesWord value)
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σFinal I := by
    exact bytesStoreStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hvalueSize : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hlenChunk :
      readStorageBytesLength? bytesStoreConfig evmSolm1
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreSetChunkLengthAfterShortWrite
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (len := len) (payloadStart := payloadStart) (acc := accSolm)
      haccSolm hnz hshort
    simpa [evmSolm0, evmSolm1, value, storedWord, hstored, hvalueSize,
      bytesStoreSetChunkRef, bytesStoreSetChunkRefOf] using hlen₀
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreSetChunkFrameOf (bytesStoreSetChunkIndexWord I) value)
          evmSolm1 (some (.int value.size))) := by
    have hbody₀ := bytesStoreSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreSetChunkIndexWord I)
        (chunksLen := bytesStoreChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hboundPost hlenChunk
    change ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
      (bytesStoreSetChunkLocalsOf (bytesStoreSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreSetChunkFrameOf (bytesStoreSetChunkIndexWord I) value)
        evmSolm1 (some (.int value.size)))
    exact hbody₀
  have hCreated : (cA, σFinal).1 = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts]
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
theorem bytesStoreSetChunkShortNonemptyOldShortRuntimeOfReach_post_oob
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setChunkTransition)
    (hdec : decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata =
        some (bytesStoreSetChunkLocals I))
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hboundPost :
      ¬ (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I)
            (bytesStoreSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetChunkValueBytes I
  let storedWord := bytesStoreSetChunkShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetChunkSlot I) (solidityShortBytesWord value)
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) storedWord
  have hrev :
      RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    have hbodyReach := bytesStoreX_setChunkShortNonemptyWriteReturnsToBody
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
      hperm hreach hboundChunk hlenMax
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
        using hflag)
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot, hchunkIndex]
        using hvalid)
      hnz hshort
    exact bytesStoreX_setChunkReturnOobChunksLength
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm) (σ := σFinal)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (slot := bytesStoreSetChunkSlot I) (len := len) (payloadStart := payloadStart)
      (chunkIndex := chunkIndex)
      (by simpa [σFinal, storedWord, bytesStoreSetChunkSlot, hchunkIndex,
          bytesStoreSetChunkShortStoredWord] using hbodyReach)
      (by simpa [σFinal, storedWord, bytesStoreSetChunkSlot, hchunkIndex] using hboundPost)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value] using
      bytesStoreSetChunkWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using
      bytesStoreSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState, hstored] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreSetChunkSlot I) (solidityShortBytesWord value)
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σFinal I := by
    exact bytesStoreStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, value, bytesStoreSetChunkLocals,
      bytesStoreSetChunkLocalsOf, bytesStoreSetChunkIndexWord] using
      bytesStoreSetChunkBodyReturnRevertsOfPostChunksLength
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreSetChunkIndexWord I)
        (chunksLen := bytesStoreChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreChunksLengthWord σFinal I)
        (value := value)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter
        (by simpa [σFinal] using hboundPost)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetChunkEmptyOldShortRuntime_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hboundPost :
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) ⟨0⟩) I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_gt_max I hoffMax hlenMaxAbiWord
  have hlenZeroLen : len = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_zero I hoffMax hlenZero
  have hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  exact bytesStoreSetChunkEmptyOldShortRuntimeOfReach_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hcode hperm hwv hAccounts hreach hchunkIndex hd hdec hpayloadList hlenMaxLen hbound
    hboundPost hflag hvalid hlenZeroLen hlenZero

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetChunkShortNonemptyOldShortRuntime_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hboundPost :
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I)
            (bytesStoreSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  exact bytesStoreSetChunkShortNonemptyOldShortRuntimeOfReach_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (accEvm := accEvm)
    hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen hbound
    (by simpa [len, payloadStart] using hboundPost) hflag hvalid hnzLen hshortLen

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetChunkShortNonemptyOldShortRuntime_post_oob
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hboundPost :
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
      ¬ (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I)
            (bytesStoreSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, chunkIndex]
    exact bytesStoreX_setChunkDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I := by
    dsimp [chunkIndex]
    rw [bytesStoreSetChunkIndexWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  exact bytesStoreSetChunkShortNonemptyOldShortRuntimeOfReach_post_oob
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hcode hperm hwv hAccounts hreach hchunkIndex hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen hbound
    (by simpa [len, payloadStart] using hboundPost) hflag hvalid hnzLen hshortLen

theorem bytesStoreSetChunkShortOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hzero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩
  · by_cases hboundPost :
        (bytesStoreSetChunkIndexWord I).toNat <
          (bytesStoreChunksLengthWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I) ⟨0⟩) I).toNat
    · exact bytesStoreSetChunkEmptyOldShortRuntime_of_post_bound
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hboundPost hflag hvalid hzero
    · let len : UInt256 :=
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
      have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
          [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
        dsimp [len, payloadStart, chunkIndex]
        exact bytesStoreX_setChunkDecodeValidRaw
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g)
          hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
      have hd := bytesStoreDispatch_setChunk (cd := I.calldata)
        (by simpa [selIs] using hsel)
      have hdec := bytesStoreDecode_setChunk (I := I)
        hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
      have hlenMaxAbiWord :
          UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
              ⟨18446744073709551615⟩ = ⟨0⟩ := by
        apply ugt_zero
        rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
        exact Nat.le_of_not_gt hlenMax
      have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
        dsimp [len]
        exact bytesStoreSetChunkRawLengthWord_gt_max I hoffMax hlenMaxAbiWord
      have hlenZeroLen : len = ⟨0⟩ := by
        dsimp [len]
        exact bytesStoreSetChunkRawLengthWord_zero I hoffMax hzero
      have hchunkIndex : chunkIndex = bytesStoreSetChunkIndexWord I := by
        dsimp [chunkIndex]
        rw [bytesStoreSetChunkIndexWord, calldataWord]
        have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
        rw [h4]
      exact bytesStoreSetChunkEmptyOldShortRuntimeOfReach_post_oob
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        hcode hperm hwv hAccounts hreach hchunkIndex hd hdec hpayloadList hlenMaxLen hbound
        (by simpa [len, payloadStart] using hboundPost) hflag hvalid hlenZeroLen hzero
  · have hnz :
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0 := by
      intro hnat
      apply hzero
      apply u256_inj
      rw [hnat]
      native_decide
    obtain ⟨accEvm, haccEvm⟩ :=
      bytesStoreSetChunkAccountExistsOfBound
        (σ := σ_evm) (I := I) hbound
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
    by_cases hboundPost :
        (bytesStoreSetChunkIndexWord I).toNat <
          (bytesStoreChunksLengthWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetChunkSlot I)
              (bytesStoreSetChunkShortStoredWord I len payloadStart)) I).toNat
    · exact bytesStoreSetChunkShortNonemptyOldShortRuntime_of_post_bound
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hboundPost hflag hvalid
        hnz hshort
    · exact bytesStoreSetChunkShortNonemptyOldShortRuntime_post_oob
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound
        (by simpa [len, payloadStart] using hboundPost) hflag hvalid hnz hshort

theorem bytesStoreSetChunkLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hreach := bytesStoreX_setChunkDecodeValidRaw
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hrev : RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreX_setChunkLongMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hreach
      (by simpa [bytesStoreSetChunkIndexWord, calldataWord] using hbound)
      hlenMaxWord
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot,
        bytesStoreSetChunkIndexWord, calldataWord] using hflag)
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot,
        bytesStoreSetChunkIndexWord, calldataWord] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (chunksDataBase + bytesStoreSetChunkIndexWord I) =
        bytesStoreSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, bytesStoreSetChunkSlot] using
      bytesStoreStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreSetChunkValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreSetChunkRefOf] using
      bytesStoreWriteChunkMalformedLong
        (evm := evmSolm0)
        (oldLen := bytesStoreSetChunkIndexWord I)
        (header := bytesStoreSetChunkHeaderWord σ_evm I)
        (value := bytesStoreSetChunkValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, bytesStoreSetChunkLocals, bytesStoreSetChunkLocalsOf,
      bytesStoreSetChunkIndexWord] using
      bytesStoreSetChunkBodyRevertsOfWrite
        (evm := evmSolm0)
        (chunkIndex := bytesStoreSetChunkIndexWord I)
        (chunksLen := bytesStoreChunksLengthWord σ_evm I)
        (value := bytesStoreSetChunkValueBytes I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks
        hbound
        hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetChunkShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
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
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hreach := bytesStoreX_setChunkDecodeValidRaw
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hrev : RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreX_setChunkShortMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hreach
      (by simpa [bytesStoreSetChunkIndexWord, calldataWord] using hbound)
      hlenMaxWord
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot,
        bytesStoreSetChunkIndexWord, calldataWord] using hflag)
      (by simpa [bytesStoreSetChunkHeaderWord, bytesStoreSetChunkSlot,
        bytesStoreSetChunkIndexWord, calldataWord] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (chunksDataBase + bytesStoreSetChunkIndexWord I) =
        bytesStoreSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, bytesStoreSetChunkSlot] using
      bytesStoreStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetChunkRefOf (bytesStoreSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreSetChunkValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreSetChunkRefOf] using
      bytesStoreWriteChunkMalformedShort
        (evm := evmSolm0)
        (oldLen := bytesStoreSetChunkIndexWord I)
        (header := bytesStoreSetChunkHeaderWord σ_evm I)
        (value := bytesStoreSetChunkValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, bytesStoreSetChunkLocals, bytesStoreSetChunkLocalsOf,
      bytesStoreSetChunkIndexWord] using
      bytesStoreSetChunkBodyRevertsOfWrite
        (evm := evmSolm0)
        (chunkIndex := bytesStoreSetChunkIndexWord I)
        (chunksLen := bytesStoreChunksLengthWord σ_evm I)
        (value := bytesStoreSetChunkValueBytes I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks
        hbound
        hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetChunkOobRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
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
      ¬ (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [bytesStoreSetChunkLocals, bytesStoreSetChunkLocalsOf,
      bytesStoreSetChunkIndexWord] using
      bytesStoreSetChunkBodyBoundsRevertsOfLength
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (chunkIndex := bytesStoreSetChunkIndexWord I)
        (chunksLen := bytesStoreChunksLengthWord σ_evm I)
        (value := bytesStoreSetChunkValueBytes I)
        (by simp only [initState]; exact hwv)
        (by simpa [initState] using hloadChunks)
        hbound
  exact (bytesStoreX_setChunkOob
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetChunkShortNewOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hbound :
      (bytesStoreSetChunkIndexWord I).toNat <
        (bytesStoreChunksLengthWord σ_evm I).toNat
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreSetChunkShortOldShortRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflag hvalid hshort
    · exact bytesStoreSetChunkShortMalformedRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflag
        (not_ne_iff.mp hvalid)
  · exact bytesStoreSetChunkOobRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound

end BytesStore
