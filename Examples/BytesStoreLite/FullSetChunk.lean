import Examples.BytesStoreLite.FullSetPacket

/-!
# BytesStoreLite — `setChunk(uint256,bytes)` runtime slice

This module starts the full-contract `setChunk(uint256,bytes)` selector arm.  The first layer pins
the mixed static/dynamic ABI decoding facts used by both `setChunk` and the analogous mapped bytes
setter.
-/

namespace BytesStoreLite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

def bytesStoreLiteSetChunkIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreLiteSetChunkValueBytes (I : ExecutionEnv) : ByteArray :=
  ByteArray.mk
    ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).toArray)

theorem bytesStoreLiteSetChunkValueBytes_toList {I : ExecutionEnv} :
    (bytesStoreLiteSetChunkValueBytes I).toList =
      (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) := by
  simp [bytesStoreLiteSetChunkValueBytes, byteArray_toList_eq]

theorem bytesStoreLiteSetChunkValueBytes_size {I : ExecutionEnv}
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    (bytesStoreLiteSetChunkValueBytes I).size =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
  let payload :=
    (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
  change payload.toArray.size =
    (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
  rw [show payload.toArray.size = payload.length by simp]
  simpa [payload] using hpayload

@[simp] theorem bytesStoreLiteCalldataWord36_add32 (I : ExecutionEnv) :
    uInt256OfByteArray
      (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) =
        calldataWord I.calldata 36 := by
  have h : (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) = 36 := by
    native_decide
  simp [calldataWord, h]

theorem bytesStoreLiteSetChunkRawLengthWord_eq (I : ExecutionEnv)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32) =
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
  rw [bytesStoreLiteCalldataWord36_add32]
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

theorem bytesStoreLiteSetChunkRawLengthWord_gt_max
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
  rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
  exact hlenMax

theorem bytesStoreLiteSetChunkRawLengthWord_zero
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
  rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
  exact hlenZero

def bytesStoreLiteSetChunkShortStoredWord (I : ExecutionEnv)
    (len payloadStart : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
    (UInt256.land
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
      (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))

theorem bytesStoreLiteSetChunkShortStoredWord_flag_eq {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    UInt256.land (bytesStoreLiteSetChunkShortStoredWord I len payloadStart) ⟨1⟩ =
      ⟨0⟩ := by
  simpa [bytesStoreLiteSetChunkShortStoredWord, bytesStoreLiteSetPacketShortStoredWord] using
    bytesStoreLiteSetPacketShortStoredWord_flag_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort

theorem bytesStoreLiteSetChunkShortStoredWord_shortLen_eq {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    UInt256.land
        (UInt256.div (bytesStoreLiteSetChunkShortStoredWord I len payloadStart) ⟨2⟩)
        ⟨127⟩ = len := by
  simpa [bytesStoreLiteSetChunkShortStoredWord, bytesStoreLiteSetPacketShortStoredWord] using
    bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort

theorem bytesStoreLiteSetChunkShortStoredWord_beq_zero_false {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    (bytesStoreLiteSetChunkShortStoredWord I len payloadStart == (default : UInt256)) =
      false := by
  simpa [bytesStoreLiteSetChunkShortStoredWord, bytesStoreLiteSetPacketShortStoredWord] using
    bytesStoreLiteSetPacketShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort

theorem bytesStoreLiteSetChunkPayloadStart_toNat {I : ExecutionEnv} {payloadStart : UInt256}
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

theorem bytesStoreLiteSetChunkShortValueReadWithPadding_toList {I : ExecutionEnv}
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
    ((bytesStoreLiteSetChunkValueBytes I).readWithPadding 0 32).toList =
      (I.calldata.toList.drop payloadStart.toNat).take len.toNat ++
        List.replicate (32 - len.toNat) 0 := by
  have hsize :
      (bytesStoreLiteSetChunkValueBytes I).size = len.toNat := by
    rw [bytesStoreLiteSetChunkValueBytes_size hpayload, ← hlenAbi]
  rw [readWithPadding_zero_toList_of_size_lt32
    (bytesStoreLiteSetChunkValueBytes I)
    (by rw [hsize]; exact hnz)
    (by rw [hsize]; exact hshort)]
  rw [hsize]
  rw [bytesStoreLiteSetChunkValueBytes_toList]
  rw [← hlenAbi]
  have hpayloadNat :=
    bytesStoreLiteSetChunkPayloadStart_toNat
      (I := I) (payloadStart := payloadStart) hpayloadStart hoffMax
  rw [hpayloadNat]
  rw [List.drop_drop]
  rw [show 4 + ((calldataWord I.calldata 36).toNat + 32) =
      4 + (calldataWord I.calldata 36).toNat + 32 by omega]

theorem bytesStoreLiteSetChunkPayloadStartLen_le_of_payload {I : ExecutionEnv}
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
    bytesStoreLiteSetChunkPayloadStart_toNat
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

theorem bytesStoreLiteSetChunkShortPayloadMaskedCallDataWord_eq_decodedWord
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
        ((bytesStoreLiteSetChunkValueBytes I).readWithPadding 0 32) := by
  rw [BytesStoreLiteCore.setShortPackedHeader_mask_of_short hshort]
  rw [uInt256OfByteArray_readBytes_at_high_mask_eq_padded
    I.calldata payloadStart.toNat len.toNat hshort hsrc]
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq]
  rw [← byteArray_toList_eq
    ((bytesStoreLiteSetChunkValueBytes I).readWithPadding 0 32)]
  rw [bytesStoreLiteSetChunkShortValueReadWithPadding_toList
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax hnz hshort hpayload]
  rw [byteArray_toList_eq]

theorem bytesStoreLiteSetChunkShortStoredWord_eq_solidityShortBytesWord
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
    bytesStoreLiteSetChunkShortStoredWord I len payloadStart =
      solidityShortBytesWord (bytesStoreLiteSetChunkValueBytes I) := by
  rw [bytesStoreLiteSetChunkShortStoredWord]
  rw [bytesStoreLiteOptimizedShortStoredWord_eq_setShortPackedHeader
    (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)) len hshort]
  have hpayloadWord :=
    bytesStoreLiteSetChunkShortPayloadMaskedCallDataWord_eq_decodedWord
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload
  have hsize : (bytesStoreLiteSetChunkValueBytes I).size = len.toNat := by
    rw [bytesStoreLiteSetChunkValueBytes_size hpayload, ← hlenAbi]
  have htag :
      UInt256.mul ⟨2⟩ len =
        UInt256.ofNat ((bytesStoreLiteSetChunkValueBytes I).size * 2) := by
    apply u256_inj
    rw [u256_mul_toNat]
    change (2 * len.toNat) % UInt256.size =
      ((bytesStoreLiteSetChunkValueBytes I).size * 2) % UInt256.size
    rw [hsize, Nat.mul_comm]
  rw [BytesStoreLiteCore.setShortPackedHeader, solidityShortBytesWord]
  rw [hpayloadWord]
  rw [htag]

def bytesStoreLiteSetChunkLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "chunkIndex"
    (.int (Int.ofNat (bytesStoreLiteSetChunkIndexWord I).toNat))).insert "value"
    (.bytes (bytesStoreLiteSetChunkValueBytes I)))

def bytesStoreLiteSetChunkLocalsOf (chunkIndex : UInt256) (value : ByteArray) : Store :=
  ((∅ : Store).insert "chunkIndex" (.int (Int.ofNat chunkIndex.toNat))).insert "value"
    (.bytes value)

def bytesStoreLiteSetChunkFrameOf (chunkIndex : UInt256) (value : ByteArray) : Frame :=
  { contract := bytesStoreLiteContract,
    locals := bytesStoreLiteSetChunkLocalsOf chunkIndex value }

def bytesStoreLiteSetChunkRefOf (chunkIndex : UInt256) : EvaledStorageRef :=
  { base := "chunks", steps := [.aindex (.int (Int.ofNat chunkIndex.toNat))] }

def bytesStoreLiteSetChunkRef (I : ExecutionEnv) : EvaledStorageRef :=
  bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)

def bytesStoreLiteSetChunkSlot (I : ExecutionEnv) : UInt256 :=
  chunksDataBase + bytesStoreLiteSetChunkIndexWord I

theorem bytesStoreLiteSetChunkLocalsOf_get_chunkIndex (chunkIndex : UInt256)
    (value : ByteArray) :
    (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
      some (.int (Int.ofNat chunkIndex.toNat)) := by
  unfold bytesStoreLiteSetChunkLocalsOf
  rw [store_get_ne]
  · exact store_get_self (∅ : Store) "chunkIndex" (.int (Int.ofNat chunkIndex.toNat))
  · native_decide

theorem bytesStoreLiteSetChunkLocalsOf_getElem_chunkIndex (chunkIndex : UInt256)
    (value : ByteArray) :
    (bytesStoreLiteSetChunkLocalsOf chunkIndex value)["chunkIndex"]? =
      some (.int (Int.ofNat chunkIndex.toNat)) := by
  simpa [Std.HashMap.get?_eq_getElem?] using
    bytesStoreLiteSetChunkLocalsOf_get_chunkIndex chunkIndex value

theorem bytesStoreLiteSetChunkLocalsOf_get_chunks_none (chunkIndex : UInt256)
    (value : ByteArray) :
    (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunks" = none := by
  unfold bytesStoreLiteSetChunkLocalsOf
  rw [store_get_ne]
  · rw [store_get_ne]
    · simp
    · native_decide
  · native_decide

theorem bytesStoreLiteSetChunk_storageTypeAt {chunkIndex : UInt256} :
    storageTypeAt? bytesStoreLiteContract.storage (bytesStoreLiteSetChunkRefOf chunkIndex) =
      some .bytes := by
  simp [bytesStoreLiteSetChunkRefOf, storageTypeAt?,
    bytesStoreLiteContract, storageDecls, bytesSt, storageTypeStep?]

theorem accountMapEquiv_setChunkHeaderStore {σ : AccountMap} {evm : EVM.State}
    (I : ExecutionEnv) (owner : AccountAddress) (header : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
  accountMapEquiv
      (sstoreAccountMap owner σ (bytesStoreLiteSetChunkSlot I) header)
      (Solm.EVM.storageStore evm owner (bytesStoreLiteSetChunkSlot I) header).accountMap := by
  exact accountMapEquiv_bytesHeaderStore owner (bytesStoreLiteSetChunkSlot I) header hAccounts

theorem bytesStoreLiteSetChunkRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLiteLayout
        { bytesStoreLiteSetChunkRef I with
          steps := (bytesStoreLiteSetChunkRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreLiteSetChunkSlot I := by
  refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetChunkSlot I) evm, ?_, ?_⟩
  · have hnonneg : ¬ ((bytesStoreLiteSetChunkIndexWord I).toNat : Int) < 0 := by
      omega
    simp [bytesStoreLiteLayout, bytesStoreLiteSetChunkRef, bytesStoreLiteSetChunkRefOf,
      chunksElemSlot?, nonnegativeIndexSlot?, bytesStoreLiteSetChunkSlot, u256_ofNat_toNat]
    simp [hnonneg]
  · simp [bytesLikeLengthLoc]

theorem bytesStoreLiteSetChunkEvalStorageRefOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat) :
    evalStorageRef bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value)
      evm (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreLiteSetChunkRefOf chunkIndex) := by
  have hgetIndex :
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
        some (.int (Int.ofNat chunkIndex.toNat)) :=
    bytesStoreLiteSetChunkLocalsOf_get_chunkIndex chunkIndex value
  have hkey :
      valueToKey? (.int (Int.ofNat chunkIndex.toNat)) =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkFrameOf chunkIndex value).contract.storage "chunks" []
        (.int (Int.ofNat chunkIndex.toNat)) = .ok () := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig,
      bytesStoreLiteSetChunkFrameOf, bytesStoreLiteContract, storageDecls, bytesSt,
      bytesStoreLiteStorageLayout, solidityStorageLayout, bytesStoreLiteLayout,
      bytesStoreLiteStorageLocLoad_uint256, hload] using hbound
  simpa [chunkRef, bytesStoreLiteSetChunkFrameOf, bytesStoreLiteSetChunkRefOf] using
    (evalStorageRef_aindex_var_of_get?_ok
      (cfg := bytesStoreLiteConfig)
      (solm := bytesStoreLiteSetChunkFrameOf chunkIndex value)
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

theorem bytesStoreLiteSetChunkEvalStorageRefRevertsOfChunksLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    evalStorageRef bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value)
      evm (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetIndex :
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
        some (.int (Int.ofNat chunkIndex.toNat)) :=
    bytesStoreLiteSetChunkLocalsOf_get_chunkIndex chunkIndex value
  have hkey :
      valueToKey? (.int (Int.ofNat chunkIndex.toNat)) =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    simp [valueToKey?]
  have hbounds :
      arrayIndexInBounds? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkFrameOf chunkIndex value).contract.storage "chunks" []
        (.int (Int.ofNat chunkIndex.toNat)) = .revert := by
    simpa [arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig,
      bytesStoreLiteSetChunkFrameOf, bytesStoreLiteContract, storageDecls, bytesSt,
      bytesStoreLiteStorageLayout, solidityStorageLayout, bytesStoreLiteLayout,
      bytesStoreLiteStorageLocLoad_uint256, hload] using Nat.le_of_not_gt hbound
  simpa [chunkRef, bytesStoreLiteSetChunkFrameOf] using
    (evalStorageRef_aindex_var_of_get?_revert
      (cfg := bytesStoreLiteConfig)
      (solm := bytesStoreLiteSetChunkFrameOf chunkIndex value)
      (evm := evm) (base := "chunks") (name := "chunkIndex")
      hgetIndex hkey hbounds)

def bytesStoreLiteSetChunkHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetChunkSlot I) ⟨0⟩)

theorem bytesStoreLiteSetChunkHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreLiteSetChunkHeaderWord σ_evm I =
      bytesStoreLiteSetChunkHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreLiteSetChunkSlot I) ⟨0⟩

theorem bytesStoreLiteStorageLoadSetChunkHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLiteSetChunkSlot I) =
      bytesStoreLiteSetChunkHeaderWord σ_evm I := by
  simpa [bytesStoreLiteSetChunkHeaderWord] using
    bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreLiteSetChunkSlot I) hAccounts

theorem bytesStoreLiteSetChunkAccountExistsOfBound {σ : AccountMap} {I : ExecutionEnv}
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ acc, σ.find? I.codeOwner = some acc := by
  cases hacc : σ.find? I.codeOwner with
  | none =>
      have hzero : bytesStoreLiteChunksLengthWord σ I = ⟨0⟩ := by
        unfold bytesStoreLiteChunksLengthWord
        rw [hacc]
        rfl
      rw [hzero] at hbound
      exact False.elim (Nat.not_lt_zero _ hbound)
  | some acc =>
      exact ⟨acc, rfl⟩

theorem bytesStoreLiteSetChunkResolveOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value) evm
      (chunkRef (.var "chunkIndex")) =
        .ok (bytesStoreLiteSetChunkRefOf chunkIndex, .bytes) := by
  have hgetChunks :
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunks" = none :=
    bytesStoreLiteSetChunkLocalsOf_get_chunks_none chunkIndex value
  have her'' :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkLocalsOf chunkIndex value }
        evm { base := "chunks", steps := [.aindex (.var "chunkIndex")] } =
          .ok (bytesStoreLiteSetChunkRefOf chunkIndex) := by
    simpa [chunkRef, bytesStoreLiteSetChunkFrameOf] using
      (bytesStoreLiteSetChunkEvalStorageRefOfLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact resolveStorageRef?_ok hgetChunks her'' bytesStoreLiteSetChunk_storageTypeAt

theorem bytesStoreLiteSetChunkResolveRevertsOfChunksLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value) evm
      (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetChunks :
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunks" = none :=
    bytesStoreLiteSetChunkLocalsOf_get_chunks_none chunkIndex value
  have herInline :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkLocalsOf chunkIndex value }
        evm (chunkRef (.var "chunkIndex")) = .revert := by
    simpa [bytesStoreLiteSetChunkFrameOf] using
      (bytesStoreLiteSetChunkEvalStorageRefRevertsOfChunksLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunks herInline

theorem bytesStoreLiteSetChunkAssignOfLength {evm evm' : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkRefOf chunkIndex) .bytes (.bytes value) = .ok evm') :
    assignStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value)
      evm .storage (chunkRef (.var "chunkIndex")) (.bytes value) =
        .ok (bytesStoreLiteSetChunkFrameOf chunkIndex value, evm') := by
  have hresolve :=
    bytesStoreLiteSetChunkResolveOfLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  exact assignStorageRef_storage_bytes_ok_of_write hresolve hwrite

theorem bytesStoreLiteSetChunkLengthAfterWrite {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray} {n : Nat}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hlen :
      readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkRefOf chunkIndex) = .ok n) :
    evalExpr? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value)
      evm (.arrayLength .storage (chunkRef (.var "chunkIndex"))) =
        .ok (.int n) := by
  have hgetIndex :
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunkIndex" =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    unfold bytesStoreLiteSetChunkLocalsOf
    rw [store_get_ne]
    · exact store_get_self (∅ : Store) "chunkIndex" (.int (Int.ofNat chunkIndex.toNat))
    · native_decide
  have hgetIndexElem :
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value)["chunkIndex"]? =
        some (.int (Int.ofNat chunkIndex.toNat)) := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetIndex
  have hresolve :=
    bytesStoreLiteSetChunkResolveOfLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  rw [evalExpr?]
  rw [hresolve]
  simp [readStorageArrayLength?, hlen, EvalResult.bind, bind, pure]

theorem bytesStoreLiteSetChunkLengthRevertsOfChunksLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    evalExpr? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value)
      evm (.arrayLength .storage (chunkRef (.var "chunkIndex"))) = .revert := by
  have hresolve :=
    bytesStoreLiteSetChunkResolveRevertsOfChunksLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  rw [evalExpr?]
  rw [hresolve]
  simp [EvalResult.bind, bind]

theorem bytesStoreLiteSetChunkBodyReturnsOfWrite {evm evm' : EVM.State}
    {chunkIndex chunksLen chunksLenPost : UInt256} {value : ByteArray} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkRefOf chunkIndex) .bytes (.bytes value) = .ok evm')
    (hloadAfter :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hboundPost : chunkIndex.toNat < chunksLenPost.toNat)
    (hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evm'
        (bytesStoreLiteSetChunkRefOf chunkIndex) = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf chunkIndex value)
        evm' (some (.int n))) := by
  let solm0 := bytesStoreLiteSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreLiteSetChunkFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) =
          .ok (solm0, evm') := by
    simpa [solm0] using
      bytesStoreLiteSetChunkAssignOfLength
        (evm := evm) (evm' := evm') (chunkIndex := chunkIndex) (value := value)
        hload hbound hwrite
  have hret :
      evalExpr? bytesStoreLiteConfig solm0 evm'
        (.arrayLength .storage (chunkRef (.var "chunkIndex"))) =
          .ok (.int n) := by
    simpa [solm0] using
      bytesStoreLiteSetChunkLengthAfterWrite
        (evm := evm') (chunkIndex := chunkIndex) (chunksLen := chunksLenPost) (value := value)
        hloadAfter hboundPost hlenChunk
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteSetChunkBodyReturnRevertsOfPostChunksLength {evm evm' : EVM.State}
    {chunkIndex chunksLen chunksLenPost : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkRefOf chunkIndex) .bytes (.bytes value) = .ok evm')
    (hloadAfter :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩ = chunksLenPost)
    (hboundPost : ¬ chunkIndex.toNat < chunksLenPost.toNat) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body .reverted := by
  let solm0 := bytesStoreLiteSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreLiteSetChunkFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) =
          .ok (solm0, evm') := by
    simpa [solm0] using
      bytesStoreLiteSetChunkAssignOfLength
        (evm := evm) (evm' := evm') (chunkIndex := chunkIndex) (value := value)
        hload hbound hwrite
  have hret :
      evalExpr? bytesStoreLiteConfig solm0 evm'
        (.arrayLength .storage (chunkRef (.var "chunkIndex"))) = .revert := by
    simpa [solm0] using
      bytesStoreLiteSetChunkLengthRevertsOfChunksLength
        (evm := evm') (chunkIndex := chunkIndex) (chunksLen := chunksLenPost)
        (value := value) hloadAfter hboundPost
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem bytesStoreLiteSetChunkBodyRevertsOfWrite {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : chunkIndex.toNat < chunksLen.toNat)
    (hwrite :
      writeStorage? bytesStoreLiteConfig evm
        (bytesStoreLiteSetChunkRefOf chunkIndex) .bytes (.bytes value) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body .reverted := by
  let solm0 := bytesStoreLiteSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreLiteSetChunkFrameOf] using hlookup)
  have hresolve :=
    bytesStoreLiteSetChunkResolveOfLength
      (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
      hload hbound
  have hresolve0 :
      resolveStorageRef? bytesStoreLiteConfig solm0 evm
        (chunkRef (.var "chunkIndex")) =
          .ok (bytesStoreLiteSetChunkRefOf chunkIndex, .bytes) := by
    simpa [solm0] using hresolve
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) = .revert := by
    exact assignStorageRef_storage_bytes_revert_of_write hresolve0 hwrite
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetChunkResolveRevertsOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetChunkFrameOf chunkIndex value) evm
      (chunkRef (.var "chunkIndex")) = .revert := by
  have hgetChunksGet :
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "chunks" = none :=
    bytesStoreLiteSetChunkLocalsOf_get_chunks_none chunkIndex value
  have her'' :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetChunkLocalsOf chunkIndex value }
        evm { base := "chunks", steps := [.aindex (.var "chunkIndex")] } = .revert := by
    simpa [chunkRef, bytesStoreLiteSetChunkFrameOf] using
      (bytesStoreLiteSetChunkEvalStorageRefRevertsOfChunksLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact resolveStorageRef?_revert_of_evalStorageRef_revert hgetChunksGet her''

theorem bytesStoreLiteSetChunkBodyBoundsRevertsOfLength {evm : EVM.State}
    {chunkIndex chunksLen : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = chunksLen)
    (hbound : ¬ chunkIndex.toNat < chunksLen.toNat) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetChunkLocalsOf chunkIndex value)
      setChunkTransition.body .reverted := by
  let solm0 := bytesStoreLiteSetChunkFrameOf chunkIndex value
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetChunkLocalsOf chunkIndex value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetChunkLocalsOf
      exact store_get_self ((∅ : Store).insert "chunkIndex"
        (.int (Int.ofNat chunkIndex.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreLiteSetChunkFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm0 evm .storage
        (chunkRef (.var "chunkIndex")) (.bytes value) = .revert := by
    exact assignStorageRef_storage_revert_of_resolve
      (bytesStoreLiteSetChunkResolveRevertsOfLength
        (evm := evm) (chunkIndex := chunkIndex) (chunksLen := chunksLen) (value := value)
        hload hbound)
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetChunkWriteEmptyOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩)
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
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetChunkSlot I) ⟨0⟩
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
      (.bytes (bytesStoreLiteSetChunkValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize0 : (bytesStoreLiteSetChunkValueBytes I).size = 0 := by
    rw [bytesStoreLiteSetChunkValueBytes_size hpayload, hlenZero]
    rfl
  have hvalueEmpty : bytesStoreLiteSetChunkValueBytes I = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero (bytesStoreLiteSetChunkValueBytes I) hvalueSize0
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkSlot I) =
        bytesStoreLiteSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := bytesStoreLiteWriteEmptyChunkShortPacked
    (evm := evmSolm0)
    (oldLen := bytesStoreLiteSetChunkIndexWord I)
    (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
    (len := oldLen)
    (by simpa [bytesStoreLiteSetChunkSlot] using hload)
    (by simpa [bytesStoreLiteSetChunkSlot] using hpacked)
    hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreLiteSetChunkRefOf, bytesStoreLiteSetChunkSlot, hvalueEmpty]
    using hwrite

theorem bytesStoreLiteSetChunkWriteShortOldShortPacked
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
      UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord (bytesStoreLiteSetChunkValueBytes I))
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
      (.bytes (bytesStoreLiteSetChunkValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : (bytesStoreLiteSetChunkValueBytes I).size < 32 := by
    rw [bytesStoreLiteSetChunkValueBytes_size hpayload, ← hlenAbi]
    exact hshort
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkSlot I) =
        bytesStoreLiteSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreLiteSetChunkSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := bytesStoreLiteWriteChunkShortPacked
    (evm := evmSolm0)
    (oldLen := bytesStoreLiteSetChunkIndexWord I)
    (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
    (len := oldLen)
    (value := bytesStoreLiteSetChunkValueBytes I)
    hvalueSize
    (by simpa [bytesStoreLiteSetChunkSlot] using hload)
    (by simpa [bytesStoreLiteSetChunkSlot] using hpacked)
    hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreLiteSetChunkRefOf, bytesStoreLiteSetChunkSlot]
    using hwrite

theorem bytesStoreLiteSetChunkShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetChunkSlot I)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (bytesStoreLiteSetChunkSlot I) storedWord)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (bytesStoreLiteSetChunkSlot I) 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner (bytesStoreLiteSetChunkSlot I)
          (solidityShortBytesWord value)).accountMap := by
  exact accountMapEquiv_setBytesShortFromLongPostAccountMapEquiv
    (baseSlot := bytesStoreLiteSetChunkSlot I)
    (oldLen := oldLen) (storedWord := storedWord) (value := value)
    hAccounts hstored holdLenLt

theorem bytesStoreLiteSetChunkLengthAfterEmptyWrite
    {cA gh bl σ_solm σ₀ A I} {g : UInt256} :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetChunkSlot I) ⟨0⟩
    readStorageBytesLength? bytesStoreLiteConfig evmSolm1
      (bytesStoreLiteSetChunkRef I) = .ok 0 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  exact bytesStoreLiteReadLengthAfterHeaderStoreZero
    (er := bytesStoreLiteSetChunkRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreLiteSetChunkSlot I) (by rfl)
    (by simpa [evmSolm1] using bytesStoreLiteSetChunkRef_length_slot evmSolm1 I)

theorem bytesStoreLiteSetChunkLengthAfterShortWrite
    {cA gh bl σ_solm σ₀ A I} {g len payloadStart : UInt256} {acc : Account}
    (hacc : σ_solm.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetChunkSlot I) storedWord
    readStorageBytesLength? bytesStoreLiteConfig evmSolm1
      (bytesStoreLiteSetChunkRef I) = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) storedWord
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
  exact bytesStoreLiteReadLengthAfterHeaderStorePresent
    (er := bytesStoreLiteSetChunkRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreLiteSetChunkSlot I) (header := storedWord) (len := len.toNat)
    (by rfl)
    (by simpa [evmSolm1] using bytesStoreLiteSetChunkRef_length_slot evmSolm1 I)
    (by simpa [evmSolm0, initState] using hacc)
    hdecode

theorem bytesStoreLiteSetChunkSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteReachSetChunkDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2154⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨409⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreLiteReachSetChunk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, by
    simpa [bytesStoreLiteSetChunkEntryPc] using
      (evm_run hreach with [
        jumpdest, push2 ⟨263⟩, push2 ⟨409⟩, calldatasize, push1 ⟨4⟩,
        push2 ⟨2154⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setChunkDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setChunkDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetChunkDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setChunkDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetChunkDecoder
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

theorem bytesStoreLiteX_setChunkDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetChunkDecoder
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

theorem bytesStoreLiteX_setChunkDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetChunkDecoder
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

theorem bytesStoreLiteX_setChunkDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetChunkDecoder
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
theorem bytesStoreLiteX_setChunkDecodeValidRaw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    ∃ k C, RD bytesStoreLiteBytecode I g
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
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetChunkDecoder
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

theorem bytesStoreLiteX_setChunkOobFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1144⟩ := hreach
  have rd1152 := evm_run rd1144 with [
    jumpdest, push0, dup3, dup3, push1 ⟨1⟩, dup7, dup2]
  obtain ⟨_, _, rd1153₀⟩ := rd1152.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1153⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1153⟩
        [bytesStoreLiteChunksLengthWord σ I, chunkIndex, ⟨1⟩, len, payloadStart, ⟨0⟩,
          len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1153₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreLiteChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1153 with [
    dup2, lt, push2 ⟨1166⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨1166⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkReachWriteHelperFromBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩, chunksDataBase + chunkIndex,
        ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1144⟩ := hreach
  have rd1152 := evm_run rd1144 with [
    jumpdest, push0, dup3, dup3, push1 ⟨1⟩, dup7, dup2]
  obtain ⟨_, _, rd1153₀⟩ := rd1152.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1153⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1153⟩
        [bytesStoreLiteChunksLengthWord σ I, chunkIndex, ⟨1⟩, len, payloadStart, ⟨0⟩,
          len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1153₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreLiteChunksLengthWord σ I) = ⟨1⟩ :=
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
      (by native_decide) mem_cost bytesStoreLiteChunkLengthSlotHash
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd1173 with [
    add, swap2, dup3, push2 ⟨1187⟩, swap3, swap2, swap1, push2 ⟨2599⟩,
    jump (by native_decide)]⟩

theorem bytesStoreLiteX_setChunkReachWriteHeaderDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      ((σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: (chunksDataBase + chunkIndex) ::
        payloadStart :: len :: ⟨1187⟩ :: (chunksDataBase + chunkIndex) ::
        ⟨0⟩ :: len :: payloadStart :: chunkIndex :: ⟨263⟩ ::
        bytesStoreLiteSelWord I :: [])
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreLiteX_setChunkReachWriteHelperFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound
  exact bytesStoreLiteX_writeBytesHelperReachHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
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
            ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩, chunksDataBase + chunkIndex,
        ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreLiteX_setChunkReachWriteHelperFromBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound
  exact bytesStoreLiteX_writeBytesHelperShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax hflag hvalid
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkLongMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
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
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let header : UInt256 :=
    σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)
  have hdecoder := bytesStoreLiteX_setChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) hreach hbound hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩,
      chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    hdecoder
    (by simpa [header] using hflag)
    (by simpa [header] using hbad)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkShortMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
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
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let header : UInt256 :=
    σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)
  have hdecoder := bytesStoreLiteX_setChunkReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) hreach hbound hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, chunksDataBase + chunkIndex, payloadStart, len, ⟨1187⟩,
      chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)
    hdecoder
    (by simpa [header] using hflag)
    (by simpa [header] using hbad)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkShortOldLongReachWriteBranchWithLoopSchedule
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
    (hshort : len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩) =
        ⟨0⟩) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩ fuel
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
  have holdGtNat : 31 < oldStoredLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩ :=
    ugt_one (by omega)
  have hshortWord : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hloopEntry := bytesStoreLiteX_writeBytesCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
      chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := (⟨0⟩ : UInt256) + bytesLikeDataBase slot)
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

theorem bytesStoreLiteX_setChunkShortOldLongReachWriteBranch
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
    (hshort : len.toNat < 32) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1187⟩, slot, ⟨0⟩, len, payloadStart,
        chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
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
    bytesStoreLiteX_setChunkShortOldLongReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hbound hlenMax hflag holdStoredLen hvalid hshort hcontinue hdone

theorem bytesStoreLiteX_setChunkShortNonemptyOldLongWriteReturnsToBody
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
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear slot
        (bytesStoreLiteSetChunkShortStoredWord I len payloadStart)) k C := by
  dsimp only
  let slot : UInt256 := chunksDataBase + chunkIndex
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hbranch := bytesStoreLiteX_setChunkShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hshort
  have hwrite := bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [slot, σClear] using hbranch) hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot
      (bytesStoreLiteSetChunkShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [bytesStoreLiteSetChunkShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkEmptyOldLongWriteReturnsToBody
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
    let slot : UInt256 := chunksDataBase + chunkIndex
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
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
  have hbranch := bytesStoreLiteX_setChunkShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (chunkIndex := chunkIndex) (oldStoredLen := oldStoredLen)
    hperm hreach hbound hlenMax hflag holdStoredLen hvalid hshort
  have hpacked := bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [slot, σClear] using hbranch) hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreLiteX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hwrite
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkEmptyWriteReturnsToBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart chunkIndex : UInt256}
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
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩)
      k C := by
  have hbranch := bytesStoreLiteX_setChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound hlenMax hflag hvalid
  have hpacked := bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hbranch hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreLiteX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hwrite (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkShortNonemptyWriteReturnsToBody
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
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord : UInt256 :=
      UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
        (UInt256.land
          (UInt256.lnot
            (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
          (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1187⟩
      [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) storedWord) k C := by
  dsimp only
  have hbranch := bytesStoreLiteX_setChunkShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hreach hbound hlenMax hflag hvalid
  have hwrite := bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1187⟩)
    (tail := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hbranch hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
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
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    (by simpa using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkReturnFromDecodedLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {chunkLen slot len payloadStart chunkIndex : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1002⟩
      [chunkLen, slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [chunkLen, bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd1002⟩ := hreach
  exact ⟨_, _, evm_run rd1002 with [
    jumpdest, swap6, swap5, pop, pop, pop, pop, pop, jump (by native_decide)]⟩

theorem bytesStoreLiteSetChunkEmptyHeaderAfterWrite
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

theorem bytesStoreLiteX_setChunkReachReturnLengthDecoder
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
        ⟨1002⟩, chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3)
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
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
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
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1218⟩
        [(σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)),
          chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
          bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [initState] using rd1218₀⟩
  exact ⟨_, _, evm_run rd1218 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_panic32MemFromReachSetChunk
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2579⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2579⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2591₀ := evm_run rd2579 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2591 := rd2591₀
  rw [hsel] at rd2591
  exact evm_run rd2591 with [
    raw mstore 0 (bytesStoreLiteFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreLiteFullPanicMemFrom ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreLiteX_setChunkReturnOobChunksLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart chunkIndex : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1187⟩
      [slot, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hbound : ¬ chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd1187⟩ := hreach
  have rd1193 := evm_run rd1187 with [
    jumpdest, pop, push1 ⟨1⟩, dup5, dup2]
  obtain ⟨_, _, rd1194₀⟩ := rd1193.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1194⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1194⟩
        [bytesStoreLiteChunksLengthWord σ I, chunkIndex, ⟨1⟩, ⟨0⟩, len, payloadStart,
          chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteChunksLengthWord, initState] using rd1194₀⟩
  have hlt : UInt256.lt chunkIndex (bytesStoreLiteChunksLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1194 with [
    dup2, lt, push2 ⟨1207⟩, jumpiNT (by simpa using hlt),
    push2 ⟨1207⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32MemFromReachSetChunk ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setChunkEmptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hboundPost :
      chunkIndex.toNat <
        (bytesStoreLiteChunksLengthWord
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
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  dsimp only
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) ⟨0⟩
  have hbody := bytesStoreLiteX_setChunkEmptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hperm hreach hbound hlenMax hflag hvalid hlenZero
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ' I).toNat := by
    simpa [σ'] using hboundPost
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (by simpa [σ'] using hbody) hbound'
  have hheader : (σ'.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) = ⟨0⟩ := by
    simpa [σ'] using bytesStoreLiteSetChunkEmptyHeaderAfterWrite σ I chunkIndex
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [chunksDataBase + chunkIndex, ⟨0⟩, len, payloadStart, chunkIndex, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
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
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)
        (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

theorem bytesStoreLiteX_setChunkShortNonemptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart chunkIndex : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1144⟩
      [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hboundPost :
      chunkIndex.toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex)
            (bytesStoreLiteSetChunkShortStoredWord I len payloadStart)) I).toNat)
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
    let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) storedWord
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray len) := by
  dsimp only
  let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) storedWord
  let header : UInt256 :=
    σ'.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)
  have hbody := bytesStoreLiteX_setChunkShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hperm hreach hbound hlenMax hflag hvalid hnz hshort
  have hbound' : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ' I).toNat := by
    simpa [σ', storedWord] using hboundPost
  have hdecoder := bytesStoreLiteX_setChunkReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := chunksDataBase + chunkIndex)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (by
      simpa [σ', storedWord, bytesStoreLiteSetChunkShortStoredWord] using hbody)
    hbound'
  have hdata :
      (σ'.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + chunkIndex) ⟨0⟩)) =
        storedWord := by
    have hnzStored := bytesStoreLiteSetChunkShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simpa [σ', storedWord] using
      sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc
        (chunksDataBase + chunkIndex) storedWord hacc hnzStored
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
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
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
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨1⟩ : UInt256) (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteX_setChunkOob {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
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
      ¬ (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := bytesStoreLiteX_setChunkDecodeValidRaw
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMax hpayload
  exact bytesStoreLiteX_setChunkOobFromBody (g := g) hreach (by
    simpa [bytesStoreLiteSetChunkIndexWord, calldataWord] using hbound)

theorem bytesStoreLiteDecode_setChunk_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_short (cd := I.calldata) (x := "chunkIndex")
      (y := "value") hshort

theorem bytesStoreLiteDecode_setChunk_none_totalHuge {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_total_huge (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hbig

theorem bytesStoreLiteDecode_setChunk_none_offsetHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_offset_huge (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hsz68 hsizeSign hoff

theorem bytesStoreLiteDecode_setChunk_none_lengthShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32) :
    decodeCalldata (setChunkTransition.params.map Param.name)
      (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_length_short (cd := I.calldata)
      (x := "chunkIndex") (y := "value") hsz68 hsizeSign hoffMax hshort

theorem bytesStoreLiteDecode_setChunk_none_lengthHuge {I : ExecutionEnv}
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

theorem bytesStoreLiteDecode_setChunk_none_payloadShort {I : ExecutionEnv}
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

theorem bytesStoreLiteDecode_setChunk {I : ExecutionEnv}
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
        some (bytesStoreLiteSetChunkLocals I) := by
  show decodeCalldata ["chunkIndex", "value"] [uint256, .bytes] I.calldata =
    some (bytesStoreLiteSetChunkLocals I)
  simpa [uint256, abiUInt256, bytesStoreLiteSetChunkLocals,
    bytesStoreLiteSetChunkIndexWord, bytesStoreLiteSetChunkValueBytes] using
    decodeCalldata_uint256_bytes_some (cd := I.calldata) (x := "chunkIndex")
      (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem bytesStoreLiteSetChunkDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkSelector_size hsel
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk_none_short (I := I) hshort
  exact (bytesStoreLiteX_setChunkDecodeShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hshort hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkSelector_size hsel
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk_none_totalHuge (I := I) (by omega)
  exact (bytesStoreLiteX_setChunkDecodeHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hbig hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setChunkTransition.params.map Param.name)
        (transitionSignature setChunkTransition).paramTypes I.calldata = none := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · exact bytesStoreLiteDecode_setChunk_none_offsetHuge (I := I)
        hsz68 hsizeSign hoff
    · exact bytesStoreLiteDecode_setChunk_none_totalHuge (I := I)
        (Nat.le_of_not_gt hsizeSign)
  exact (bytesStoreLiteX_setChunkDecodeOffsetHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk_none_lengthShort (I := I)
    hsz68 hsizeSign hoffMax hlenShort
  exact (bytesStoreLiteX_setChunkDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk_none_lengthHuge (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenHuge
  exact (bytesStoreLiteX_setChunkDecodeLengthHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk_none_payloadShort (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenMax hpayloadList
  exact (bytesStoreLiteX_setChunkDecodePayloadShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetChunkEmptyOldShortRuntimeOfReach_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256}
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
    (hboundPost :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) ⟨0⟩) I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkEmptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart)
        (chunkIndex := chunkIndex)
        hperm hreach hboundChunk (by simpa [σFinal, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hboundPost) hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hlenZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreLiteSetChunkValueBytes I)) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreLiteSetChunkWriteEmptyOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hAccounts hpayloadList hlenZeroAbi hflag hvalid
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σFinal I := by
    exact bytesStoreLiteStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm1
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) = .ok 0 := by
    simpa [evmSolm0, evmSolm1, bytesStoreLiteSetChunkRef, bytesStoreLiteSetChunkRefOf]
      using bytesStoreLiteSetChunkLengthAfterEmptyWrite
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I)
          (bytesStoreLiteSetChunkValueBytes I)) evmSolm1 (some (.int 0))) := by
    simpa [evmSolm0, evmSolm1, bytesStoreLiteSetChunkLocals,
      bytesStoreLiteSetChunkLocalsOf, bytesStoreLiteSetChunkIndexWord] using
      bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := bytesStoreLiteSetChunkValueBytes I)
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

theorem bytesStoreLiteSetChunkEmptyOldShortRuntimeOfReach_post_oob
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256}
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
    (hboundPost :
      ¬ (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) ⟨0⟩) I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hrev :
      RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    have hbodyReach := bytesStoreLiteX_setChunkEmptyWriteReturnsToBody
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
      hperm hreach hboundChunk hlenMax
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
        using hflag)
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
        using hvalid)
      hlenZero
    exact bytesStoreLiteX_setChunkReturnOobChunksLength
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm) (σ := σFinal)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (slot := bytesStoreLiteSetChunkSlot I) (len := len) (payloadStart := payloadStart)
      (chunkIndex := chunkIndex)
      (by simpa [σFinal, bytesStoreLiteSetChunkSlot, hchunkIndex] using hbodyReach)
      (by simpa [σFinal, bytesStoreLiteSetChunkSlot, hchunkIndex] using hboundPost)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreLiteSetChunkValueBytes I)) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1] using
      bytesStoreLiteSetChunkWriteEmptyOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hAccounts hpayloadList hlenZeroAbi hflag hvalid
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkSlot I) ⟨0⟩
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σFinal I := by
    exact bytesStoreLiteStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, bytesStoreLiteSetChunkLocals,
      bytesStoreLiteSetChunkLocalsOf, bytesStoreLiteSetChunkIndexWord] using
      bytesStoreLiteSetChunkBodyReturnRevertsOfPostChunksLength
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord σFinal I)
        (value := bytesStoreLiteSetChunkValueBytes I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter
        (by simpa [σFinal] using hboundPost)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkShortNonemptyOldShortRuntimeOfReach_of_post_bound
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
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hboundPost :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            (bytesStoreLiteSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord value)
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) storedWord
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    simpa [σFinal, storedWord, bytesStoreLiteSetChunkSlot, hchunkIndex] using
      bytesStoreLiteX_setChunkShortNonemptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
        (acc := accEvm)
        hperm hreach hboundChunk
        (by simpa [σFinal, storedWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hboundPost) hlenMax
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hflag)
        (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
          using hvalid)
        hnz hshort haccEvm
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value] using
      bytesStoreLiteSetChunkWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using
      bytesStoreLiteSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState, hstored] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord value)
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σFinal I := by
    exact bytesStoreLiteStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hvalueSize : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetChunkValueBytes_size hpayloadList, ← hlenAbi]
  have hlenChunk :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm1
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) =
          .ok value.size := by
    have hlen₀ := bytesStoreLiteSetChunkLengthAfterShortWrite
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (len := len) (payloadStart := payloadStart) (acc := accSolm)
      haccSolm hnz hshort
    simpa [evmSolm0, evmSolm1, value, storedWord, hstored, hvalueSize,
      bytesStoreLiteSetChunkRef, bytesStoreLiteSetChunkRefOf] using hlen₀
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body
        (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
          evmSolm1 (some (.int value.size))) := by
    have hbody₀ := bytesStoreLiteSetChunkBodyReturnsOfWrite
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := value)
        (n := value.size)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter hboundPost hlenChunk
    change ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
      (bytesStoreLiteSetChunkLocalsOf (bytesStoreLiteSetChunkIndexWord I) value)
      setChunkTransition.body
      (.returned (bytesStoreLiteSetChunkFrameOf (bytesStoreLiteSetChunkIndexWord I) value)
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
theorem bytesStoreLiteSetChunkShortNonemptyOldShortRuntimeOfReach_post_oob
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart chunkIndex : UInt256}
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
    (hboundPost :
      ¬ (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            (bytesStoreLiteSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetChunkValueBytes I
  let storedWord := bytesStoreLiteSetChunkShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord value)
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) storedWord
  have hrev :
      RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    have hboundChunk : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ_evm I).toNat := by
      rw [hchunkIndex]
      exact hbound
    have hbodyReach := bytesStoreLiteX_setChunkShortNonemptyWriteReturnsToBody
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
      hperm hreach hboundChunk hlenMax
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
        using hflag)
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot, hchunkIndex]
        using hvalid)
      hnz hshort
    exact bytesStoreLiteX_setChunkReturnOobChunksLength
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm) (σ := σFinal)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (slot := bytesStoreLiteSetChunkSlot I) (len := len) (payloadStart := payloadStart)
      (chunkIndex := chunkIndex)
      (by simpa [σFinal, storedWord, bytesStoreLiteSetChunkSlot, hchunkIndex,
          bytesStoreLiteSetChunkShortStoredWord] using hbodyReach)
      (by simpa [σFinal, storedWord, bytesStoreLiteSetChunkSlot, hchunkIndex] using hboundPost)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value] using
      bytesStoreLiteSetChunkWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using
      bytesStoreLiteSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState, hstored] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkSlot I) (solidityShortBytesWord value)
  have hloadAfter :
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σFinal I := by
    exact bytesStoreLiteStorageLoadChunksLength_of_accountMapEquiv
      (evm := evmSolm1) (σ := σFinal) (τ := σFinal) (I := I)
      (by simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv])
      hAccountsPost rfl
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, evmSolm1, value, bytesStoreLiteSetChunkLocals,
      bytesStoreLiteSetChunkLocalsOf, bytesStoreLiteSetChunkIndexWord] using
      bytesStoreLiteSetChunkBodyReturnRevertsOfPostChunksLength
        (evm := evmSolm0) (evm' := evmSolm1)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord σFinal I)
        (value := value)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hbound hwrite hloadAfter
        (by simpa [σFinal] using hboundPost)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkEmptyOldShortRuntime_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
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
    (hboundPost :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) ⟨0⟩) I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
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
  exact bytesStoreLiteSetChunkEmptyOldShortRuntimeOfReach_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hcode hperm hwv hAccounts hreach hchunkIndex hd hdec hpayloadList hlenMaxLen hbound
    hboundPost hflag hvalid hlenZeroLen hlenZero

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkShortNonemptyOldShortRuntime_of_post_bound
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
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            (bytesStoreLiteSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
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
  exact bytesStoreLiteSetChunkShortNonemptyOldShortRuntimeOfReach_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    (accEvm := accEvm)
    hcode hperm hwv hAccounts haccEvm hreach hchunkIndex hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen hbound
    (by simpa [len, payloadStart] using hboundPost) hflag hvalid hnzLen hshortLen

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetChunkShortNonemptyOldShortRuntime_post_oob
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
      ¬ (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
            (bytesStoreLiteSetChunkShortStoredWord I len payloadStart)) I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
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
  exact bytesStoreLiteSetChunkShortNonemptyOldShortRuntimeOfReach_post_oob
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (chunkIndex := chunkIndex)
    hcode hperm hwv hAccounts hreach hchunkIndex hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen hbound
    (by simpa [len, payloadStart] using hboundPost) hflag hvalid hnzLen hshortLen

theorem bytesStoreLiteSetChunkShortOldShortRuntime
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
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hzero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩
  · by_cases hboundPost :
        (bytesStoreLiteSetChunkIndexWord I).toNat <
          (bytesStoreLiteChunksLengthWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I) ⟨0⟩) I).toNat
    · exact bytesStoreLiteSetChunkEmptyOldShortRuntime_of_post_bound
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
      have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1144⟩
          [len, payloadStart, chunkIndex, ⟨263⟩, bytesStoreLiteSelWord I]
          solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
        dsimp [len, payloadStart, chunkIndex]
        exact bytesStoreLiteX_setChunkDecodeValidRaw
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g)
          hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
      have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata)
        (by simpa [selIs] using hsel)
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
        exact bytesStoreLiteSetChunkRawLengthWord_zero I hoffMax hzero
      have hchunkIndex : chunkIndex = bytesStoreLiteSetChunkIndexWord I := by
        dsimp [chunkIndex]
        rw [bytesStoreLiteSetChunkIndexWord, calldataWord]
        have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
        rw [h4]
      exact bytesStoreLiteSetChunkEmptyOldShortRuntimeOfReach_post_oob
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
      bytesStoreLiteSetChunkAccountExistsOfBound
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
        (bytesStoreLiteSetChunkIndexWord I).toNat <
          (bytesStoreLiteChunksLengthWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkSlot I)
              (bytesStoreLiteSetChunkShortStoredWord I len payloadStart)) I).toNat
    · exact bytesStoreLiteSetChunkShortNonemptyOldShortRuntime_of_post_bound
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hboundPost hflag hvalid
        hnz hshort
    · exact bytesStoreLiteSetChunkShortNonemptyOldShortRuntime_post_oob
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound
        (by simpa [len, payloadStart] using hboundPost) hflag hvalid hnz hshort

theorem bytesStoreLiteSetChunkLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
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
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hreach := bytesStoreLiteX_setChunkDecodeValidRaw
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreLiteX_setChunkLongMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hreach
      (by simpa [bytesStoreLiteSetChunkIndexWord, calldataWord] using hbound)
      hlenMaxWord
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot,
        bytesStoreLiteSetChunkIndexWord, calldataWord] using hflag)
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot,
        bytesStoreLiteSetChunkIndexWord, calldataWord] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (chunksDataBase + bytesStoreLiteSetChunkIndexWord I) =
        bytesStoreLiteSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, bytesStoreLiteSetChunkSlot] using
      bytesStoreLiteStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreLiteSetChunkValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreLiteSetChunkRefOf] using
      bytesStoreLiteWriteChunkMalformedLong
        (evm := evmSolm0)
        (oldLen := bytesStoreLiteSetChunkIndexWord I)
        (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
        (value := bytesStoreLiteSetChunkValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, bytesStoreLiteSetChunkLocals, bytesStoreLiteSetChunkLocalsOf,
      bytesStoreLiteSetChunkIndexWord] using
      bytesStoreLiteSetChunkBodyRevertsOfWrite
        (evm := evmSolm0)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := bytesStoreLiteSetChunkValueBytes I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks
        hbound
        hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
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
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hreach := bytesStoreLiteX_setChunkDecodeValidRaw
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreLiteX_setChunkShortMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hreach
      (by simpa [bytesStoreLiteSetChunkIndexWord, calldataWord] using hbound)
      hlenMaxWord
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot,
        bytesStoreLiteSetChunkIndexWord, calldataWord] using hflag)
      (by simpa [bytesStoreLiteSetChunkHeaderWord, bytesStoreLiteSetChunkSlot,
        bytesStoreLiteSetChunkIndexWord, calldataWord] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (chunksDataBase + bytesStoreLiteSetChunkIndexWord I) =
        bytesStoreLiteSetChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, bytesStoreLiteSetChunkSlot] using
      bytesStoreLiteStorageLoadSetChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetChunkRefOf (bytesStoreLiteSetChunkIndexWord I)) .bytes
        (.bytes (bytesStoreLiteSetChunkValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreLiteSetChunkRefOf] using
      bytesStoreLiteWriteChunkMalformedShort
        (evm := evmSolm0)
        (oldLen := bytesStoreLiteSetChunkIndexWord I)
        (header := bytesStoreLiteSetChunkHeaderWord σ_evm I)
        (value := bytesStoreLiteSetChunkValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [evmSolm0, bytesStoreLiteSetChunkLocals, bytesStoreLiteSetChunkLocalsOf,
      bytesStoreLiteSetChunkIndexWord] using
      bytesStoreLiteSetChunkBodyRevertsOfWrite
        (evm := evmSolm0)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := bytesStoreLiteSetChunkValueBytes I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks
        hbound
        hwrite
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkOobRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
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
      ¬ (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunk (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hloadChunks :
      Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨1⟩ =
          bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [initState] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetChunkLocals I) setChunkTransition.body .reverted := by
    simpa [bytesStoreLiteSetChunkLocals, bytesStoreLiteSetChunkLocalsOf,
      bytesStoreLiteSetChunkIndexWord] using
      bytesStoreLiteSetChunkBodyBoundsRevertsOfLength
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (chunkIndex := bytesStoreLiteSetChunkIndexWord I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (value := bytesStoreLiteSetChunkValueBytes I)
        (by simp only [initState]; exact hwv)
        (by simpa [initState] using hloadChunks)
        hbound
  exact (bytesStoreLiteX_setChunkOob
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkShortNewOldShortRuntime
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
    (hflag : UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hbound :
      (bytesStoreLiteSetChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat
  · by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetChunkShortOldShortRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflag hvalid hshort
    · exact bytesStoreLiteSetChunkShortMalformedRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound hflag
        (not_ne_iff.mp hvalid)
  · exact bytesStoreLiteSetChunkOobRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hbound

end BytesStoreLite
