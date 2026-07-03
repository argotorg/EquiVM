import Examples.BytesStoreLite.FullPushChunkLongStorage
import Examples.BytesStoreLite.FullSetLongOldLongReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStoreLite

theorem ugt_eq_zero_of_ne_one_local {a b : UInt256}
    (h : ¬ UInt256.gt a b = ⟨1⟩) : UInt256.gt a b = ⟨0⟩ := by
  by_cases hgt : a > b
  · exfalso
    apply h
    simp [UInt256.gt, UInt256.fromBool, hgt]
    native_decide
  · simp [UInt256.gt, UInt256.fromBool, hgt]
    native_decide

set_option maxHeartbeats 200000 in
theorem bytesStoreLitePushChunkLongNoTailShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (_hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.land (UInt256.div oldHeader ⟨2⟩) ⟨127⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
        (oldLen + ⟨1⟩))
      (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
    evmSolm0.executionEnv.codeOwner (chunksDataBase + oldLen) header
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
        (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32))
      (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [hlenEvm] using hlenMaxWord
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have hmod : len.toNat % 32 = 0 := by
    simpa [len] using hnoTailMod
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreLiteX_pushChunkLongNoTailReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter hvalidAfter hlong hmod
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, oldBytesLen, header, value] using
      bytesStoreLitePushChunkLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSizeLong hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have haddrBound :
      ∀ i, i < len.toNat / 32 → payloadStart.toNat + 32 * i < UInt256.size := by
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
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    have hbridge := accountMapEquiv_pushChunkLongNoTailStorage
      (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
      (σ_evm := σ_evm) (σ_solm := σ_solm)
      hAccounts hsrc haddrBound hsizeDecoded hlenAbiLocal hpayloadStartLocal hoffMax
      hmod (by simpa [header, value] using hheaderEq)
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
              (chunksDataBase + oldLen) value 0
              (solidityBytesDataWordCount value.size))
            (chunksDataBase + oldLen) header := by
      simp [evmSolm1, evmSolm0, value, header, initState, storageStore_accountMap,
        storageStore_executionEnv, writeSolidityBytesDataWordsFrom_accountMap]
    rw [hsolmMap]
    simpa [finalEvmMap, value, header] using hbridge
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv,
            writeSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 200000 in
theorem bytesStoreLitePushChunkLongNoTailShortPackedRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongNoTailShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hnewLong hnoTailMod hflag hvalid

set_option maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem bytesStoreLitePushChunkLongNoTailOldLongNoClearRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (_hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div postHeader ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.div oldHeader ⟨2⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen :=
    Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
      (oldLen + ⟨1⟩)
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel (oldFuel - clearFuel))
      (chunksDataBase + oldLen) value 0 clearFuel)
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel (oldFuel - clearFuel))
      (chunksDataBase + oldLen) value 0 clearFuel).executionEnv.codeOwner
    (chunksDataBase + oldLen) header
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
        (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32))
      (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [hlenEvm] using hlenMaxWord
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have hmod : len.toNat % 32 = 0 := by
    simpa [len] using hnoTailMod
  have holdLenLe : oldBytesLen.toNat ≤ len.toNat :=
    BytesStoreLiteCore.ugt_eq_zero_toNat_le
      (by simpa [oldBytesLen, oldHeader, len] using hgtOldNew)
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have holdAfter :
      oldBytesLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
          ⟨2⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (congrArg (fun w => UInt256.div w ⟨2⟩) hheaderAfter).symm
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hgtOldNewAfter : UInt256.gt oldBytesLen len = ⟨0⟩ := by
    simpa [oldBytesLen, oldHeader, len] using hgtOldNew
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreLiteX_pushChunkLongNoTailOldLongNoClearReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart) (oldStoredLen := oldBytesLen)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter holdAfter hvalidAfter
        hgtOldNewAfter hlong hmod
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, evmSolmLen, oldBytesLen, oldFuel, clearFuel, header, value,
      solidityBytesDataWordCount] using
      bytesStoreLitePushChunkLongOldLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSizeLong hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have haddrBound :
      ∀ i, i < len.toNat / 32 → payloadStart.toNat + 32 * i < UInt256.size := by
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
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner
              (clearDataWordsForwardFrom I.codeOwner
                (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
                (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel)
                (oldFuel - clearFuel))
              (chunksDataBase + oldLen) value 0 clearFuel)
            (chunksDataBase + oldLen) header := by
      simp [evmSolm1, evmSolmLen, evmSolm0, oldFuel, clearFuel, value, header,
        initState, storageStore_accountMap, storageStore_executionEnv,
        writeSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_accountMap,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv,
        bytesLikeDataBase, solidityBytesDataBaseSlot]
    rw [hsolmMap]
    simpa [finalEvmMap, value, header, oldFuel, clearFuel] using
      accountMapEquiv_pushChunkLongNoTailStorageOldLongNoClear
        (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
        (oldBytesLen := oldBytesLen) (σ_evm := σ_evm) (σ_solm := σ_solm)
        hAccounts hsrc haddrBound hsizeDecoded hlenAbiLocal hpayloadStartLocal hoffMax
        hmod (by simpa [header, value] using hheaderEq) holdLenLe
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolmLen, evmSolm0, initState, storageStore_executionEnv,
            writeSolidityBytesDataWordsFrom_executionEnv,
            clearSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolmLen, evmSolm0, initState,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem bytesStoreLitePushChunkLongNoTailOldLongNoClearRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongNoTailOldLongNoClearRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hnewLong hnoTailMod hflag hvalid hgtOldNew

set_option maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem bytesStoreLitePushChunkLongNoTailOldLongClearRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (_hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div postHeader ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.div oldHeader ⟨2⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let tailFuel : Nat := oldFuel - clearFuel
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen :=
    Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
      (oldLen + ⟨1⟩)
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel tailFuel)
      (chunksDataBase + oldLen) value 0 clearFuel)
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel tailFuel)
      (chunksDataBase + oldLen) value 0 clearFuel).executionEnv.codeOwner
    (chunksDataBase + oldLen) header
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩)
  let τclear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase (chunksDataBase + oldLen))
      ⟨0⟩ clearCount.toNat
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner τclear
        (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32))
      (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [hlenEvm] using hlenMaxWord
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have hmod : len.toNat % 32 = 0 := by
    simpa [len] using hnoTailMod
  have holdGtNat : len.toNat < oldBytesLen.toNat :=
    BytesStoreLiteCore.ugt_eq_one_toNat_lt
      (by simpa [oldBytesLen, oldHeader, len] using hgtOldNew)
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have holdAfter :
      oldBytesLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
          ⟨2⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (congrArg (fun w => UInt256.div w ⟨2⟩) hheaderAfter).symm
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hgtOldNewAfter : UInt256.gt oldBytesLen len = ⟨1⟩ := by
    simpa [oldBytesLen, oldHeader, len] using hgtOldNew
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, σLen, clearCount, τclear, finalEvmMap] using
      bytesStoreLiteX_pushChunkLongNoTailOldLongClearReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart) (oldStoredLen := oldBytesLen)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter holdAfter hvalidAfter
        hgtOldNewAfter hlong hmod
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, evmSolmLen, oldBytesLen, oldFuel, clearFuel, tailFuel, header,
      value, solidityBytesDataWordCount] using
      bytesStoreLitePushChunkLongOldLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSizeLong hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have haddrBound :
      ∀ i, i < len.toNat / 32 → payloadStart.toNat + 32 * i < UInt256.size := by
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
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hclearFuelEq : clearFuel = len.toNat / 32 := by
    dsimp [clearFuel, value]
    rw [hsizeDecoded]
    exact BytesStoreLiteCore.nat_ceil32_eq_div_of_mod_zero hmod
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact BytesStoreLiteCore.nat_ceil32_le_ceil32 (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldBytesLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := oldHeader) rfl
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMaxLen
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
      (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign (x := oldBytesLen) holdLenLt
  have hcountNat : clearCount.toNat = tailFuel := by
    dsimp [clearCount, tailFuel]
    rw [usub_toNat]
    · rw [holdShiftNat, hnewShiftClear]
    · rw [holdShiftNat, hnewShiftClear]
      exact hclearLeOld
  have hcountNatShift :
      (UInt256.sub (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewShiftEq]
    simpa [clearCount] using hcountNat
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    let σSolmLen : AccountMap :=
      sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩)
    let σSolmClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σSolmLen
        (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel) tailFuel
    have hwordCount :
        solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
          clearFuel := by
      simp [value, clearFuel, solidityBytesDataWordCount, hsizeDecoded]
    have hheaderWord :
        solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
          header := by
      simp [value, header]
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner σSolmClear
              (chunksDataBase + oldLen) (BytesStoreLiteCore.setDecodedValueBytes I) 0
              (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size))
            (chunksDataBase + oldLen)
            (solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size) := by
      simp [evmSolm1, evmSolmLen, evmSolm0, oldFuel, clearFuel, tailFuel, value, header,
        σSolmClear, σSolmLen, hwordCount, hheaderWord, initState, storageStore_accountMap,
        storageStore_executionEnv,
        writeSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_accountMap,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv,
        bytesLikeDataBase, solidityBytesDataBaseSlot]
    have hlenAccounts : accountMapEquiv σLen σSolmLen := by
      simpa [σLen, σSolmLen] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ (oldLen + ⟨1⟩) hAccounts
    have hclearAccounts : accountMapEquiv τclear σSolmClear := by
      have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
        (owner := I.codeOwner) (σ := σLen) (τ := σSolmLen)
        (baseSlot := chunksDataBase + oldLen)
        clearFuel (⟨0⟩ : UInt256) tailFuel hlenAccounts
      dsimp [τclear, σSolmClear, clearCount]
      rw [hnewShiftEq, hcountNatShift]
      have hidxZero :
          UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
        simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
      simpa [hidxZero, u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (chunksDataBase + oldLen))] using hshift
    have hwriteAccounts :=
      accountMapEquiv_pushChunkLongNoTailStorageFromLen
        (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
        (σ_evm_len := τclear) (σ_solm_len := σSolmClear)
        hclearAccounts hsrc haddrBound hsizeDecoded hlenAbiLocal hpayloadStartLocal
        hoffMax hmod (by simpa [header, value] using hheaderEq)
    rw [hsolmMap]
    exact hwriteAccounts
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolmLen, evmSolm0, initState, storageStore_executionEnv,
            writeSolidityBytesDataWordsFrom_executionEnv,
            clearSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolmLen, evmSolm0, initState,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem bytesStoreLitePushChunkLongNoTailOldLongClearRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongNoTailOldLongClearRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hnewLong hnoTailMod hflag hvalid hgtOldNew

set_option maxHeartbeats 3000000 in
set_option maxHeartbeats 300000 in
theorem bytesStoreLitePushChunkLongTailShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (_hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.land (UInt256.div oldHeader ⟨2⟩) ⟨127⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
        (oldLen + ⟨1⟩))
      (chunksDataBase + oldLen) value 0 (solidityBytesDataWordCount value.size))
    evmSolm0.executionEnv.codeOwner (chunksDataBase + oldLen) header
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
          (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase (chunksDataBase + oldLen))
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [hlenEvm] using hlenMaxWord
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have htailModLen : len.toNat % 32 ≠ 0 := by
    simpa [len] using htailMod
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ = ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
                  (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                    (fun acc => acc.storage.findD
                      (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreLiteX_pushChunkLongTailReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter hvalidAfter hlong htailModLen
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, oldBytesLen, header, value] using
      bytesStoreLitePushChunkLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSizeLong hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have haddrBound :
      ∀ i, i < len.toNat / 32 → payloadStart.toNat + 32 * i < UInt256.size := by
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
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    have hbridge := accountMapEquiv_pushChunkLongTailStorage
      (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
      (σ_evm := σ_evm) (σ_solm := σ_solm)
      hAccounts hsrc haddrBound htailAddr hsizeDecoded hlenAbiLocal hpayloadStartLocal
      hoffMax hlong htailModLen (by simpa [header, value] using hheaderEq)
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner
              (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
              (chunksDataBase + oldLen) value 0
              (solidityBytesDataWordCount value.size))
            (chunksDataBase + oldLen) header := by
      simp [evmSolm1, evmSolm0, value, header, initState, storageStore_accountMap,
        storageStore_executionEnv, writeSolidityBytesDataWordsFrom_accountMap]
    rw [hsolmMap]
    simpa [finalEvmMap, value, header] using hbridge
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv,
            writeSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 3000000 in
set_option maxHeartbeats 300000 in
theorem bytesStoreLitePushChunkLongTailShortPackedRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongTailShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hnewLong htailMod hflag hvalid

set_option maxHeartbeats 300000 in
set_option maxHeartbeats 3000000 in
theorem bytesStoreLitePushChunkLongTailOldLongClearRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (_hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div postHeader ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.div oldHeader ⟨2⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let tailFuel : Nat := oldFuel - clearFuel
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen :=
    Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
      (oldLen + ⟨1⟩)
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel tailFuel)
      (chunksDataBase + oldLen) value 0 clearFuel)
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel tailFuel)
      (chunksDataBase + oldLen) value 0 clearFuel).executionEnv.codeOwner
    (chunksDataBase + oldLen) header
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩)
  let τclear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase (chunksDataBase + oldLen))
      ⟨0⟩ clearCount.toNat
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner τclear
          (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase (chunksDataBase + oldLen))
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [hlenEvm] using hlenMaxWord
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have htailModLen : len.toNat % 32 ≠ 0 := by
    simpa [len] using htailMod
  have holdGtNat : len.toNat < oldBytesLen.toNat :=
    BytesStoreLiteCore.ugt_eq_one_toNat_lt
      (by simpa [oldBytesLen, oldHeader, len] using hgtOldNew)
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have holdAfter :
      oldBytesLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
          ⟨2⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (congrArg (fun w => UInt256.div w ⟨2⟩) hheaderAfter).symm
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hgtOldNewAfter : UInt256.gt oldBytesLen len = ⟨1⟩ := by
    simpa [oldBytesLen, oldHeader, len] using hgtOldNew
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, σLen, clearCount, τclear, finalEvmMap] using
      bytesStoreLiteX_pushChunkLongTailOldLongClearReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart) (oldStoredLen := oldBytesLen)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter holdAfter hvalidAfter
        hgtOldNewAfter hlong htailModLen
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, evmSolmLen, oldBytesLen, oldFuel, clearFuel, tailFuel, header,
      value, solidityBytesDataWordCount] using
      bytesStoreLitePushChunkLongOldLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSizeLong hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have haddrBound :
      ∀ i, i < len.toNat / 32 → payloadStart.toNat + 32 * i < UInt256.size := by
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
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact BytesStoreLiteCore.nat_ceil32_le_ceil32 (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldBytesLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := oldHeader) rfl
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMaxLen
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
      (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign (x := oldBytesLen) holdLenLt
  have hcountNat : clearCount.toNat = tailFuel := by
    dsimp [clearCount, tailFuel]
    rw [usub_toNat]
    · rw [holdShiftNat, hnewShiftClear]
    · rw [holdShiftNat, hnewShiftClear]
      exact hclearLeOld
  have hcountNatShift :
      (UInt256.sub (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewShiftEq]
    simpa [clearCount] using hcountNat
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    let σSolmLen : AccountMap :=
      sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩)
    let σSolmClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σSolmLen
        (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel) tailFuel
    have hwordCount :
        solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
          clearFuel := by
      simp [value, clearFuel, solidityBytesDataWordCount, hsizeDecoded]
    have hheaderWord :
        solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
          header := by
      simp [value, header]
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner σSolmClear
              (chunksDataBase + oldLen) (BytesStoreLiteCore.setDecodedValueBytes I) 0
              (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size))
            (chunksDataBase + oldLen)
            (solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size) := by
      simp [evmSolm1, evmSolmLen, evmSolm0, oldFuel, clearFuel, tailFuel, value, header,
        σSolmClear, σSolmLen, hwordCount, hheaderWord, initState, storageStore_accountMap,
        storageStore_executionEnv,
        writeSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_accountMap,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv,
        bytesLikeDataBase, solidityBytesDataBaseSlot]
    have hlenAccounts : accountMapEquiv σLen σSolmLen := by
      simpa [σLen, σSolmLen] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ (oldLen + ⟨1⟩) hAccounts
    have hclearAccounts : accountMapEquiv τclear σSolmClear := by
      have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
        (owner := I.codeOwner) (σ := σLen) (τ := σSolmLen)
        (baseSlot := chunksDataBase + oldLen)
        clearFuel (⟨0⟩ : UInt256) tailFuel hlenAccounts
      dsimp [τclear, σSolmClear, clearCount]
      rw [hnewShiftEq, hcountNatShift]
      have hidxZero :
          UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
        simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
      simpa [hidxZero, u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (chunksDataBase + oldLen))] using hshift
    have hwriteAccounts :=
      accountMapEquiv_pushChunkLongTailStorageFromLen
        (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
        (σ_evm_len := τclear) (σ_solm_len := σSolmClear)
        hclearAccounts hsrc haddrBound htailAddr hsizeDecoded hlenAbiLocal
        hpayloadStartLocal hoffMax hlong htailModLen
        (by simpa [header, value] using hheaderEq)
    rw [hsolmMap]
    exact hwriteAccounts
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolmLen, evmSolm0, initState, storageStore_executionEnv,
            writeSolidityBytesDataWordsFrom_executionEnv,
            clearSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolmLen, evmSolm0, initState,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 300000 in
set_option maxHeartbeats 3000000 in
theorem bytesStoreLitePushChunkLongTailOldLongClearRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongTailOldLongClearRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hnewLong htailMod hflag hvalid hgtOldNew

set_option maxHeartbeats 3000000 in
set_option maxHeartbeats 800000 in
theorem bytesStoreLitePushChunkLongTailOldLongNoClearRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (_hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div postHeader ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.div oldHeader ⟨2⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let header : UInt256 := solidityBytesHeaderWord value.size
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen :=
    Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
      (oldLen + ⟨1⟩)
  let evmSolm1 := Solm.EVM.storageStore
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel (oldFuel - clearFuel))
      (chunksDataBase + oldLen) value 0 clearFuel)
    (writeSolidityBytesDataWordsFrom
      (clearSolidityBytesDataWordsFrom evmSolmLen
        (chunksDataBase + oldLen) clearFuel (oldFuel - clearFuel))
      (chunksDataBase + oldLen) value 0 clearFuel).executionEnv.codeOwner
    (chunksDataBase + oldLen) header
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
          (bytesLikeDataBase (chunksDataBase + oldLen)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase (chunksDataBase + oldLen))
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      (chunksDataBase + oldLen) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [hlenEvm] using hlenMaxWord
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hlenMaxLen : len.toNat ≤ ABI.solcMaxU64 := by
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hlong : ¬ len.toNat < 32 := by
    simpa [len] using hnewLong
  have hvalueSizeLong : ¬ value.size < 32 := by
    rw [hsizeDecoded]
    exact hlong
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMaxLen
  have htailModLen : len.toNat % 32 ≠ 0 := by
    simpa [len] using htailMod
  have holdLenLe : oldBytesLen.toNat ≤ len.toNat :=
    BytesStoreLiteCore.ugt_eq_zero_toNat_le
      (by simpa [oldBytesLen, oldHeader, len] using hgtOldNew)
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have holdAfter :
      oldBytesLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
          ⟨2⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (congrArg (fun w => UInt256.div w ⟨2⟩) hheaderAfter).symm
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hgtOldNewAfter : UInt256.gt oldBytesLen len = ⟨0⟩ := by
    simpa [oldBytesLen, oldHeader, len] using hgtOldNew
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, finalEvmMap] using
      bytesStoreLiteX_pushChunkLongTailOldLongNoClearReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart) (oldStoredLen := oldBytesLen)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter holdAfter hvalidAfter
        hgtOldNewAfter hlong htailModLen
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, evmSolmLen, oldBytesLen, oldFuel, clearFuel, header, value,
      solidityBytesDataWordCount] using
      bytesStoreLitePushChunkLongOldLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSizeLong hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have haddrBound :
      ∀ i, i < len.toNat / 32 → payloadStart.toNat + 32 * i < UInt256.size := by
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
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner
            (solidityDataWordsForwardFrom I.codeOwner
              (clearDataWordsForwardFrom I.codeOwner
                (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
                (bytesLikeDataBase (chunksDataBase + oldLen)) (UInt256.ofNat clearFuel)
                (oldFuel - clearFuel))
              (chunksDataBase + oldLen) value 0 clearFuel)
            (chunksDataBase + oldLen) header := by
      simp [evmSolm1, evmSolmLen, evmSolm0, oldFuel, clearFuel, value, header,
        initState, storageStore_accountMap, storageStore_executionEnv,
        writeSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_accountMap,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv,
        bytesLikeDataBase, solidityBytesDataBaseSlot]
    rw [hsolmMap]
    simpa [finalEvmMap, value, header, oldFuel, clearFuel] using
      accountMapEquiv_pushChunkLongTailStorageOldLongNoClear
        (I := I) (len := len) (payloadStart := payloadStart) (oldLen := oldLen)
        (oldBytesLen := oldBytesLen) (σ_evm := σ_evm) (σ_solm := σ_solm)
        hAccounts hsrc haddrBound htailAddr hsizeDecoded hlenAbiLocal hpayloadStartLocal
        hoffMax hlong htailModLen (by simpa [header, value] using hheaderEq) holdLenLe
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolmLen, evmSolm0, initState, storageStore_executionEnv,
            writeSolidityBytesDataWordsFrom_executionEnv,
            clearSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolmLen, evmSolm0, initState,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 3000000 in
set_option maxHeartbeats 800000 in
theorem bytesStoreLitePushChunkLongTailOldLongNoClearRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongTailOldLongNoClearRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hnewLong htailMod hflag hvalid hgtOldNew

set_option maxHeartbeats 800000 in
theorem bytesStoreLitePushChunkLongOldLongNoClearRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div postHeader ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
    intro hzero
    exact hnewLong (by omega)
  by_cases hmod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0
  · exact bytesStoreLitePushChunkLongNoTailOldLongNoClearRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnz hnewLong hmod hflag hvalid hgtOldNew
  · exact bytesStoreLitePushChunkLongTailOldLongNoClearRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnz hnewLong hmod hflag hvalid hgtOldNew

set_option maxHeartbeats 800000 in
theorem bytesStoreLitePushChunkLongOldLongNoClearRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongOldLongNoClearRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnewLong hflag hvalid hgtOldNew

theorem bytesStoreLitePushChunkLongOldLongClearRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div postHeader ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
    intro hzero
    exact hnewLong (by omega)
  by_cases hmod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0
  · exact bytesStoreLitePushChunkLongNoTailOldLongClearRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnz hnewLong hmod hflag hvalid hgtOldNew
  · exact bytesStoreLitePushChunkLongTailOldLongClearRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnz hnewLong hmod hflag hvalid hgtOldNew

theorem bytesStoreLitePushChunkLongOldLongClearRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongOldLongClearRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnewLong hflag hvalid hgtOldNew

theorem bytesStoreLitePushChunkLongOldLongRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hgtOldNew :
      UInt256.gt (UInt256.div postHeader ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩
  · exact bytesStoreLitePushChunkLongOldLongClearRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnewLong hflag hvalid hgtOldNew
  · have hgtOldNewZero :
        UInt256.gt (UInt256.div postHeader ⟨2⟩)
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩ := by
      exact ugt_eq_zero_of_ne_one_local hgtOldNew
    exact bytesStoreLitePushChunkLongOldLongNoClearRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnewLong hflag hvalid hgtOldNewZero

theorem bytesStoreLitePushChunkLongOldLongRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongOldLongRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnewLong hflag hvalid

set_option maxHeartbeats 900000 in
theorem bytesStoreLitePushChunkShortNonemptyOldLongRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.div oldHeader ⟨2⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let storedWord : UInt256 := bytesStoreLiteOptimizedShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen :=
    Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
      (oldLen + ⟨1⟩)
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolmLen (chunksDataBase + oldLen) 0 oldFuel)
    (clearSolidityBytesDataWordsFrom evmSolmLen
      (chunksDataBase + oldLen) 0 oldFuel).executionEnv.codeOwner
    (chunksDataBase + oldLen) (solidityShortBytesWord value)
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩)
  let τclear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + oldLen)) ⟨0⟩
      clearCount.toNat
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner τclear (chunksDataBase + oldLen) storedWord
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_pushChunk (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [hlenEvm] using hlenMaxWord
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hlenAbiLocal :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := rfl
  have hpayloadStartLocal :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) := rfl
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value, len]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
  have hvalueSizeShort : value.size < 32 := by
    rw [hsizeDecoded]
    exact hshort
  have hshortLen : len.toNat < 32 := by
    simpa [len] using hshort
  have hnzLen : len.toNat ≠ 0 := by
    simpa [len] using hnz
  have hstoredEq : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, len, payloadStart] using
      bytesStoreLiteOptimizedShortStoredWord_abbrev_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbiLocal hpayloadStartLocal hoffMax hnzLen hshortLen hsrc hpayloadList
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have holdAfter :
      oldBytesLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
          ⟨2⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (congrArg (fun w => UInt256.div w ⟨2⟩) hheaderAfter).symm
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, σLen, clearCount, τclear, finalEvmMap, storedWord,
      bytesStoreLiteOptimizedShortStoredWord, len, payloadStart] using
      bytesStoreLiteX_pushChunkShortOldLongReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart) (oldStoredLen := oldBytesLen)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter holdAfter hvalidAfter
        hnzLen hshortLen
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes value) }
        evmSolm0 chunksRef (some (.bytes value)) = .ok evmSolm1 := by
    simpa [evmSolm1, evmSolmLen, oldBytesLen, oldFuel, value] using
      bytesStoreLitePushChunkShortOldLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen value hvalueSizeShort hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes value)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes value) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have holdLenLt : oldBytesLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := oldHeader) (len := oldBytesLen) rfl
  have holdShiftNat :
      (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign
      (x := oldBytesLen) holdLenLt
  have hcountNat : clearCount.toNat = oldFuel := by
    dsimp [clearCount]
    rw [BytesStoreLiteCore.uint256_sub_zero_right]
    exact holdShiftNat
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    let σSolmLen : AccountMap := sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩)
    let σSolmClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σSolmLen
        (bytesLikeDataBase (chunksDataBase + oldLen)) ⟨0⟩ oldFuel
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner σSolmClear (chunksDataBase + oldLen)
            (solidityShortBytesWord value) := by
      simp [evmSolm1, evmSolmLen, evmSolm0, oldFuel, value, σSolmClear, σSolmLen,
        initState, storageStore_accountMap, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_executionEnv,
        bytesLikeDataBase, solidityBytesDataBaseSlot,
        show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide]
    have hlenAccounts : accountMapEquiv σLen σSolmLen := by
      simpa [σLen, σSolmLen] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ (oldLen + ⟨1⟩) hAccounts
    have hclearAccounts : accountMapEquiv τclear σSolmClear := by
      have hbaseZero :
          (⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + oldLen) =
            bytesLikeDataBase (chunksDataBase + oldLen) :=
        u256_zero_add (bytesLikeDataBase (chunksDataBase + oldLen))
      have hclear := accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
        (bytesLikeDataBase (chunksDataBase + oldLen)) (⟨0⟩ : UInt256)
        oldFuel hlenAccounts
      simpa [τclear, σSolmClear, clearCount, hbaseZero, hcountNat] using hclear
    rw [hsolmMap]
    simpa [finalEvmMap, hstoredEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (chunksDataBase + oldLen)
        (solidityShortBytesWord value) hclearAccounts
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolmLen, evmSolm0, initState, storageStore_executionEnv,
            clearSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolmLen, evmSolm0, initState,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 900000 in
theorem bytesStoreLitePushChunkShortNonemptyOldLongRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkShortNonemptyOldLongRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hshort hflag hvalid

set_option maxHeartbeats 900000 in
set_option maxHeartbeats 900000 in
theorem bytesStoreLitePushChunkEmptyOldLongRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := postHeader
  let oldBytesLen : UInt256 := UInt256.div oldHeader ⟨2⟩
  let len : UInt256 := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldFuel : Nat := (oldBytesLen.toNat + 31) / 32
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolmLen :=
    Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩
      (oldLen + ⟨1⟩)
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolmLen (chunksDataBase + oldLen) 0 oldFuel)
    (clearSolidityBytesDataWordsFrom evmSolmLen
      (chunksDataBase + oldLen) 0 oldFuel).executionEnv.codeOwner
    (chunksDataBase + oldLen) ⟨0⟩
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  let σLen : AccountMap := sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩)
  let τclear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σLen
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + oldLen)) ⟨0⟩
      clearCount.toNat
  let finalEvmMap : AccountMap :=
    sstoreAccountMap I.codeOwner τclear (chunksDataBase + oldLen) ⟨0⟩
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  have hreach := bytesStoreLiteReachPushChunk (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := bytesStoreLiteDecode_pushChunk_empty (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    rw [hlenZero]
    apply ugt_zero
    rw [u256_add_assoc]
    rw [show ((⟨0⟩ : UInt256) + ⟨32⟩) = ⟨32⟩ by native_decide]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    rw [ulit_toNat' I.calldata.size hsize]
    exact hlenWord
  have hdecodedReach := bytesStoreLiteX_pushChunkDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hreach hsz36 hhi hsize hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = len := by
    simpa [len] using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  have hlenZeroLen : len = ⟨0⟩ := by
    simpa [len] using hlenZeroAbi
  have hlenMaxWordLen :
      UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenZeroLen]
    native_decide
  have hdecodedReachLen :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1559⟩
        [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [len, payloadStart, hlenEvm] using hdecodedReach
  have hflagAfter :
      UInt256.land
        ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader] using
      (by
        rw [hheaderAfter]
        exact hflag)
  have holdAfter :
      oldBytesLen =
        UInt256.div
          ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
            (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
          ⟨2⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (congrArg (fun w => UInt256.div w ⟨2⟩) hheaderAfter).symm
  have hvalidAfter :
      UInt256.sub
          (UInt256.land
            ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
              (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
                (fun acc => acc.storage.findD
                  (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldBytesLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [oldLen, oldHeader, oldBytesLen] using
      (by
        rw [hheaderAfter]
        exact hvalid)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, finalEvmMap)
        (UInt256.toByteArray
          (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩))) := by
    simpa [oldLen, σLen, clearCount, τclear, finalEvmMap] using
      bytesStoreLiteX_pushChunkEmptyOldLongReturnsSplit
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := len)
        (payloadStart := payloadStart) (oldStoredLen := oldBytesLen)
        hperm hdecodedReachLen hlenMaxWordLen hflagAfter holdAfter hvalidAfter
        hlenZeroLen
  have hlenEq :
      bytesStoreLiteChunksLengthWord σ_solm I = oldLen := by
    simpa [oldLen] using
      (bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv (I := I) hAccounts).symm
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hpush :
      pushArray? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract,
          locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
        evmSolm0 chunksRef (some (.bytes ByteArray.empty)) = .ok evmSolm1 := by
    simpa [evmSolm1, evmSolmLen, oldBytesLen, oldFuel, hshortEmpty] using
      bytesStoreLitePushChunkShortOldLongPushArray_of_post_header (evm := evmSolm0)
        oldLen oldHeader oldBytesLen ByteArray.empty (by decide) hloadLen
        (by simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using hloadElemLen)
        (by simpa [oldHeader] using hflag)
        (by simp [oldBytesLen])
        (by simpa [oldHeader, oldBytesLen] using hvalid)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        ((∅ : Store).insert "value" (.bytes ByteArray.empty)) pushChunkTransition.body
        (.returned
          { contract := bytesStoreLiteContract,
            locals := (∅ : Store).insert "value" (.bytes ByteArray.empty) }
          evmSolm1
          (some (.int (Int.ofNat
            (Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩).toNat)))) := by
    exact bytesStoreLitePushChunkEmptyBodyReturns (evm := evmSolm0) (evm' := evmSolm1)
      (by simp [evmSolm0, initState]; exact hwv) hpush
  have holdLenLt : oldBytesLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := oldHeader) (len := oldBytesLen) rfl
  have holdShiftNat :
      (UInt256.shiftRight (oldBytesLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign
      (x := oldBytesLen) holdLenLt
  have hcountNat : clearCount.toNat = oldFuel := by
    dsimp [clearCount]
    rw [BytesStoreLiteCore.uint256_sub_zero_right]
    exact holdShiftNat
  have hpostAccounts : accountMapEquiv finalEvmMap evmSolm1.accountMap := by
    let σSolmLen : AccountMap := sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩)
    let σSolmClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σSolmLen
        (bytesLikeDataBase (chunksDataBase + oldLen)) ⟨0⟩ oldFuel
    have hsolmMap :
        evmSolm1.accountMap =
          sstoreAccountMap I.codeOwner σSolmClear (chunksDataBase + oldLen) ⟨0⟩ := by
      simp [evmSolm1, evmSolmLen, evmSolm0, oldFuel, σSolmClear, σSolmLen,
        initState, storageStore_accountMap, storageStore_executionEnv,
        clearSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_executionEnv,
        bytesLikeDataBase, solidityBytesDataBaseSlot,
        show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide]
    have hlenAccounts : accountMapEquiv σLen σSolmLen := by
      simpa [σLen, σSolmLen] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ (oldLen + ⟨1⟩) hAccounts
    have hclearAccounts : accountMapEquiv τclear σSolmClear := by
      have hbaseZero :
          (⟨0⟩ : UInt256) + bytesLikeDataBase (chunksDataBase + oldLen) =
            bytesLikeDataBase (chunksDataBase + oldLen) :=
        u256_zero_add (bytesLikeDataBase (chunksDataBase + oldLen))
      have hclear := accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
        (bytesLikeDataBase (chunksDataBase + oldLen)) (⟨0⟩ : UInt256)
        oldFuel hlenAccounts
      simpa [τclear, σSolmClear, clearCount, hbaseZero, hcountNat] using hclear
    rw [hsolmMap]
    simpa [finalEvmMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (chunksDataBase + oldLen)
        (⟨0⟩ : UInt256) hclearAccounts
  have hretWordEq :
      (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) =
      Solm.EVM.storageLoad evmSolm1 evmSolm1.executionEnv.codeOwner ⟨1⟩ := by
    simpa [bytesStoreLiteChunksLengthWord] using
      bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1) (σ := finalEvmMap) (I := I)
        (by
          simp [evmSolm1, evmSolmLen, evmSolm0, initState, storageStore_executionEnv,
            clearSolidityBytesDataWordsFrom_executionEnv])
        hpostAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolmLen, evmSolm0, initState,
      clearSolidityBytesDataWordsFrom_createdAccounts, storageStore_createdAccounts])
    hpostAccounts
    (by
      simpa [hretWordEq] using
        (returnEquiv_of_encode
          (uint256ReturnEncoding
            (finalEvmMap.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)))))

set_option maxHeartbeats 900000 in
set_option maxHeartbeats 900000 in
theorem bytesStoreLitePushChunkEmptyOldLongRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkEmptyOldLongRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenZero hflag hvalid

set_option maxHeartbeats 900000 in
theorem bytesStoreLitePushChunkLongShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let lenNat :=
    (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
  have hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
    intro hzero
    exact hnewLong (by omega)
  by_cases hmod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0
  · exact bytesStoreLitePushChunkLongNoTailShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnz hnewLong hmod hflag hvalid
  · exact bytesStoreLitePushChunkLongTailShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnz hnewLong hmod hflag hvalid

set_option maxHeartbeats 900000 in
theorem bytesStoreLitePushChunkLongShortPackedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkLongShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnewLong hflag hvalid

theorem bytesStoreLitePushChunkNonemptyShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32
  · exact bytesStoreLitePushChunkShortNonemptyShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnz hshort hflag hvalid
  · exact bytesStoreLitePushChunkLongShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hshort hflag hvalid

theorem bytesStoreLitePushChunkNonemptyShortPackedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkNonemptyShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hnz hflag hvalid

theorem bytesStoreLitePushChunkValidShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hzero :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat = 0
  · have hwordZero :
        calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
      simpa [hzero] using
        (u256_ofNat_toNat
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))).symm
    have hlenZero :
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩ := by
      rw [BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax]
      exact hwordZero
    exact bytesStoreLitePushChunkEmptyShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenZero hflag hvalid
  · exact bytesStoreLitePushChunkNonemptyShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hzero hflag hvalid

theorem bytesStoreLitePushChunkValidShortPackedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkValidShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    hflag hvalid

theorem bytesStoreLitePushChunkValidZeroRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (_hzero :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩)
    (hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact bytesStoreLitePushChunkValidShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts postHeader
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hflag hvalid

theorem bytesStoreLitePushChunkValidZeroRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hzero :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  have hflag :
      UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
    unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
    rw [hzero]
    native_decide
  have hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
    rw [hzero]
    native_decide
  exact bytesStoreLitePushChunkValidZeroRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hzero
    hflag hvalid

theorem bytesStoreLitePushChunkValidZeroOrShortPackedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      ((σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∧
        (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land postHeader ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div postHeader ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
        UInt256.sub (UInt256.land postHeader ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div postHeader ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  rcases hcase with ⟨hzero, ⟨hflag, hvalid⟩⟩ | ⟨hflag, hvalid⟩
  ·
    exact bytesStoreLitePushChunkValidZeroRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hzero
      hflag hvalid
  · exact bytesStoreLitePushChunkValidShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hflag hvalid

theorem bytesStoreLitePushChunkValidZeroOrShortPackedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD
          (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∨
      (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
        UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  have hcasePost :
      ((σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∧
          (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
            UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt
                (UInt256.land
                  (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                  ⟨127⟩)
                ⟨32⟩) ≠ ⟨0⟩)) ∨
        (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩) := by
    rcases hcase with hzero | hshort
    · left
      have hflag :
          UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
        unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
        rw [hzero]
        native_decide
      have hvalid :
          UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩ := by
        unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
        rw [hzero]
        native_decide
      exact ⟨hzero, ⟨hflag, hvalid⟩⟩
    · exact Or.inr hshort
  exact bytesStoreLitePushChunkValidZeroOrShortPackedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hcasePost

theorem bytesStoreLitePushChunkValidZeroOrShortPackedOrOldLongNoClearRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      (((σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∧
        (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land postHeader ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div postHeader ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
        (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land postHeader ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div postHeader ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      (UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩ ∧
        UInt256.sub (UInt256.land postHeader ⟨1⟩)
          (UInt256.lt (UInt256.div postHeader ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩ ∧
        UInt256.gt (UInt256.div postHeader ⟨2⟩)
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hvalidPacked | ⟨hflag, hvalid, hgtOldNew⟩
  · exact bytesStoreLitePushChunkValidZeroOrShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hvalidPacked
  · have hgt31 :
        UInt256.lt ⟨31⟩
          (UInt256.div postHeader ⟨2⟩) ≠ ⟨0⟩ :=
      BytesStoreLiteCore.clearCurrentLongValid_gt31
        (header := postHeader)
        (len := UInt256.div postHeader ⟨2⟩)
        hflag hvalid
    have holdGt31 :
        31 < (UInt256.div postHeader ⟨2⟩).toNat := by
      simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
        ult_ne_zero_toNat_lt hgt31
    have holdLeNew :
        (UInt256.div postHeader ⟨2⟩).toNat ≤
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat :=
      BytesStoreLiteCore.ugt_eq_zero_toNat_le hgtOldNew
    have hnewLong :
        ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32 := by
      intro hshort
      omega
    exact bytesStoreLitePushChunkLongOldLongNoClearRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
      hnewLong hflag hvalid hgtOldNew

theorem bytesStoreLitePushChunkValidZeroOrShortPackedOrOldLongNoClearRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      ((σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∨
        (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ ∧
        UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩ ∧
        UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  have hcasePost :
      (((σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∧
          (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
            UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt
                (UInt256.land
                  (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                  ⟨127⟩)
                ⟨32⟩) ≠ ⟨0⟩)) ∨
        (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ ∧
        UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩ ∧
        UInt256.gt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) := by
    rcases hcase with hvalidPacked | holdLong
    · left
      rcases hvalidPacked with hzero | hshort
      · left
        have hflag :
            UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
          unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
          rw [hzero]
          native_decide
        have hvalid :
            UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt
                (UInt256.land
                  (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                  ⟨127⟩)
                ⟨32⟩) ≠ ⟨0⟩ := by
          unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
          rw [hzero]
          native_decide
        exact ⟨hzero, ⟨hflag, hvalid⟩⟩
      · exact Or.inr hshort
    · exact Or.inr holdLong
  exact bytesStoreLitePushChunkValidZeroOrShortPackedOrOldLongNoClearRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hcasePost

theorem bytesStoreLitePushChunkValidZeroOrShortPackedOrOldLongRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      (((σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∧
        (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land postHeader ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div postHeader ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
        (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land postHeader ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div postHeader ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      (UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩ ∧
        UInt256.sub (UInt256.land postHeader ⟨1⟩)
          (UInt256.lt (UInt256.div postHeader ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hvalidPacked | ⟨hflag, hvalid⟩
  · have hvalidPackedPost :
        ((σ_evm.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∧
            (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
              UInt256.sub (UInt256.land postHeader ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div postHeader ⟨2⟩)
                    ⟨127⟩)
                  ⟨32⟩) ≠ ⟨0⟩)) ∨
          (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
            UInt256.sub (UInt256.land postHeader ⟨1⟩)
              (UInt256.lt
                (UInt256.land
                  (UInt256.div postHeader ⟨2⟩)
                  ⟨127⟩)
                ⟨32⟩) ≠ ⟨0⟩) := by
      rcases hvalidPacked with hzero | hshort
      · exact Or.inl hzero
      · exact Or.inr hshort
    exact bytesStoreLitePushChunkValidZeroOrShortPackedRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader
      hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hvalidPackedPost
  · by_cases hzero :
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat = 0
    · have hwordZero :
          calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
        simpa [hzero] using
          (u256_ofNat_toNat
            (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))).symm
      have hlenZero :
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩ := by
        rw [BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax]
        exact hwordZero
      exact bytesStoreLitePushChunkEmptyOldLongRuntime_of_post_header
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts postHeader
        hheaderAfter hloadElemLen
        hsz36 hhi hoffMax hlenWord hsizeSign hlenZero hflag hvalid
    · by_cases hshort :
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32
      · exact bytesStoreLitePushChunkShortNonemptyOldLongRuntime_of_post_header
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts postHeader
          hheaderAfter hloadElemLen
          hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
          hzero hshort hflag hvalid
      · exact bytesStoreLitePushChunkLongOldLongRuntime_of_post_header
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts postHeader
          hheaderAfter hloadElemLen
          hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
          hshort hflag hvalid

theorem bytesStoreLitePushChunkValidZeroOrShortPackedOrOldLongRuntime_of_ne
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      ((σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∨
        (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
          UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ ∧
        UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkValidZeroOrShortPackedOrOldLongRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    (by
      rcases hcase with hvalidPacked | holdLong
      · left
        rcases hvalidPacked with hzero | hshort
        · left
          have hflag :
              UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
            unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
            rw [hzero]
            native_decide
          have hvalid :
              UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩)
                  ⟨32⟩) ≠ ⟨0⟩ := by
            unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
            rw [hzero]
            native_decide
          exact ⟨hzero, ⟨hflag, hvalid⟩⟩
        · exact Or.inr hshort
      · exact Or.inr holdLong)

theorem bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      ((((σ_evm.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD
                (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∧
          (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
            UInt256.sub (UInt256.land postHeader ⟨1⟩)
              (UInt256.lt
                (UInt256.land
                  (UInt256.div postHeader ⟨2⟩)
                  ⟨127⟩)
                ⟨32⟩) ≠ ⟨0⟩)) ∨
          (UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
            UInt256.sub (UInt256.land postHeader ⟨1⟩)
              (UInt256.lt
                (UInt256.land
                  (UInt256.div postHeader ⟨2⟩)
                  ⟨127⟩)
                ⟨32⟩) ≠ ⟨0⟩)) ∨
        (UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩ ∧
          UInt256.sub (UInt256.land postHeader ⟨1⟩)
            (UInt256.lt (UInt256.div postHeader ⟨2⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      ((UInt256.land postHeader ⟨1⟩ = ⟨0⟩ ∧
        UInt256.sub (UInt256.land postHeader ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div postHeader ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩) ∨
       (UInt256.land postHeader ⟨1⟩ ≠ ⟨0⟩ ∧
        UInt256.sub (UInt256.land postHeader ⟨1⟩)
          (UInt256.lt (UInt256.div postHeader ⟨2⟩)
            ⟨32⟩) = ⟨0⟩))) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  rcases hcase with hvalidCase | hmalformedCase
  · exact bytesStoreLitePushChunkValidZeroOrShortPackedOrOldLongRuntime_of_post_header
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
      hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hvalidCase
  · rcases hmalformedCase with ⟨hflag, hbad⟩ | ⟨hflag, hbad⟩
    · exact bytesStoreLitePushChunkShortMalformedRuntime_of_post_header
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hflag hbad
    · exact bytesStoreLitePushChunkLongMalformedRuntime_of_post_header
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord hflag hbad

theorem bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hcase :
      (((σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD
              (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩ ∨
          (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
            UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt
                (UInt256.land
                  (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                  ⟨127⟩)
                ⟨32⟩) ≠ ⟨0⟩)) ∨
        (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ ∧
          UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
              ⟨32⟩) ≠ ⟨0⟩)) ∨
      ((UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ ∧
        UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) = ⟨0⟩) ∨
       (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ ∧
        UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) = ⟨0⟩))) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
    (by
      rcases hcase with hvalidCase | hmalformedCase
      · left
        rcases hvalidCase with hvalidPacked | holdLong
        · left
          rcases hvalidPacked with hzero | hshort
          · left
            have hflag :
                UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
              unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
              rw [hzero]
              native_decide
            have hvalid :
                UInt256.sub (UInt256.land (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨1⟩)
                  (UInt256.lt
                    (UInt256.land
                      (UInt256.div (bytesStoreLitePushChunkHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩)
                    ⟨32⟩) ≠ ⟨0⟩ := by
              unfold bytesStoreLitePushChunkHeaderWord bytesStoreLitePushChunkSlot
              rw [hzero]
              native_decide
            exact ⟨hzero, ⟨hflag, hvalid⟩⟩
          · exact Or.inr hshort
        · exact Or.inr holdLong
      · exact Or.inr hmalformedCase)

theorem bytesStoreLitePushChunkDecodedRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag : UInt256.land postHeader ⟨1⟩ = ⟨0⟩
  · by_cases hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div postHeader ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · by_cases hzero :
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) = ⟨0⟩
      · exact bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_post_header
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
          hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
          (Or.inl (Or.inl (Or.inl ⟨hzero, ⟨hflag, hvalid⟩⟩)))
      · exact bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_post_header
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
          hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
          (Or.inl (Or.inl (Or.inr ⟨hflag, hvalid⟩)))
    · exact bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_post_header
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
        (Or.inr (Or.inl ⟨hflag, not_ne_iff.mp hvalid⟩))
  · by_cases hvalid :
      UInt256.sub (UInt256.land postHeader ⟨1⟩)
        (UInt256.lt (UInt256.div postHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_post_header
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
        (Or.inl (Or.inr ⟨hflag, hvalid⟩))
    · exact bytesStoreLitePushChunkDecodedProvedHeaderRuntime_of_post_header
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
        hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord
        (Or.inr (Or.inr ⟨hflag, not_ne_iff.mp hvalid⟩))

theorem bytesStoreLitePushChunkDecodedRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256))
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkDecodedRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen
    hsz36 hhi hoffMax hlenWord hsizeSign hlenMax hpayloadList hpayloadWord

theorem bytesStoreLitePushChunkPayloadWordFull_of_core {cd : ByteArray} {flag : UInt256}
    (hcore :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (cd.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat cd.size) = flag) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) +
        uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) +
        ⟨32⟩))
      (UInt256.ofNat cd.size) = flag := by
  let len : UInt256 :=
    uInt256OfByteArray
      (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)
  let base : UInt256 := (⟨4⟩ : UInt256) + calldataWord cd 4
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

theorem bytesStoreLiteX_pushChunkDecodeTotalHigh {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsz := bytesStoreLitePushChunkSelector_size hsel
  obtain ⟨_, _, rd457⟩ := bytesStoreLiteReachPushChunk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffLe : (calldataWord I.calldata 4).toNat ≤ ABI.solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  have hstartPlus31Small :
      4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 + 35 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply BytesStoreLiteCore.slt_zero_of_left_low_right_high
    · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
      exact hstartPlus31Small
    · rw [ulit_toNat' I.calldata.size hsize]
      omega
  have rd1883 := evm_run rd457 with [
    jumpdest, push2 ⟨263⟩, push2 ⟨471⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1883⟩, jump (by native_decide)]
  have rd1903 := evm_run rd1883 with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨1900⟩,
    jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup3, calldataload]
  have rd1912 := RD.pushConst rd1903 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1922 := evm_run rd1912 with [
    dup2, gt, iszero, push2 ⟨1922⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd1922 with [
    jumpdest, push2 ⟨1934⟩, dup6, dup3, dup7, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLitePushChunkDecodeTotalHighRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_pushChunk (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (pushChunkTransition.params.map Param.name)
        (transitionSignature pushChunkTransition).paramTypes I.calldata = none := by
    show decodeCalldata ["value"] [.bytes] I.calldata = none
    exact BytesStoreLiteCore.decodeCalldata_set_none_totalHigh (I := I)
      (Nat.le_of_not_gt hsizeHigh)
  exact (bytesStoreLiteX_pushChunkDecodeTotalHigh
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz36 hhi hsize hsel hoffMax hsizeHigh)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLitePushChunkRuntime_of_post_header {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (postHeader : UInt256)
    (hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader)
    (hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 36
  · exact bytesStoreLitePushChunkDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hshort
  · have hsz36 : 36 ≤ I.calldata.size := by omega
    by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact bytesStoreLitePushChunkDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hbig
    · have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hbig
      by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
      · exact bytesStoreLitePushChunkDecodeOffsetHugeRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hsz36 hhi hoff
      · by_cases hlenShort :
          I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
        · exact bytesStoreLitePushChunkDecodeLengthShortRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hsz36 hhi hoff hlenShort
        · have hlenWord :
            4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size :=
            Nat.le_of_not_gt hlenShort
          by_cases hsizeSign : I.calldata.size < 2 ^ 255
          · by_cases hlenHuge :
                ABI.solcMaxU64 <
                  (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
            · exact bytesStoreLitePushChunkDecodeLengthHugeRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
                (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hsz36 hhi hoff hlenWord hsizeSign hlenHuge
            · by_cases hpayloadList :
                ((((I.calldata.toList.drop 4).drop
                  ((calldataWord I.calldata 4).toNat + 32)).take
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat)
              · by_cases hpayloadWord :
                  UInt256.gt
                    (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                      uInt256OfByteArray
                        (I.calldata.readBytes
                          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                      ⟨32⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨1⟩
                · exact bytesStoreLitePushChunkDecodePayloadShortRuntime
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hcode hsize hperm hwv hsel hsz36 hhi hoff hlenWord hsizeSign
                    hlenHuge hpayloadList hpayloadWord
                · have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_one_of_payload_short I.calldata hsize
                      hoff hlenWord hlenHuge hpayloadList
                  have hpayloadWordFull :
                      UInt256.gt
                        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                          uInt256OfByteArray
                            (I.calldata.readBytes
                              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                          ⟨32⟩))
                        (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
                    bytesStoreLitePushChunkPayloadWordFull_of_core hpayloadWordCore
                  exact False.elim (hpayloadWord hpayloadWordFull)
              · have hpayload :
                  ((((I.calldata.toList.drop 4).drop
                    ((calldataWord I.calldata 4).toNat + 32)).take
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat) :=
                  not_ne_iff.mp hpayloadList
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
                  have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_zero_of_payload I.calldata hsize
                      hoff hlenWord hlenHuge hpayload
                  exact bytesStoreLitePushChunkPayloadWordFull_of_core hpayloadWordCore
                exact bytesStoreLitePushChunkDecodedRuntime_of_post_header
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen
                  hsz36 hhi hoff hlenWord hsizeSign
                  hlenHuge hpayload hpayloadWord
          · exact bytesStoreLitePushChunkDecodeTotalHighRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoff hsizeSign

theorem bytesStoreLitePushChunkRuntime_of_ne {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hne : chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I ≠ (⟨1⟩ : UInt256)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let oldLen : UInt256 := bytesStoreLiteChunksLengthWord σ_evm I
  let oldHeader : UInt256 := bytesStoreLitePushChunkHeaderWord σ_evm I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [oldLen, oldHeader, bytesStoreLitePushChunkHeaderWord,
      bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne
        (σ := σ_evm) (I := I) oldLen (by simpa [oldLen] using hne)
  have hloadLen :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ = oldLen := by
    simpa [evmSolm0, oldLen] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElem :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
        (chunksDataBase + oldLen) = oldHeader := by
    simpa [evmSolm0, oldLen, oldHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evmSolm0, oldLen, oldHeader, storageStore_executionEnv] using
      bytesStoreLiteChunkHeaderAfterLengthStore_of_ne (evm := evmSolm0)
        oldLen oldHeader (by simpa [oldLen] using hne) hloadElem
  exact bytesStoreLitePushChunkRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts (bytesStoreLitePushChunkHeaderWord σ_evm I)
    hheaderAfter hloadElemLen

theorem bytesStoreLitePushChunkRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let postHeader : UInt256 := bytesStoreLitePushChunkPostLengthHeaderWord σ_evm I
  have hheaderAfter :
      ((sstoreAccountMap I.codeOwner σ_evm ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).find? I.codeOwner |>.option
          ⟨0⟩ (fun acc => acc.storage.findD
            (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨0⟩)) =
        postHeader := by
    simpa [postHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLitePushChunkPostLengthHeaderWord_sstore σ_evm I
  have hloadElemLen :
      Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨1⟩ (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) =
      postHeader := by
    simpa [postHeader, bytesStoreLitePushChunkSlot] using
      bytesStoreLiteStorageLoadPushChunkPostLengthHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  exact bytesStoreLitePushChunkRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts postHeader hheaderAfter hloadElemLen

end BytesStoreLite
