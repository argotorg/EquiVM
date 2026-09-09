import Benchmarks.Dss.Flipper.DentDecreaseGuard
import Benchmarks.Dss.Flipper.BidAccess
import Benchmarks.Dss.Flipper.TendRefund

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Tail helpers for `dent(uint256,uint256,uint256)` -/

abbrev dentAfterDecreaseFluxTailStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
    [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
      wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
    "_fluxRet" ++
  [ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
  checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
  [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]

abbrev dentAfterDecreaseTailStmts : List Stmt :=
  [ .ite
      (.binary .ne sender (.storage (bidsF (.var "id") "guy")))
      (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
      [] ] ++
  dentAfterDecreaseFluxTailStmts

abbrev dentAfterRefundMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (bidPackedSlotOfWord (dentId I))
    (setAddressOffset0Word
      (flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ I)
      (solcSourceWord I))

abbrev dentAfterLotMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)

abbrev dentLocalsAfterFlux (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (dentLocalsLotOneBegLot σ I).insert "_fluxRet" (collapseReturns [])

abbrev dentLocalsAfterFluxWithTicFrom (σpre σtic : AccountMap) (I : ExecutionEnv) :
    Store :=
  (dentLocalsAfterFlux σpre I).insert "tic_"
    (.int (Int.ofNat (tendTicNewWord σtic I).toNat))

abbrev dentFluxArgValsOf (evm : EVM.State) (I : ExecutionEnv) : List Value :=
  [.fixedBytes bytes32Width
      (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)),
    .address evm.executionEnv.codeOwner,
    .address (AccountAddress.ofNat
      (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidSlotOfWord (dentId I) ⟨3⟩))
        solcAddrMask).toNat),
    .int (Int.ofNat
      (UInt256.sub
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (bidSlotOfWord (dentId I) ⟨1⟩))
        (dentLot I)).toNat)]

abbrev dentFluxArgValsMap (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
    .address I.codeOwner,
    .address (AccountAddress.ofNat (bidUsrWord (dentId I) σ I).toNat),
    .int (Int.ofNat (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I)).toNat)]

abbrev dentVatFluxSelectorWord : UInt256 :=
  UInt256.shiftLeft (⟨814276375⟩ : UInt256) ⟨225⟩

noncomputable abbrev dentVatHashMem (mem : ByteArray) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (dentId I) ⟨1⟩ mem

noncomputable abbrev dentVatFluxCallMem (mem : ByteArray) (σ : AccountMap)
    (I : ExecutionEnv) : ByteArray :=
  writeCascade (dentVatHashMem mem I)
    [(128, dentVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidUsrWord (dentId I) σ I),
     (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))]

theorem dentVatHashMem_size {mem : ByteArray} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    (dentVatHashMem mem I).size = 96 := by
  unfold dentVatHashMem
  exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize

theorem dentVatHashMem_read64 {mem : ByteArray} {I : ExecutionEnv}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentVatHashMem mem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentVatHashMem
  exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64

theorem dentVatHashMem_solcMappingSlot {mem : ByteArray} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((dentVatHashMem mem I).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (dentId I) := by
  unfold dentVatHashMem
  simpa [bidBaseOfWord] using twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize

theorem dentVatFluxSelectorWord_prefix :
    (UInt256.toByteArray dentVatFluxSelectorWord).extract 0 4 = vatFluxSelector := by
  decide +native

theorem dentVatFluxCallMem_eq_cascade (mem : ByteArray) (σ : AccountMap)
    (I : ExecutionEnv) :
    dentVatFluxCallMem mem σ I =
      writeCascade (dentVatHashMem mem I)
        [(128, dentVatFluxSelectorWord),
         (132, flipperSlotWord ⟨3⟩ σ I),
         (164, EVM.word I.codeOwner.val),
         (196, bidUsrWord (dentId I) σ I),
         (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))] := by
  rfl

theorem dentVatFluxCallMem_size {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    (dentVatFluxCallMem mem σ I).size = 260 := by
  rw [dentVatFluxCallMem_eq_cascade]
  exact writeCascade_size_of_base (dentVatHashMem mem I)
    [(128, dentVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidUsrWord (dentId I) σ I),
     (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))]
    (dentVatHashMem_size hmemSize)
    (by simp [WriteGapsOk] <;> decide +native)
    (by norm_num [writeCascadeSize])

theorem dentVatFluxCallMem_read64 {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentVatFluxCallMem mem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [dentVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_preserved_of_base (dentVatHashMem mem I)
    [(128, dentVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidUsrWord (dentId I) σ I),
     (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))]
    (dentVatHashMem_size hmemSize)
    (by simp [WindowDisjointFromWrites] <;> decide +native)]
  exact dentVatHashMem_read64 hmemSize hmemRead64

theorem dentVatFluxCallMem_read128_4 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatFluxCallMem mem σ I).readWithPadding 128 4 = vatFluxSelector := by
  rw [dentVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_window_of_head (dentVatHashMem mem I) 128 0 4
    dentVatFluxSelectorWord
    [(132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidUsrWord (dentId I) σ I),
     (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))]
    (by rw [dentVatHashMem_size hmemSize]; decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)
    (by norm_num) (by norm_num) (by norm_num)]
  exact dentVatFluxSelectorWord_prefix

theorem dentVatFluxCallMem_read132 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatFluxCallMem mem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons]
  have hbase :
      (writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord).size = 160 := by
    rw [writeWord_size]
    · rw [dentVatHashMem_size hmemSize]; decide +native
    · rw [dentVatHashMem_size hmemSize]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord)
    (base := 160) (off := 132) (word := flipperSlotWord ⟨3⟩ σ I)
    (rest := [(164, EVM.word I.codeOwner.val),
      (196, bidUsrWord (dentId I) σ I),
      (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dentVatFluxCallMem_read164 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatFluxCallMem mem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (EVM.word I.codeOwner.val) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size hmemSize]; decide +native
    · rw [dentVatHashMem_size hmemSize]; decide +native
  have hbase :
      (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)).size = 164 := by
    rw [writeWord_size]
    · rw [hmem1]; decide +native
    · rw [hmem1]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I))
    (base := 164) (off := 164) (word := EVM.word I.codeOwner.val)
    (rest := [(196, bidUsrWord (dentId I) σ I),
      (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dentVatFluxCallMem_read196 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatFluxCallMem mem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (bidUsrWord (dentId I) σ I) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size hmemSize]; decide +native
    · rw [dentVatHashMem_size hmemSize]; decide +native
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; decide +native
    · rw [hmem1]; decide +native
  have hbase : (writeWord mem2 164 (EVM.word I.codeOwner.val)).size = 196 := by
    rw [writeWord_size]
    · rw [hmem2]; decide +native
    · rw [hmem2]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (EVM.word I.codeOwner.val))
    (base := 196) (off := 196) (word := bidUsrWord (dentId I) σ I)
    (rest := [(228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

theorem dentVatFluxCallMem_read228 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatFluxCallMem mem σ I).readWithPadding 228 32 =
      UInt256.toByteArray (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I)) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  let mem3 := writeWord mem2 164 (EVM.word I.codeOwner.val)
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size hmemSize]; decide +native
    · rw [dentVatHashMem_size hmemSize]; decide +native
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; decide +native
    · rw [hmem1]; decide +native
  have hmem3 : mem3.size = 196 := by
    dsimp [mem3]
    rw [writeWord_size]
    · rw [hmem2]; decide +native
    · rw [hmem2]; decide +native
  have hbase : (writeWord mem3 196 (bidUsrWord (dentId I) σ I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem3]; decide +native
    · rw [hmem3]; decide +native
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem3 196 (bidUsrWord (dentId I) σ I))
    (base := 228) (off := 228)
    (word := UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))
    (rest := [])
    hbase (by decide +native)
    (by simp [WindowDisjointFromWrites])

theorem dentVatFluxCallMem_read {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    (dentVatFluxCallMem mem σ I).readWithPadding 128 132 =
      vatFluxSelector ++
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
      UInt256.toByteArray (EVM.word I.codeOwner.val) ++
      UInt256.toByteArray (bidUsrWord (dentId I) σ I) ++
      UInt256.toByteArray (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I)) := by
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 128 4 128
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size hmemSize])]
  rw [dentVatFluxCallMem_read128_4 hmemSize]
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 132 32 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size hmemSize])]
  rw [dentVatFluxCallMem_read132 hmemSize]
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 164 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size hmemSize])]
  rw [dentVatFluxCallMem_read164 hmemSize]
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 196 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size hmemSize])]
  rw [dentVatFluxCallMem_read196 hmemSize, dentVatFluxCallMem_read228 hmemSize]
  simp [ByteArray.append_assoc]

theorem dentVatFluxCallMem_encode {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    config.externalABI.encode? "flux" (dentFluxArgValsMap σ I) =
      some ((dentVatFluxCallMem mem σ I).readWithPadding 128 132) := by
  rw [dentVatFluxCallMem_read hmemSize]
  unfold dentFluxArgValsMap config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have husr :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidUsrWord (dentId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidUsrWord (dentId I) σ I)).toList := by
    simpa [bidUsrWord, flipperAddressReturnWord] using
      yankEncodeABIValue_address_word (flipperSlotWord (bidSlotOfWord (dentId I) ⟨3⟩) σ I)
  have hpayload :
      encodeABIValues? [bytes32, addr, addr, uint256]
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
          .address I.codeOwner,
          .address (AccountAddress.ofNat (bidUsrWord (dentId I) σ I).toNat),
          .int (Int.ofNat (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I)).toNat)] =
          some (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
            UInt256.toByteArray (EVM.word I.codeOwner.val) ++
            UInt256.toByteArray (bidUsrWord (dentId I) σ I) ++
            UInt256.toByteArray
              (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 by decide +native]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_bytes32_word, yankEncodeABIValue_this_address, husr,
      yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType bytes32 = false by decide +native,
      show isDynamicABIType addr = false by decide +native,
      show isDynamicABIType uint256 = false by decide +native,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [vatFluxSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem dentLocalsLotOne_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "vat" = none := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide)]
  simp [dentLocals, store_get_ne]

theorem dentLocalsLotOneBegLot_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "vat" = none := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_vat]

theorem dentLocalsLotOne_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "ttl" = none := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide)]
  simp [dentLocals, store_get_ne]

theorem dentLocalsLotOneBegLot_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "ttl" = none := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_ttl]

theorem dentLocalsLotOne_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "ilk" = none := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide)]
  simp [dentLocals, store_get_ne]

theorem dentLocalsLotOneBegLot_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "ilk" = none := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_ilk]

theorem dentLocalsAfterFlux_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterFlux σ I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsAfterFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_id σ I

theorem dentLocalsAfterFlux_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterFlux σ I).get? "lot" =
      some (.int (Int.ofNat (dentLot I).toNat)) := by
  rw [dentLocalsAfterFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_lot σ I

theorem dentLocalsAfterFlux_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterFlux σ I).get? "bids" = none := by
  rw [dentLocalsAfterFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_bids σ I

theorem dentLocalsAfterFlux_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterFlux σ I).get? "ttl" = none := by
  rw [dentLocalsAfterFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_ttl σ I

theorem dentLocalsAfterFlux_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterFlux σ I).get? "ilk" = none := by
  rw [dentLocalsAfterFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_ilk σ I

theorem dentLocalsAfterFluxWithTicFrom_get_id (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (dentLocalsAfterFluxWithTicFrom σpre σtic I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsAfterFluxWithTicFrom, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterFlux_get_id σpre I

theorem dentLocalsAfterFluxWithTicFrom_get_bids (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (dentLocalsAfterFluxWithTicFrom σpre σtic I).get? "bids" = none := by
  rw [dentLocalsAfterFluxWithTicFrom, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterFlux_get_bids σpre I

theorem dentLocalsAfterFluxWithTicFrom_get_tic (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (dentLocalsAfterFluxWithTicFrom σpre σtic I).get? "tic_" =
      some (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  rw [dentLocalsAfterFluxWithTicFrom, store_get_self]

theorem evalExpr_dentTicVarWithTicFrom {evm : EVM.State} {σpre σtic : AccountMap}
    {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σpre σtic I }
      evm (.var "tic_") = .ok (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  exact evalExpr_varUInt256 (evm := evm)
    (locals := dentLocalsAfterFluxWithTicFrom σpre σtic I)
    (name := "tic_") (value := tendTicNewWord σtic I)
    (dentLocalsAfterFluxWithTicFrom_get_tic σpre σtic I)

theorem evalExpr_dentTicNewGeNow_true_from {evm : EVM.State} {σpre σtic : AccountMap}
    {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (hfit : (tendNow48 I).toNat + (tendTtlWord σtic I).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σpre σtic I }
      evm (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic := evalExpr_dentTicVarWithTicFrom
    (evm := evm) (σpre := σpre) (σtic := σtic) (I := I)
  have hnow := evalExpr_tendNow48
    (evm := evm) (locals := dentLocalsAfterFluxWithTicFrom σpre σtic I) (I := I) hts
  have hle : (tendNow48 I).toNat ≤ (tendTicNewWord σtic I).toNat :=
    tendTicNewWord_ge_now48_noOverflow hfit
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [htic, hnow]
  simp [evalBinaryOp?, hle]
  all_goals decide

theorem evalExpr_dentDecreaseRequire_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (dentBegLotWord σ I).toNat ≤ (dentLotOneWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true) := by
  have hbegLot :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOneBegLot σ I) (name := "begLot")
      (value := dentBegLotWord σ I) (dentLocalsLotOneBegLot_get_begLot σ I)
  have hlotOne :=
    evalExpr_varUInt256 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := dentLocalsLotOneBegLot σ I) (name := "lotOne")
      (value := dentLotOneWord σ I) (dentLocalsLotOneBegLot_get_lotOne σ I)
  exact evalExpr_le_uint256_true hbegLot hlotOne hle

theorem evalExpr_dentCallerNeGuy_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcaller : solcSourceWord I = bidGuyWord (dentId I) σ I) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
        .ok (.bool false) := by
  have hsender :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ g A I) sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, initState]
    rfl
  have hguy := evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocalsLotOneBegLot σ I) (id := dentId I)
    (dentLocalsLotOneBegLot_get_id σ I) (dentLocalsLotOneBegLot_get_bids σ I)
  have haddr : AccountAddress.ofNat (bidGuyWord (dentId I) σ I).toNat = I.source := by
    rw [← hcaller, solcSource_ofNat]
  simp [evalExpr?, EvalResult.bind, bind, hsender, hguy, evalBinaryOp?, haddr]

theorem evalExpr_dentIlk_ofLocals {evm : EVM.State} {locals : Store}
    (hilk : locals.get? "ilk" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ilkRef) =
      .ok (.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))) := by
  rw [evalExpr_storage_scalar
    (t := .bytes bytes32Width)
    (loc := bytes32Loc ⟨3⟩)
    (er := ({ base := "ilk", steps := [] } : EvaledStorageRef))
    (hbase := hilk)
    (her := by simp [evalStorageRef, evalStorageRefSteps, ilkRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, ilkRef])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_bytes32 evm ⟨3⟩)

theorem evalExpr_bidUsr_of_get_id_evm {evm : EVM.State} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (bidsF (.var "id") "usr")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨3⟩))
            solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidSlotOfWord id ⟨3⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
      (id := id) (field := "usr") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_address_offset0 evm (bidSlotOfWord id ⟨3⟩))

theorem evalExpr_dentLotDelta {evm : EVM.State} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat (dentLot evm.executionEnv).toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))) =
        .ok (.int (Int.ofNat
          (UInt256.sub
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨1⟩))
            (dentLot evm.executionEnv)).toNat)) := by
  have hbidLot := evalExpr_bidLot_of_get_id_evm (evm := evm)
    (locals := locals) (id := id) hid hbids
  have hlotVar := evalExpr_varUInt256 (evm := evm) (locals := locals)
    (name := "lot") (value := dentLot evm.executionEnv) hlot
  rw [wrap256]
  simp only [evalExpr?, hbidLot, hlotVar, EvalResult.bind, bind, pure]
  change (if wordModulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidSlotOfWord id ⟨1⟩)).toNat -
          Int.ofNat (dentLot evm.executionEnv).toNat) % wordModulus))) =
    .ok (Value.int (Int.ofNat
      (UInt256.sub
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨1⟩))
        (dentLot evm.executionEnv)).toNat))
  rw [if_neg (by norm_num [wordModulus]), intModWord_sub_toNat]

theorem evalExprs_dentFluxArgs_ofLocals {evm : EVM.State} {locals : Store}
    (hid : locals.get? "id" = some (.int (Int.ofNat (dentId evm.executionEnv).toNat)))
    (hlot : locals.get? "lot" =
      some (.int (Int.ofNat (dentLot evm.executionEnv).toNat)))
    (hbids : locals.get? "bids" = none)
    (hilk : locals.get? "ilk" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
        wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
        .ok (dentFluxArgValsOf evm evm.executionEnv) := by
  have hilkEval := evalExpr_dentIlk_ofLocals (evm := evm) (locals := locals) hilk
  have husr := evalExpr_bidUsr_of_get_id_evm (evm := evm)
    (locals := locals) (id := dentId evm.executionEnv) hid hbids
  have hdelta := evalExpr_dentLotDelta (evm := evm) (locals := locals)
    (id := dentId evm.executionEnv) hid hlot hbids
  simp only [evalExprs?, evalExpr?, envValue, thisAddr, hilkEval, husr, hdelta,
    dentFluxArgValsOf, EvalResult.bind, bind, pure]

theorem flipperDentSourceBlockAfterDecreaseSameCallerTail {cA gh bl σ σ₀ A I}
    {g : UInt256} {r : ExecResult}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (dentId I) σ I)
    (htail :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        dentAfterDecreaseFluxTailStmts r) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body r := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_dentGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hmulLot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.storage (bidsF (.var "id") "lot")) (.intLit ONE)) =
          .ok (.int (Int.ofNat (dentLotOneWord σ I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_dentLotOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitLot
  have hreqLot :
      evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "lotOne") (.intLit ONE))
            (.storage (bidsF (.var "id") "lot")))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_dentLotOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitLot
  have hmulBeg :
      evalExpr? config { contract := contract, locals := dentLocalsLotOne σ I } evm0
        (mul256 (.storage begRef) (.var "lot")) =
          .ok (.int (Int.ofNat (dentBegLotWord σ I).toNat)) := by
    dsimp [evm0]
    exact evalExpr_dentBegLotMul_afterLotOne_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hreqBeg :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .or
          (.binary .eq (.var "lot") (.intLit 0))
          (.binary .eq (.binary .div (.var "begLot") (.var "lot")) (.storage begRef))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_dentBegLotRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hcallerFalse :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool false) := by
    simpa [evm0] using
      evalExpr_dentCallerNeGuy_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcaller
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hmulLot) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqLot) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hmulBeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hdec) ?_
  refine ExecBlock.consNormal (ExecStmt.iteFalse hcallerFalse ExecBlock.nil) ?_
  simpa [dentAfterDecreaseTailStmts, dentAfterDecreaseFluxTailStmts] using htail

theorem flipperDentSourceBodyFluxNoCodeSameCaller {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (dentId I) σ I)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsLotOneBegLot_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    apply evalExpr_flipperVatCodeGuard_false_ofLocals hvat
    simpa [evm0, initState] using hvatNoCode
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evm0)
        (locals := dentLocalsLotOneBegLot σ I) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux") (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        hguardFlux
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        dentAfterDecreaseFluxTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hfluxBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    simpa [locals, evm0] using
      (flipperDentSourceBlockAfterDecreaseSameCallerTail (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodyFluxCallFailureSameCaller {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmFlux : EVM.State} {outFlux : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (dentId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "flux" 0
        (dentFluxArgValsOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (false, evmFlux, outFlux) true) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsLotOneBegLot_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsFlux :
      evalExprs? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
          .ok (dentFluxArgValsOf evm0 I) := by
    exact evalExprs_dentFluxArgs_ofLocals
      (dentLocalsLotOneBegLot_get_id σ I)
      (dentLocalsLotOneBegLot_get_lot σ I)
      (dentLocalsLotOneBegLot_get_bids σ I)
      (dentLocalsLotOneBegLot_get_ilk σ I)
  have hcallFlux' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "flux" 0
        (dentFluxArgValsOf evm0 I) (false, evmFlux, outFlux) true := by
    simpa [evm0, initState] using hcallFlux
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmFlux) (locals := dentLocalsLotOneBegLot σ I)
        (receiver := .storage vatRef) (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        (argVals := dentFluxArgValsOf evm0 I) (out := outFlux) (perm := true)
        hguardFlux hvat hargsFlux hcallFlux'
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        dentAfterDecreaseFluxTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hfluxBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    simpa [locals, evm0] using
      (flipperDentSourceBlockAfterDecreaseSameCallerTail (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodySuccessSameCaller {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmFlux : EVM.State} {outFlux : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (dentId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "flux" 0
        (dentFluxArgValsOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmFlux, outFlux) true)
    (hfluxTs : evmFlux.executionEnv.header.timestamp = I.header.timestamp)
    (hfluxOwner : evmFlux.executionEnv.codeOwner = I.codeOwner)
    (hfitTic :
      (tendNow48 I).toNat +
          (tendTtlWord
            (Solm.EVM.storageStore evmFlux evmFlux.executionEnv.codeOwner
              (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)).accountMap I).toNat <
        2 ^ 48) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmLot := Solm.EVM.storageStore evmFlux evmFlux.executionEnv.codeOwner
      (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
    let evmTic := Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner
      (bidPackedSlotOfWord (dentId I))
      (setUint48Offset20Word
        (Solm.EVM.storageLoad evmLot evmLot.executionEnv.codeOwner
          (bidPackedSlotOfWord (dentId I)))
        (tendTicNewWord evmLot.accountMap I))
    ExecTransitionBody config contract evm0 locals dentTransition.body
      (.returned { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
        evmTic none) := by
  intro locals evm0 evmLot evmTic
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsLotOneBegLot_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsFlux :
      evalExprs? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
          .ok (dentFluxArgValsOf evm0 I) := by
    exact evalExprs_dentFluxArgs_ofLocals
      (dentLocalsLotOneBegLot_get_id σ I)
      (dentLocalsLotOneBegLot_get_lot σ I)
      (dentLocalsLotOneBegLot_get_bids σ I)
      (dentLocalsLotOneBegLot_get_ilk σ I)
  have hcallFlux' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "flux" 0
        (dentFluxArgValsOf evm0 I) (true, evmFlux, outFlux) true := by
    simpa [evm0, initState] using hcallFlux
  have hdecFlux : config.externalABI.decode? "flux" outFlux = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        (.ok { contract := contract, locals := dentLocalsAfterFlux σ I } evmFlux) := by
    simpa [checkedExternalCallStmts, dentLocalsAfterFlux] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmFlux) (locals := dentLocalsLotOneBegLot σ I)
        (receiver := .storage vatRef) (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        (argVals := dentFluxArgValsOf evm0 I) (out := outFlux) (perm := true)
        (value := []) hguardFlux hvat hargsFlux hcallFlux' hdecFlux
  have hlotVar :
      evalExpr? config { contract := contract, locals := dentLocalsAfterFlux σ I } evmFlux
        (.var "lot") = .ok (.int (Int.ofNat (dentLot I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmFlux) (locals := dentLocalsAfterFlux σ I)
      (name := "lot") (value := dentLot I) (dentLocalsAfterFlux_get_lot σ I)
  have hassignLot :
      assignStorageRef? config { contract := contract, locals := dentLocalsAfterFlux σ I }
        evmFlux .storage (bidsF (.var "id") "lot")
        (.int (Int.ofNat (dentLot I).toNat)) =
          .ok ({ contract := contract, locals := dentLocalsAfterFlux σ I }, evmLot) := by
    simpa [evmLot] using
      assign_bidLotStorage evmFlux (dentId I) (dentLot I)
        (dentLocalsAfterFlux_get_id σ I) (dentLocalsAfterFlux_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := dentLocalsAfterFlux σ I } evmLot
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmLot) (locals := dentLocalsAfterFlux σ I) (I := I)
      (dentLocalsAfterFlux_get_ttl σ I)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxOwner)
  have hgeTic :
      evalExpr? config
          { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
          evmLot (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
    exact evalExpr_dentTicNewGeNow_true_from (evm := evmLot)
      (σpre := σ) (σtic := evmLot.accountMap) (I := I)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
      (by simpa [evmLot] using hfitTic)
  have hticVar :
      evalExpr? config
          { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
          evmLot (.var "tic_") =
            .ok (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) := by
    exact evalExpr_dentTicVarWithTicFrom (evm := evmLot)
      (σpre := σ) (σtic := evmLot.accountMap) (I := I)
  have hassignTic :
      assignStorageRef? config
          { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
          evmLot .storage (bidsF (.var "id") "tic")
          (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) =
        .ok ({ contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }, evmTic) := by
    simpa [evmTic] using
      assign_bidTicStorage evmLot (dentId I) (tendTicNewWord evmLot.accountMap I)
        (tendTicNewWord_bound evmLot.accountMap I)
        (dentLocalsAfterFluxWithTicFrom_get_id σ evmLot.accountMap I)
        (dentLocalsAfterFluxWithTicFrom_get_bids σ evmLot.accountMap I)
  have hpost :
      ExecBlock config { contract := contract, locals := dentLocalsAfterFlux σ I } evmFlux
        ([ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        (.ok { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
          evmTic) := by
    refine ExecBlock.consNormal (ExecStmt.assign hlotVar hassignLot) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hgeTic) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hticVar hassignTic) ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        dentAfterDecreaseFluxTailStmts
        (.ok { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
          evmTic) := by
    have hjoined :
        ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
          (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
              wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
            "_fluxRet" ++
          ([ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
            checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]))
          (.ok { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
            evmTic) := by
      exact execBlock_append hfluxBlock hpost
    simpa [dentAfterDecreaseFluxTailStmts, List.append_assoc] using hjoined
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        (.ok { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
          evmTic) := by
    simpa [locals, evm0] using
      (flipperDentSourceBlockAfterDecreaseSameCallerTail (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockOK hblock

theorem flipperDentSourceBodyAdd48OverflowSameCaller {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmFlux : EVM.State} {outFlux : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (dentId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := dentLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .lt (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (hfitLot : (bidLotWord (dentId I) σ I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg : (dentBegWord σ I).toNat * (dentLot I).toNat < UInt256.size)
    (hdec :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "begLot") (.var "lotOne")) = .ok (.bool true))
    (hcaller : solcSourceWord I = bidGuyWord (dentId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "flux" 0
        (dentFluxArgValsOf (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmFlux, outFlux) true)
    (hfluxTs : evmFlux.executionEnv.header.timestamp = I.header.timestamp)
    (hfluxOwner : evmFlux.executionEnv.codeOwner = I.codeOwner)
    (hoverTic :
      2 ^ 48 ≤
        (tendNow48 I).toNat +
          (tendTtlWord
            (Solm.EVM.storageStore evmFlux evmFlux.executionEnv.codeOwner
              (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)).accountMap I).toNat) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  let evmLot := Solm.EVM.storageStore evmFlux evmFlux.executionEnv.codeOwner
    (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsLotOneBegLot_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsFlux :
      evalExprs? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
          .ok (dentFluxArgValsOf evm0 I) := by
    exact evalExprs_dentFluxArgs_ofLocals
      (dentLocalsLotOneBegLot_get_id σ I)
      (dentLocalsLotOneBegLot_get_lot σ I)
      (dentLocalsLotOneBegLot_get_bids σ I)
      (dentLocalsLotOneBegLot_get_ilk σ I)
  have hcallFlux' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "flux" 0
        (dentFluxArgValsOf evm0 I) (true, evmFlux, outFlux) true := by
    simpa [evm0, initState] using hcallFlux
  have hdecFlux : config.externalABI.decode? "flux" outFlux = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        (.ok { contract := contract, locals := dentLocalsAfterFlux σ I } evmFlux) := by
    simpa [checkedExternalCallStmts, dentLocalsAfterFlux] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmFlux) (locals := dentLocalsLotOneBegLot σ I)
        (receiver := .storage vatRef) (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        (argVals := dentFluxArgValsOf evm0 I) (out := outFlux) (perm := true)
        (value := []) hguardFlux hvat hargsFlux hcallFlux' hdecFlux
  have hlotVar :
      evalExpr? config { contract := contract, locals := dentLocalsAfterFlux σ I } evmFlux
        (.var "lot") = .ok (.int (Int.ofNat (dentLot I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmFlux) (locals := dentLocalsAfterFlux σ I)
      (name := "lot") (value := dentLot I) (dentLocalsAfterFlux_get_lot σ I)
  have hassignLot :
      assignStorageRef? config { contract := contract, locals := dentLocalsAfterFlux σ I }
        evmFlux .storage (bidsF (.var "id") "lot")
        (.int (Int.ofNat (dentLot I).toNat)) =
          .ok ({ contract := contract, locals := dentLocalsAfterFlux σ I }, evmLot) := by
    simpa [evmLot] using
      assign_bidLotStorage evmFlux (dentId I) (dentLot I)
        (dentLocalsAfterFlux_get_id σ I) (dentLocalsAfterFlux_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := dentLocalsAfterFlux σ I } evmLot
        (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmLot) (locals := dentLocalsAfterFlux σ I) (I := I)
      (dentLocalsAfterFlux_get_ttl σ I)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxOwner)
  have hgeTicFalse :
      evalExpr? config
          { contract := contract, locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I }
          evmLot (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
    have htic := evalExpr_dentTicVarWithTicFrom (evm := evmLot)
      (σpre := σ) (σtic := evmLot.accountMap) (I := I)
    have hnow := evalExpr_tendNow48
      (evm := evmLot) (locals := dentLocalsAfterFluxWithTicFrom σ evmLot.accountMap I)
      (I := I) (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
    have hlt : (tendTicNewWord evmLot.accountMap I).toNat < (tendNow48 I).toNat :=
      tendTicNewWord_lt_now48_overflow (by simpa [evmLot] using hoverTic)
    exact evalExpr_ge_uint256_false htic hnow hlt
  have hpost :
      ExecBlock config { contract := contract, locals := dentLocalsAfterFlux σ I } evmFlux
        ([ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.assign hlotVar hassignLot) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hgeTicFalse)
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        dentAfterDecreaseFluxTailStmts .reverted := by
    have hjoined :
        ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
          (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
              wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
            "_fluxRet" ++
          ([ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
            checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]))
          .reverted := by
      exact execBlock_append hfluxBlock hpost
    simpa [dentAfterDecreaseFluxTailStmts, List.append_assoc] using hjoined
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    simpa [locals, evm0] using
      (flipperDentSourceBlockAfterDecreaseSameCallerTail (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDentX_skipRefund {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hcaller : solcSourceWord I = bidGuyWord (dentId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨4733⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4750 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4752, C4752, rd4752raw⟩ := rd4750.sload (by decide +native) (by evm_ov)
  have rd4752 : RD flipperBytecode I g s0 ⟨4752⟩
      [bidPackedWord (dentId I) σ I, dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4752 C4752 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) =
          bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd] using rd4752raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have rd4763raw := evm_run rd4752 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  obtain ⟨k4763, C4763, rd4763⟩ : ∃ k' C',
      RD flipperBytecode I g s0 ⟨4763⟩
        [UInt256.eq (solcSourceWord I) (bidGuyWord (dentId I) σ I), dentBid I,
          dentLot I, dentId I, ret, sel]
        (twoWordHashMem (dentId I) ⟨1⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [bidGuyWord, bidPackedWord, flipperAddressReturnWord, hmask160, u256_land_comm]
        using rd4763raw⟩
  have heq : UInt256.eq (solcSourceWord I) (bidGuyWord (dentId I) σ I) = ⟨1⟩ := by
    rw [hcaller]
    exact u256_eq_refl _
  rw [heq] at rd4763
  exact ⟨_, _, evm_run rd4763 with [
    raw push2 ⟨4927⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]⟩

theorem flipperDentDecodePushMask5104 :
    decode flipperBytecode (⟨5104⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

theorem flipperDentX_toFluxExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5037⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawIlk := flipperSlotWord ⟨3⟩ σ I
  let rawUsr := flipperSlotWord (bidSlotOfWord (dentId I) ⟨3⟩) σ I
  let rawLot := flipperSlotWord (bidSlotOfWord (dentId I) ⟨1⟩) σ I
  let base := solcMappingSlot ⟨1⟩ (dentId I)
  let memHash := dentVatHashMem mem I
  let memSel := writeWord memHash 128 dentVatFluxSelectorWord
  let memIlk := writeWord memSel 132 rawIlk
  let memThis := writeWord memIlk 164 (EVM.word I.codeOwner.val)
  let memUsr := writeWord memThis 196 (bidUsrWord (dentId I) σ I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have husrCleanLeft :
      UInt256.land solcAddrMask rawUsr = bidUsrWord (dentId I) σ I := by
    simpa [rawUsr, bidUsrWord, flipperAddressReturnWord] using
      (u256_land_comm solcAddrMask rawUsr)
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (dentVatHashMem mem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dentVatHashMem mem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dentVatHashMem_size hmemSize]; decide) (by decide)
      (dentVatHashMem_read64 hmemSize hmemRead64)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (dentVatFluxCallMem mem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dentVatFluxCallMem mem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dentVatFluxCallMem_size hmemSize]; decide) (by decide)
      (dentVatFluxCallMem_read64 hmemSize hmemRead64)
  have rd4930pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov)]
  obtain ⟨k4931, C4931, rd4931raw⟩ := rd4930pre.sload (by decide +native) (by evm_ov)
  have rd4931 : RD flipperBytecode I g s0 ⟨4931⟩
      [rawVat, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k4931 C4931 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd4931raw
  have rd4934 := evm_run rd4931 with [
    raw push1 ⟨3⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k4935, C4935, rd4935raw⟩ := rd4934.sload (by decide +native) (by evm_ov)
  have rd4935 : RD flipperBytecode I g s0 ⟨4935⟩
      [rawIlk, ⟨3⟩, rawVat, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k4935 C4935 := by
    simpa [rawIlk, flipperSlotWord, solcSlotWord] using rd4935raw
  have rd4954 := evm_run rd4935 with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 3)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 3)
      (by decide +native) mem_cost
      (by simpa [memHash, base] using dentVatHashMem_solcMappingSlot hmemSize)
      (by decide) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4956, C4956, rd4956raw⟩ := rd4954.sload (by decide +native) (by evm_ov)
  have rd4956 : RD flipperBytecode I g s0 ⟨4956⟩
      [rawUsr, ⟨64⟩, ⟨1⟩, ⟨0⟩, rawIlk, base, rawVat, dentBid I,
        dentLot I, dentId I, ret, sel]
      memHash (UInt256.ofNat 3) rdata (cA, σ) k4956 C4956 := by
    have hslotAdd : base + (⟨3⟩ : UInt256) = bidSlotOfWord (dentId I) ⟨3⟩ := by
      simp [base, bidSlotOfWord, bidBaseOfWord]
    simpa [rawUsr, flipperSlotWord, hslotAdd] using rd4956raw
  have rd4959 := evm_run rd4956 with [
    raw swap5 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov)]
  obtain ⟨k4961, C4961, rd4961raw⟩ := rd4959.sload (by decide +native) (by evm_ov)
  have rd4961 : RD flipperBytecode I g s0 ⟨4961⟩
      [rawLot, ⟨64⟩, ⟨0⟩, rawIlk, rawUsr, rawVat, dentBid I,
        dentLot I, dentId I, ret, sel]
      memHash (UInt256.ofNat 3) rdata (cA, σ) k4961 C4961 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + base = bidSlotOfWord (dentId I) ⟨1⟩ := by
      simpa [base, bidSlotOfWord, bidBaseOfWord] using
        (u256_add_comm (⟨1⟩ : UInt256) (solcMappingSlot ⟨1⟩ (dentId I)))
    simpa [rawLot, flipperSlotWord, hslotAdd] using rd4961raw
  have rd4972 := evm_run rd4961 with [
    raw dup2 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨814276375⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨225⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 memSel (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4980 := evm_run rd4972 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw mstore 3 memIlk (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4981 := RD.address rd4980 (by decide +native) (by evm_ov)
  have rd4986 := evm_run rd4981 with [
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 memThis (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by
        dsimp [memThis]
        rfl)
      (by decide) (by evm_ov)]
  have rd5002 := evm_run rd4986 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 memUsr (UInt256.ofNat 8)
      (by decide +native) mem_cost
      (by
        rw [hmask160, husrCleanLeft]
        dsimp [memUsr]
        rfl)
      (by decide) (by evm_ov)]
  have rd5010 := evm_run rd5002 with [
    raw dup8 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by
        dsimp [memUsr, memThis, memIlk, memSel, memHash, dentVatFluxCallMem,
          dentVatHashMem, writeCascade, Reasoning.Theory.writeWord]
        rfl)
      (by decide) (by evm_ov)]
  have rd5037 := evm_run rd5010 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push4 ⟨1628552750⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨132⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  rw [hmask160, hvatClean] at rd5037
  exact ⟨_, _, by simpa [rawVat] using rd5037⟩

theorem flipperDentX_fluxNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem out : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd5037⟩ := flipperDentX_toFluxExtcodesizeGuard hmemSize hmemRead64 h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5037⟩) (okPc := ⟨5049⟩) rd5037
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem flipperDentX_toFluxCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem out : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) out (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨5052⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨132⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
        ret :: sel :: [])
      (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  obtain ⟨_, _, rd5037⟩ := flipperDentX_toFluxExtcodesizeGuard hmemSize hmemRead64 h
  obtain ⟨gasWord, k5052, C5052, rd5052⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5037⟩) (okPc := ⟨5049⟩) rd5037
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k5052, C5052, by simpa using rd5052⟩

theorem flipperDentX_fluxPostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {mem out0 : ByteArray} {ret sel : UInt256}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) out0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨5053⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
          ret :: sel :: [])
        (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "flux" 0
        (dentFluxArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA })
          I)
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd5052⟩ :=
    flipperDentX_toFluxCall hmemSize hmemRead64 hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k5053, C5053, hΘpack, rd5053raw,
      houtsz⟩ :=
    RD.call rd5052 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k5053, C5053, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
      decide +native
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd5053 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨5053⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
          ret :: sel :: [])
        (out.write 0 (dentVatFluxCallMem mem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 9) out (cA', σ') k5053 C5053 :=
      haw ▸ rd5053raw
    rw [hmin, byteArray_write_len_zero] at rd5053
    exact rd5053
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := dentVatFluxCallMem mem σ I) (inOff := ⟨128⟩) (inSize := ⟨132⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · simpa [dentFluxArgValsOf, dentFluxArgValsMap, initState, flipperSlotWord,
        solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidUsrWord, bidLotWord, bidSlotOfWord, bidBaseOfWord, flipperAddressReturnWord]
        using dentVatFluxCallMem_encode (σ := σ) (I := I) hmemSize
    · simpa [initState, hperm] using hΘ

theorem flipperDentX_fluxCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target bid lot id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨5053⟩
      (⟨0⟩ :: ⟨260⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5053⟩) (okPc := ⟨5069⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtsz (by simp)

theorem flipperDentX_fluxCallDepthLimit {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem out : ByteArray} {ret sel : UInt256}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (h : RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨gasWord, _, _, rd5052⟩ :=
    flipperDentX_toFluxCall hmemSize hmemRead64 hcodeSize h
  obtain ⟨k5053, C5053, rd5053raw⟩ :=
    RD.callDepthLimit
      (code := flipperBytecode) (ee := I) (g := g) (s0 := s0) (pc := ⟨5052⟩)
      (mem := dentVatFluxCallMem mem σ I) (aw := UInt256.ofNat 9) (rdata := out)
      (cA := cA) (σ := σ) (gasArg := gasWord) (target := flipperVatTargetWord σ I)
      (inOffset := ⟨128⟩) (inSize := ⟨132⟩) (outOffset := ⟨128⟩) (outSize := ⟨0⟩)
      (t := [⟨260⟩, ⟨1628552750⟩, flipperVatTargetWord σ I, dentBid I, dentLot I,
        dentId I, ret, sel])
      rd5052 (by decide +native) hdepth (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
    decide +native
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd5053 : RD flipperBytecode I g s0 ⟨5053⟩
      (⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
        ret :: sel :: [])
      (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9) ByteArray.empty (cA, σ)
      k5053 C5053 := by
    rw [hmin, byteArray_write_len_zero] at rd5053raw
    exact haw ▸ rd5053raw
  exact flipperDentX_fluxCallFailure rd5053 (by decide +native)

theorem flipperDentX_fluxCallSuccessToStoreStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target bid lot id ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨5053⟩
      (⟨1⟩ :: ⟨260⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5073⟩
      (target :: bid :: lot :: id :: ret :: sel :: []) mem aw out acc k' C' := by
  obtain ⟨k5071, C5071, rd5071⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨5053⟩) (okPc := ⟨5069⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  exact ⟨_, _, evm_run rd5071 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]⟩

theorem flipperDentX_storeLotToAdd48 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {target ret sel : UInt256}
    (hperm : I.perm = true)
    (hmemSize : 64 ≤ mem.size)
    (h : RD flipperBytecode I g s0 ⟨5073⟩
      [target, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6272⟩
      [tendTtlWord (dentAfterLotMap σ I) I, tendNow I, ⟨3859⟩,
        dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 9) out
      (cA, dentAfterLotMap σ I) k' C' := by
  let mem1 := wordAt0Mem (dentId I) mem
  let mem2 := twoWordHashMem (dentId I) ⟨1⟩ mem
  have rd5092 := evm_run h with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 9) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 9) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by
        simpa [mem2, bidBaseOfWord] using
          tendTwoWordHashMem_solcMappingSlot_of_size_ge ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨k5093, C5093, rd5093raw⟩ := rd5092.sstore hperm (by decide +native) (by evm_ov)
  have rd5094 : RD flipperBytecode I g s0 ⟨5094⟩
      [target, dentBid I, dentLot I, dentId I, ret, sel]
      mem2 (UInt256.ofNat 9) out (cA, dentAfterLotMap σ I) k5093 C5093 := by
    simpa [mem2, dentAfterLotMap, bidSlotOfWord, bidBaseOfWord] using rd5093raw
  have rd5097 := evm_run rd5094 with [
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov)]
  obtain ⟨k5098, C5098, rd5098raw⟩ := rd5097.sload (by decide +native) (by evm_ov)
  have rd5098 : RD flipperBytecode I g s0 ⟨5098⟩
      [flipperSlotWord ⟨5⟩ (dentAfterLotMap σ I) I,
        dentBid I, dentLot I, dentId I, ret, sel]
      mem2 (UInt256.ofNat 9) out (cA, dentAfterLotMap σ I) k5098 C5098 := by
    simpa [flipperSlotWord, solcSlotWord] using rd5098raw
  have rd5115 := evm_run rd5098 with [
    raw push2 ⟨3859⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw timestamp (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperDentDecodePushMask5104
      (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push2 ⟨6272⟩ (by decide +native) (by evm_ov)]
  have httlRaw :
      UInt256.land uint48Mask (flipperSlotWord ⟨5⟩ (dentAfterLotMap σ I) I) =
        tendTtlWord (dentAfterLotMap σ I) I := by
    simpa [tendTtlWord, flipperUint48Offset0Word, u256_land_comm]
  rw [httlRaw] at rd5115
  exact ⟨_, _, rd5115.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem flipperDentX_add48Success {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {ret sel : UInt256}
    (hfit : (tendNow48 I).toNat + (tendTtlWord σ I).toNat < 2 ^ 48)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [tendTtlWord σ I, tendNow I, ⟨3859⟩, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3859⟩
      [tendNow I + tendTtlWord σ I, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 9) out (cA, σ) k' C' := by
  have rd6289 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperTendDecodePushMask6276
      (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov)]
  have hltWord :
      UInt256.lt (tendTicNewWord σ I) (tendNow48 I) = ⟨0⟩ :=
    ult_zero (tendTicNewWord_ge_now48_noOverflow hfit)
  have hltRaw :
      UInt256.lt
        (UInt256.land (tendNow I + tendTtlWord σ I) uint48Mask)
        (UInt256.land (tendNow I) uint48Mask) = ⟨0⟩ := by
    simpa [tendNow48, tendTicNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6290
  have rd6299 := rd6290.push2 ⟨6299⟩ (by decide +native) (by evm_ov)
    |>.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd6299 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]⟩

theorem flipperDentX_add48Overflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {ret sel : UInt256}
    (hover : 2 ^ 48 ≤ (tendNow48 I).toNat + (tendTtlWord σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [tendTtlWord σ I, tendNow I, ⟨3859⟩, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd6289 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperTendDecodePushMask6276
      (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov)]
  have hltWord :
      UInt256.lt (tendTicNewWord σ I) (tendNow48 I) = ⟨1⟩ :=
    ult_one (tendTicNewWord_lt_now48_overflow hover)
  have hltRaw :
      UInt256.lt
        (UInt256.land (tendNow I + tendTtlWord σ I) uint48Mask)
        (UInt256.land (tendNow I) uint48Mask) = ⟨1⟩ := by
    simpa [tendNow48, tendTicNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6290
  have rd6295 := rd6290.push2 ⟨6299⟩ (by decide +native) (by evm_ov)
    |>.jumpiNT (by decide +native) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd6295 (by decide +native) (by decide +native)
    (by decide +native) (by evm_ov)

theorem flipperDentX_storeTicReturn {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hmemSize : 64 ≤ mem.size)
    (h : RD flipperBytecode I g s0 ⟨3859⟩
      [tendNow I + tendTtlWord σ I, dentBid I, dentLot I, dentId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 9) out (cA, σ) k C) :
    RDret flipperBytecode g s0 (cA, tendStoreTicMap σ I) ByteArray.empty := by
  let mem1 := wordAt0Mem (dentId I) mem
  let mem2 := twoWordHashMem (dentId I) ⟨1⟩ mem
  have rd3878 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 9) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 9) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by
        simpa [mem2, bidBaseOfWord] using
          tendTwoWordHashMem_solcMappingSlot_of_size_ge ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k3880, C3880, rd3880raw⟩ := rd3878.sload (by decide +native) (by evm_ov)
  have rd3880 : RD flipperBytecode I g s0 ⟨3880⟩
      [flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ I,
        bidPackedSlotOfWord (dentId I), dentBid I, dentLot I,
        tendNow I + tendTtlWord σ I, ⟨323⟩, sel]
      mem2 (UInt256.ofNat 9) out (cA, σ) k3880 C3880 := by
    have hslotAdd :
        ⟨2⟩ + bidBaseOfWord (dentId I) = bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [mem2, bidPackedSlotOfWord, flipperSlotWord, hslotAdd] using rd3880raw
  have rd3917 := evm_run rd3880 with [
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperTendDecodePushMask3880
      (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      flipperTendDecodePushMask3897
      (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw not (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw or (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov)]
  have hstoredRaw :
      UInt256.lor
          (UInt256.land (flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ I)
            (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨160⟩)))
          (UInt256.mul
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
            (UInt256.land uint48Mask (tendNow I + tendTtlWord σ I))) =
        tendStoredTicWord σ I := by
    simpa [dentId, tendId] using tendStoredTicRuntimeWord σ I
  rw [hstoredRaw] at rd3917
  obtain ⟨_, _, rd3918⟩ := rd3917.sstore hperm (by decide +native) (by evm_ov)
  have rd3920 := evm_run rd3918 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  have rd324 := rd3920.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd324 (by decide +native) (by evm_ov)

end Benchmarks.Dss.Flipper
