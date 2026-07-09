import Benchmarks.Dss.Flipper.DentSameCaller

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Caller-changing refund branch for `dent(uint256,uint256,uint256)` -/

abbrev dentRefundMoveArgValsOf (evm : EVM.State) (I : ExecutionEnv) : List Value :=
  [.address evm.executionEnv.source,
    .address
      (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          solcAddrMask).toNat),
    .int (Int.ofNat (dentBid I).toNat)]

abbrev dentRefundMoveArgValsMap (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [.address I.source,
    .address (AccountAddress.ofNat (bidGuyWord (dentId I) σ I).toNat),
    .int (Int.ofNat (dentBid I).toNat)]

noncomputable abbrev dentVatRefundCallMem (mem : ByteArray) (σ : AccountMap)
    (I : ExecutionEnv) : ByteArray :=
  writeCascade (dentVatHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (dentId I) σ I),
     (196, dentBid I)]

abbrev dentLocalsAfterRefund (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (dentLocalsLotOneBegLot σ I).insert "_refundRet" (collapseReturns [])

abbrev dentLocalsAfterRefundFlux (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (dentLocalsAfterRefund σ I).insert "_fluxRet" (collapseReturns [])

abbrev dentLocalsAfterRefundWithTicFrom (σpre σtic : AccountMap) (I : ExecutionEnv) :
    Store :=
  (dentLocalsAfterRefundFlux σpre I).insert "tic_"
    (.int (Int.ofNat (tendTicNewWord σtic I).toNat))

theorem dentVatRefundCallMem_eq_cascade (mem : ByteArray) (σ : AccountMap)
    (I : ExecutionEnv) :
    dentVatRefundCallMem mem σ I =
      writeCascade (dentVatHashMem mem I)
        [(128, yankVatMoveSelectorWord),
         (132, solcSourceWord I),
         (164, bidGuyWord (dentId I) σ I),
         (196, dentBid I)] := by
  rfl

theorem dentVatRefundCallMem_size {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    (dentVatRefundCallMem mem σ I).size = 228 := by
  rw [dentVatRefundCallMem_eq_cascade]
  exact writeCascade_size_of_base (dentVatHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (dentId I) σ I),
     (196, dentBid I)]
    (dentVatHashMem_size hmemSize)
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem dentVatRefundCallMem_read64 {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentVatRefundCallMem mem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [dentVatRefundCallMem_eq_cascade]
  rw [writeCascade_read_preserved_of_base (dentVatHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGuyWord (dentId I) σ I),
     (196, dentBid I)]
    (dentVatHashMem_size hmemSize)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact dentVatHashMem_read64 hmemSize hmemRead64

theorem dentVatRefundCallMem_read128_4 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatRefundCallMem mem σ I).readWithPadding 128 4 = moveSelector := by
  rw [dentVatRefundCallMem_eq_cascade]
  rw [writeCascade_read_window_of_head (dentVatHashMem mem I) 128 0 4
    yankVatMoveSelectorWord
    [(132, solcSourceWord I),
     (164, bidGuyWord (dentId I) σ I),
     (196, dentBid I)]
    (by rw [dentVatHashMem_size hmemSize]; native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact yankVatMoveSelectorWord_prefix

theorem dentVatRefundCallMem_read132 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatRefundCallMem mem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  rw [dentVatRefundCallMem_eq_cascade, writeCascade_cons]
  have hbase :
      (writeWord (dentVatHashMem mem I) 128 yankVatMoveSelectorWord).size = 160 := by
    rw [writeWord_size]
    · rw [dentVatHashMem_size hmemSize]; native_decide
    · rw [dentVatHashMem_size hmemSize]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (dentVatHashMem mem I) 128 yankVatMoveSelectorWord)
    (base := 160) (off := 132) (word := solcSourceWord I)
    (rest := [(164, bidGuyWord (dentId I) σ I), (196, dentBid I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem dentVatRefundCallMem_read164 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatRefundCallMem mem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (bidGuyWord (dentId I) σ I) := by
  rw [dentVatRefundCallMem_eq_cascade, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 yankVatMoveSelectorWord
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size hmemSize]; native_decide
    · rw [dentVatHashMem_size hmemSize]; native_decide
  have hbase : (writeWord mem1 132 (solcSourceWord I)).size = 164 := by
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (solcSourceWord I))
    (base := 164) (off := 164) (word := bidGuyWord (dentId I) σ I)
    (rest := [(196, dentBid I)])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem dentVatRefundCallMem_read196 {mem : ByteArray} {σ : AccountMap}
    {I : ExecutionEnv} (hmemSize : mem.size = 96) :
    (dentVatRefundCallMem mem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (dentBid I) := by
  rw [dentVatRefundCallMem_eq_cascade, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  have hmem1 : mem1.size = 160 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size hmemSize]; native_decide
    · rw [dentVatHashMem_size hmemSize]; native_decide
  have hmem2 : mem2.size = 164 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hbase : (writeWord mem2 164 (bidGuyWord (dentId I) σ I)).size = 196 := by
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (bidGuyWord (dentId I) σ I))
    (base := 196) (off := 196) (word := dentBid I) (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem dentVatRefundCallMem_read {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    (dentVatRefundCallMem mem σ I).readWithPadding 128 100 =
      moveSelector ++
      UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (bidGuyWord (dentId I) σ I) ++
      UInt256.toByteArray (dentBid I) := by
  rw [byteArray_readWithPadding_split (dentVatRefundCallMem mem σ I) 128 4 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatRefundCallMem_size hmemSize])]
  rw [dentVatRefundCallMem_read128_4 hmemSize]
  rw [byteArray_readWithPadding_split (dentVatRefundCallMem mem σ I) 132 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatRefundCallMem_size hmemSize])]
  rw [dentVatRefundCallMem_read132 hmemSize]
  rw [byteArray_readWithPadding_split (dentVatRefundCallMem mem σ I) 164 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatRefundCallMem_size hmemSize])]
  rw [dentVatRefundCallMem_read164 hmemSize, dentVatRefundCallMem_read196 hmemSize]
  simp [ByteArray.append_assoc]

theorem dentVatRefundCallMem_encode {mem : ByteArray} {σ : AccountMap} {I : ExecutionEnv}
    (hmemSize : mem.size = 96) :
    config.externalABI.encode? "move" (dentRefundMoveArgValsMap σ I) =
      some ((dentVatRefundCallMem mem σ I).readWithPadding 128 100) := by
  rw [dentVatRefundCallMem_read hmemSize]
  unfold dentRefundMoveArgValsMap config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hguy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidGuyWord (dentId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidGuyWord (dentId I) σ I)).toList := by
    simpa [bidGuyWord, flipperAddressReturnWord] using
      yankEncodeABIValue_address_word (flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ I)
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
        [.address I.source,
          .address (AccountAddress.ofNat (bidGuyWord (dentId I) σ I).toNat),
          .int (Int.ofNat (dentBid I).toNat)] =
          some (UInt256.toByteArray (solcSourceWord I) ++
            UInt256.toByteArray (bidGuyWord (dentId I) σ I) ++
            UInt256.toByteArray (dentBid I)).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [addr, addr, uint256] = some 96 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_source_address, hguy, yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType addr = false by native_decide,
      show isDynamicABIType uint256 = false by native_decide,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [moveSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem dentLocalsLotOne_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOne σ I).get? "bid" =
      some (.int (Int.ofNat (dentBid I).toNat)) := by
  rw [dentLocalsLotOne, store_get_ne _ _ (by decide), dentLocals_get_bid]

theorem dentLocalsLotOneBegLot_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsLotOneBegLot σ I).get? "bid" =
      some (.int (Int.ofNat (dentBid I).toNat)) := by
  rw [dentLocalsLotOneBegLot, store_get_ne _ _ (by decide), dentLocalsLotOne_get_bid]

theorem dentLocalsAfterRefund_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefund σ I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_id σ I

theorem dentLocalsAfterRefund_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefund σ I).get? "lot" =
      some (.int (Int.ofNat (dentLot I).toNat)) := by
  rw [dentLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_lot σ I

theorem dentLocalsAfterRefund_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefund σ I).get? "bid" =
      some (.int (Int.ofNat (dentBid I).toNat)) := by
  rw [dentLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_bid σ I

theorem dentLocalsAfterRefund_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefund σ I).get? "bids" = none := by
  rw [dentLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_bids σ I

theorem dentLocalsAfterRefund_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefund σ I).get? "vat" = none := by
  rw [dentLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_vat σ I

theorem dentLocalsAfterRefund_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefund σ I).get? "ttl" = none := by
  rw [dentLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_ttl σ I

theorem dentLocalsAfterRefund_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefund σ I).get? "ilk" = none := by
  rw [dentLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact dentLocalsLotOneBegLot_get_ilk σ I

theorem dentLocalsAfterRefundFlux_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefundFlux σ I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsAfterRefundFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterRefund_get_id σ I

theorem dentLocalsAfterRefundFlux_get_lot (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefundFlux σ I).get? "lot" =
      some (.int (Int.ofNat (dentLot I).toNat)) := by
  rw [dentLocalsAfterRefundFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterRefund_get_lot σ I

theorem dentLocalsAfterRefundFlux_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefundFlux σ I).get? "bids" = none := by
  rw [dentLocalsAfterRefundFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterRefund_get_bids σ I

theorem dentLocalsAfterRefundFlux_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefundFlux σ I).get? "ttl" = none := by
  rw [dentLocalsAfterRefundFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterRefund_get_ttl σ I

theorem dentLocalsAfterRefundFlux_get_ilk (σ : AccountMap) (I : ExecutionEnv) :
    (dentLocalsAfterRefundFlux σ I).get? "ilk" = none := by
  rw [dentLocalsAfterRefundFlux, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterRefund_get_ilk σ I

theorem dentLocalsAfterRefundWithTicFrom_get_id (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (dentLocalsAfterRefundWithTicFrom σpre σtic I).get? "id" =
      some (.int (Int.ofNat (dentId I).toNat)) := by
  rw [dentLocalsAfterRefundWithTicFrom, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterRefundFlux_get_id σpre I

theorem dentLocalsAfterRefundWithTicFrom_get_bids (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (dentLocalsAfterRefundWithTicFrom σpre σtic I).get? "bids" = none := by
  rw [dentLocalsAfterRefundWithTicFrom, store_get_ne _ _ (by decide)]
  exact dentLocalsAfterRefundFlux_get_bids σpre I

theorem dentLocalsAfterRefundWithTicFrom_get_tic (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (dentLocalsAfterRefundWithTicFrom σpre σtic I).get? "tic_" =
      some (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  rw [dentLocalsAfterRefundWithTicFrom, store_get_self]

theorem evalExpr_dentCallerNeGuy_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I) :
    evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
        .ok (.bool true) := by
  have hsender :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ g A I) sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, initState]
    rfl
  have hguy := evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := dentLocalsLotOneBegLot σ I) (id := dentId I)
    (dentLocalsLotOneBegLot_get_id σ I) (dentLocalsLotOneBegLot_get_bids σ I)
  have haddr : I.source ≠ AccountAddress.ofNat (bidGuyWord (dentId I) σ I).toNat := by
    intro hbad
    have hmask := keyValueToWord_address_ofNat_mask (bidGuyWord (dentId I) σ I)
    rw [← hbad] at hmask
    have hsourceKey : keyValueToWord (.address I.source) = solcSourceWord I := by
      simp [keyValueToWord_address, solcSourceWord]
    rw [hsourceKey] at hmask
    have hclean :
        UInt256.land solcAddrMask (bidGuyWord (dentId I) σ I) =
          bidGuyWord (dentId I) σ I := by
      simpa [bidGuyWord, flipperAddressReturnWord, u256_land_comm] using
        (solcAddrMask_clean
          (solcAddrMask_result_canonical
            (flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ I)))
    exact hcaller (by simpa [hclean] using hmask)
  simp [evalExpr?, EvalResult.bind, bind, hsender, hguy, evalBinaryOp?, haddr]

theorem evalExprs_dentRefundMoveArgs_ofLocals {evm : EVM.State} {locals : Store}
    {I : ExecutionEnv}
    (hid : locals.get? "id" = some (.int (Int.ofNat (dentId I).toNat)))
    (hbid : locals.get? "bid" = some (.int (Int.ofNat (dentBid I).toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] =
        .ok (dentRefundMoveArgValsOf evm I) := by
  have hguy := evalExpr_bidGuy_of_get_id_evm (evm := evm)
    (locals := locals) (id := dentId I) hid hbids
  have hbidVar := evalExpr_varUInt256 (evm := evm) (locals := locals)
    (name := "bid") (value := dentBid I) hbid
  simp only [evalExprs?, evalExpr?, envValue, sender, hguy, hbidVar,
    dentRefundMoveArgValsOf, EvalResult.bind, bind, pure]

theorem evalExpr_dentLotDelta_forLocals {evm : EVM.State} {locals : Store}
    {I : ExecutionEnv}
    (hid : locals.get? "id" = some (.int (Int.ofNat (dentId I).toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat (dentLot I).toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))) =
        .ok (.int (Int.ofNat
          (UInt256.sub
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (bidSlotOfWord (dentId I) ⟨1⟩))
            (dentLot I)).toNat)) := by
  have hbidLot := evalExpr_bidLot_of_get_id_evm (evm := evm)
    (locals := locals) (id := dentId I) hid hbids
  have hlotVar := evalExpr_varUInt256 (evm := evm) (locals := locals)
    (name := "lot") (value := dentLot I) hlot
  rw [wrap256]
  simp only [evalExpr?, hbidLot, hlotVar, EvalResult.bind, bind, pure]
  change (if wordModulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidSlotOfWord (dentId I) ⟨1⟩)).toNat -
          Int.ofNat (dentLot I).toNat) % wordModulus))) =
    .ok (Value.int (Int.ofNat
      (UInt256.sub
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord (dentId I) ⟨1⟩))
        (dentLot I)).toNat))
  rw [if_neg (by norm_num [wordModulus]), intModWord_sub_toNat]

theorem evalExprs_dentFluxArgs_ofLocalsFor {evm : EVM.State} {locals : Store}
    {I : ExecutionEnv}
    (hid : locals.get? "id" = some (.int (Int.ofNat (dentId I).toNat)))
    (hlot : locals.get? "lot" = some (.int (Int.ofNat (dentLot I).toNat)))
    (hbids : locals.get? "bids" = none)
    (hilk : locals.get? "ilk" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
        wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
        .ok (dentFluxArgValsOf evm I) := by
  have hilkEval := evalExpr_dentIlk_ofLocals (evm := evm) (locals := locals) hilk
  have husr := evalExpr_bidUsr_of_get_id_evm (evm := evm)
    (locals := locals) (id := dentId I) hid hbids
  have hdelta := evalExpr_dentLotDelta_forLocals (evm := evm) (locals := locals)
    (I := I) hid hlot hbids
  simp only [evalExprs?, evalExpr?, envValue, thisAddr, hilkEval, husr, hdelta,
    dentFluxArgValsOf, EvalResult.bind, bind, pure]

theorem evalExpr_dentAfterRefundTicVarWithTicFrom {evm : EVM.State}
    {σpre σtic : AccountMap} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := dentLocalsAfterRefundWithTicFrom σpre σtic I }
      evm (.var "tic_") = .ok (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  exact evalExpr_varUInt256 (evm := evm)
    (locals := dentLocalsAfterRefundWithTicFrom σpre σtic I)
    (name := "tic_") (value := tendTicNewWord σtic I)
    (dentLocalsAfterRefundWithTicFrom_get_tic σpre σtic I)

theorem evalExpr_dentAfterRefundTicNewGeNow_true_from {evm : EVM.State}
    {σpre σtic : AccountMap} {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (hfit : (tendNow48 I).toNat + (tendTtlWord σtic I).toNat < 2 ^ 48) :
    evalExpr? config
      { contract := contract, locals := dentLocalsAfterRefundWithTicFrom σpre σtic I }
      evm (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic := evalExpr_dentAfterRefundTicVarWithTicFrom (evm := evm)
    (σpre := σpre) (σtic := σtic) (I := I)
  have hnow := evalExpr_tendNow48
    (evm := evm) (locals := dentLocalsAfterRefundWithTicFrom σpre σtic I) (I := I) hts
  have hle : (tendNow48 I).toNat ≤ (tendTicNewWord σtic I).toNat :=
    tendTicNewWord_ge_now48_noOverflow hfit
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [htic, hnow]
  simp [evalBinaryOp?, hle]
  all_goals decide

theorem flipperDentSourceBlockAfterRefundSuccessTail {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund : EVM.State} {outRefund : ByteArray} {r : ExecResult}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (dentRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (htail :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        dentAfterDecreaseFluxTailStmts r) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
      (bidPackedSlotOfWord (dentId I))
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
          (bidPackedSlotOfWord (dentId I)))
        (solcSourceWord evmRefund.executionEnv))
    ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body r := by
  intro locals evm0 evmGuy
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
  have hcallerTrue :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_dentCallerNeGuy_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsLotOneBegLot_get_vat σ I)
  have hguardRefund :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsRefund :
      evalExprs? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] =
          .ok (dentRefundMoveArgValsOf evm0 I) := by
    exact evalExprs_dentRefundMoveArgs_ofLocals
      (dentLocalsLotOneBegLot_get_id σ I)
      (dentLocalsLotOneBegLot_get_bid σ I)
      (dentLocalsLotOneBegLot_get_bids σ I)
  have hcallRefund' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "move" 0
        (dentRefundMoveArgValsOf evm0 I) (true, evmRefund, outRefund) true := by
    simpa [evm0, initState] using hcallRefund
  have hdecRefund : config.externalABI.decode? "move" outRefund = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hrefundBlock :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet")
        (.ok { contract := contract, locals := dentLocalsAfterRefund σ I } evmRefund) := by
    simpa [checkedExternalCallStmts, dentLocalsAfterRefund] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmRefund) (locals := dentLocalsLotOneBegLot σ I)
        (receiver := .storage vatRef) (retVar := "_refundRet") (name := "move")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"), .var "bid"])
        (argVals := dentRefundMoveArgValsOf evm0 I) (out := outRefund) (perm := true)
        (value := []) hguardRefund hvat hargsRefund hcallRefund' hdecRefund
  have hsender :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmRefund sender = .ok (.address evmRefund.executionEnv.source) := by
    simp [sender, evalExpr?, envValue]
    rfl
  have hassignGuy :
      assignStorageRef? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmRefund .storage (bidsF (.var "id") "guy")
        (.address evmRefund.executionEnv.source) =
          .ok ({ contract := contract, locals := dentLocalsAfterRefund σ I }, evmGuy) := by
    simpa [evmGuy] using
      assign_bidGuyStorage evmRefund (dentId I)
        (dentLocalsAfterRefund_get_id σ I) (dentLocalsAfterRefund_get_bids σ I)
  have hassignBlock :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmRefund [ .assign .storage (bidsF (.var "id") "guy") sender ]
        (.ok { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy) := by
    exact ExecBlock.consNormal (ExecStmt.assign hsender hassignGuy) ExecBlock.nil
  have hthen :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        (.ok { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy) := by
    exact execBlock_append hrefundBlock hassignBlock
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
  refine ExecBlock.consNormal (ExecStmt.iteTrue hcallerTrue hthen) ?_
  simpa [dentAfterDecreaseTailStmts, dentAfterDecreaseFluxTailStmts] using htail

theorem flipperDentSourceBodyRefundBranchRevert {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hbranch :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
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
  have hcallerTrue :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_dentCallerNeGuy_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcaller
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
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
    exact ExecBlock.consRevert (ExecStmt.iteTrue hcallerTrue hbranch)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodyRefundNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
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
  have hguardRefund :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    exact evalExpr_flipperVatCodeGuard_false_ofLocals hvat
      (by simpa [evm0, initState] using hvatNoCode)
  have hrefundBlock :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evm0)
        (locals := dentLocalsLotOneBegLot σ I) (receiver := .storage vatRef)
        (retVar := "_refundRet") (name := "move") (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"), .var "bid"])
        hguardRefund
  have hbranch :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "guy") sender ])
      hrefundBlock (by intro f' e' h; cases h)
  simpa [locals, evm0] using
    (flipperDentSourceBodyRefundBranchRevert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg hdec
      hcaller hbranch)

theorem flipperDentSourceBodyRefundCallFailure {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund : EVM.State} {outRefund : ByteArray}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (dentRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (false, evmRefund, outRefund) true) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsLotOneBegLot_get_vat σ I)
  have hguardRefund :
      evalExpr? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat
      (by simpa [evm0, initState] using hvatCode)
  have hargsRefund :
      evalExprs? config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] =
          .ok (dentRefundMoveArgValsOf evm0 I) := by
    exact evalExprs_dentRefundMoveArgs_ofLocals
      (dentLocalsLotOneBegLot_get_id σ I)
      (dentLocalsLotOneBegLot_get_bid σ I)
      (dentLocalsLotOneBegLot_get_bids σ I)
  have hcallRefund' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "move" 0
        (dentRefundMoveArgValsOf evm0 I) (false, evmRefund, outRefund) true := by
    simpa [evm0, initState] using hcallRefund
  have hrefundBlock :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmRefund) (locals := dentLocalsLotOneBegLot σ I)
        (receiver := .storage vatRef) (retVar := "_refundRet") (name := "move")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"), .var "bid"])
        (argVals := dentRefundMoveArgValsOf evm0 I) (out := outRefund) (perm := true)
        hguardRefund hvat hargsRefund hcallRefund'
  have hbranch :
      ExecBlock config { contract := contract, locals := dentLocalsLotOneBegLot σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "guy") sender ])
      hrefundBlock (by intro f' e' h; cases h)
  simpa [locals, evm0] using
    (flipperDentSourceBodyRefundBranchRevert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg hdec
      hcaller hbranch)

theorem flipperDentSourceBodyFluxNoCodeAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund : EVM.State} {outRefund : ByteArray}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (dentRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hfluxNoCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      (UInt256.ofNat
        ((evmGuy.lookupAccount
          (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (dentId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I)))
      (solcSourceWord evmRefund.executionEnv))
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsAfterRefund_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    exact evalExpr_flipperVatCodeGuard_false_ofLocals hvat (by simpa [evmGuy] using hfluxNoCode)
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evmGuy)
        (locals := dentLocalsAfterRefund σ I) (receiver := .storage vatRef)
        (retVar := "_fluxRet") (name := "flux") (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        hguardFlux
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        dentAfterDecreaseFluxTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hfluxBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    simpa [locals, evm0, evmGuy] using
      (flipperDentSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller hrefundCode hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodyFluxCallFailureAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund evmFlux : EVM.State} {outRefund outFlux : ByteArray}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (dentRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hfluxCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      0 <
        (UInt256.ofNat
          ((evmGuy.lookupAccount
            (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "flux" 0
        (dentFluxArgValsOf evmGuy I) (false, evmFlux, outFlux) true) :
    let locals := dentLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals dentTransition.body .reverted := by
  intro locals evm0
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (dentId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I)))
      (solcSourceWord evmRefund.executionEnv))
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsAfterRefund_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat (by simpa [evmGuy] using hfluxCode)
  have hargsFlux :
      evalExprs? config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
          .ok (dentFluxArgValsOf evmGuy I) := by
    exact evalExprs_dentFluxArgs_ofLocalsFor
      (evm := evmGuy) (locals := dentLocalsAfterRefund σ I) (I := I)
      (dentLocalsAfterRefund_get_id σ I)
      (dentLocalsAfterRefund_get_lot σ I)
      (dentLocalsAfterRefund_get_bids σ I)
      (dentLocalsAfterRefund_get_ilk σ I)
  have hcallFlux' :
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "flux" 0
        (dentFluxArgValsOf evmGuy I) (false, evmFlux, outFlux) true := by
    simpa [evmGuy] using hcallFlux
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evmGuy)
        (evm' := evmFlux) (locals := dentLocalsAfterRefund σ I)
        (receiver := .storage vatRef) (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmGuy.accountMap evmGuy.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        (argVals := dentFluxArgValsOf evmGuy I) (out := outFlux) (perm := true)
        hguardFlux hvat hargsFlux hcallFlux'
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        dentAfterDecreaseFluxTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hfluxBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        .reverted := by
    simpa [locals, evm0, evmGuy] using
      (flipperDentSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller hrefundCode hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperDentSourceBodySuccessAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund evmFlux : EVM.State} {outRefund outFlux : ByteArray}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (dentRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hfluxCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      0 <
        (UInt256.ofNat
          ((evmGuy.lookupAccount
            (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "flux" 0
        (dentFluxArgValsOf evmGuy I) (true, evmFlux, outFlux) true)
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
      (.returned
        { contract := contract, locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
        evmTic none) := by
  intro locals evm0 evmLot evmTic
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (dentId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I)))
      (solcSourceWord evmRefund.executionEnv))
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsAfterRefund_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat (by simpa [evmGuy] using hfluxCode)
  have hargsFlux :
      evalExprs? config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
          .ok (dentFluxArgValsOf evmGuy I) := by
    exact evalExprs_dentFluxArgs_ofLocalsFor
      (evm := evmGuy) (locals := dentLocalsAfterRefund σ I) (I := I)
      (dentLocalsAfterRefund_get_id σ I)
      (dentLocalsAfterRefund_get_lot σ I)
      (dentLocalsAfterRefund_get_bids σ I)
      (dentLocalsAfterRefund_get_ilk σ I)
  have hcallFlux' :
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "flux" 0
        (dentFluxArgValsOf evmGuy I) (true, evmFlux, outFlux) true := by
    simpa [evmGuy] using hcallFlux
  have hdecFlux : config.externalABI.decode? "flux" outFlux = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        (.ok { contract := contract, locals := dentLocalsAfterRefundFlux σ I } evmFlux) := by
    simpa [checkedExternalCallStmts, dentLocalsAfterRefundFlux] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmGuy)
        (evm' := evmFlux) (locals := dentLocalsAfterRefund σ I)
        (receiver := .storage vatRef) (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmGuy.accountMap evmGuy.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        (argVals := dentFluxArgValsOf evmGuy I) (out := outFlux) (perm := true)
        (value := []) hguardFlux hvat hargsFlux hcallFlux' hdecFlux
  have hlotVar :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmFlux (.var "lot") = .ok (.int (Int.ofNat (dentLot I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmFlux) (locals := dentLocalsAfterRefundFlux σ I)
      (name := "lot") (value := dentLot I) (dentLocalsAfterRefundFlux_get_lot σ I)
  have hassignLot :
      assignStorageRef? config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmFlux .storage (bidsF (.var "id") "lot")
        (.int (Int.ofNat (dentLot I).toNat)) =
          .ok ({ contract := contract, locals := dentLocalsAfterRefundFlux σ I }, evmLot) := by
    simpa [evmLot] using
      assign_bidLotStorage evmFlux (dentId I) (dentLot I)
        (dentLocalsAfterRefundFlux_get_id σ I) (dentLocalsAfterRefundFlux_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmLot (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmLot) (locals := dentLocalsAfterRefundFlux σ I)
      (I := I) (dentLocalsAfterRefundFlux_get_ttl σ I)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxOwner)
  have hgeTic :
      evalExpr? config
          { contract := contract,
            locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
          evmLot (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
    exact evalExpr_dentAfterRefundTicNewGeNow_true_from (evm := evmLot)
      (σpre := σ) (σtic := evmLot.accountMap) (I := I)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
      (by simpa [evmLot] using hfitTic)
  have hticVar :
      evalExpr? config
          { contract := contract,
            locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
          evmLot (.var "tic_") =
            .ok (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) := by
    exact evalExpr_dentAfterRefundTicVarWithTicFrom (evm := evmLot)
      (σpre := σ) (σtic := evmLot.accountMap) (I := I)
  let solmTic : Frame :=
    { contract := contract, locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
  have hassignTic :
      assignStorageRef? config
          { contract := contract,
            locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
          evmLot .storage (bidsF (.var "id") "tic")
          (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) =
        .ok (solmTic, evmTic) := by
    simpa [evmTic, solmTic] using
      assign_bidTicStorage evmLot (dentId I) (tendTicNewWord evmLot.accountMap I)
        (tendTicNewWord_bound evmLot.accountMap I)
        (dentLocalsAfterRefundWithTicFrom_get_id σ evmLot.accountMap I)
        (dentLocalsAfterRefundWithTicFrom_get_bids σ evmLot.accountMap I)
  have hpost :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmFlux
        ([ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        (.ok
          { contract := contract,
            locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
          evmTic) := by
    refine ExecBlock.consNormal (ExecStmt.assign hlotVar hassignLot) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hgeTic) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hticVar hassignTic) ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        dentAfterDecreaseFluxTailStmts
        (.ok
          { contract := contract,
            locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
          evmTic) := by
    have hjoined :
        ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
          (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
            [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
              wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
            "_fluxRet" ++
          ([ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
            checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]))
          (.ok
            { contract := contract,
              locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
            evmTic) := by
      exact execBlock_append hfluxBlock hpost
    simpa [dentAfterDecreaseFluxTailStmts, List.append_assoc] using hjoined
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 dentTransition.body
        (.ok
          { contract := contract,
            locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
          evmTic) := by
    simpa [locals, evm0, evmGuy] using
      (flipperDentSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller hrefundCode hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0, evmLot, evmTic] using ExecFuncBody.execBlockOK hblock

theorem flipperDentSourceBodyAdd48OverflowAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund evmFlux : EVM.State} {outRefund outFlux : ByteArray}
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
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (dentRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hfluxCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      0 <
        (UInt256.ofNat
          ((evmGuy.lookupAccount
            (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (dentId I)))
          (solcSourceWord evmRefund.executionEnv))
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "flux" 0
        (dentFluxArgValsOf evmGuy I) (true, evmFlux, outFlux) true)
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
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (dentId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (dentId I)))
      (solcSourceWord evmRefund.executionEnv))
  let evmLot := Solm.EVM.storageStore evmFlux evmFlux.executionEnv.codeOwner
    (bidSlotOfWord (dentId I) ⟨1⟩) (dentLot I)
  have hvat :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (dentLocalsAfterRefund_get_vat σ I)
  have hguardFlux :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat (by simpa [evmGuy] using hfluxCode)
  have hargsFlux :
      evalExprs? config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))] =
          .ok (dentFluxArgValsOf evmGuy I) := by
    exact evalExprs_dentFluxArgs_ofLocalsFor
      (evm := evmGuy) (locals := dentLocalsAfterRefund σ I) (I := I)
      (dentLocalsAfterRefund_get_id σ I)
      (dentLocalsAfterRefund_get_lot σ I)
      (dentLocalsAfterRefund_get_bids σ I)
      (dentLocalsAfterRefund_get_ilk σ I)
  have hcallFlux' :
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "flux" 0
        (dentFluxArgValsOf evmGuy I) (true, evmFlux, outFlux) true := by
    simpa [evmGuy] using hcallFlux
  have hdecFlux : config.externalABI.decode? "flux" outFlux = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hfluxBlock :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "flux" (.intLit 0)
          [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
            wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))]
          "_fluxRet")
        (.ok { contract := contract, locals := dentLocalsAfterRefundFlux σ I } evmFlux) := by
    simpa [checkedExternalCallStmts, dentLocalsAfterRefundFlux] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmGuy)
        (evm' := evmFlux) (locals := dentLocalsAfterRefund σ I)
        (receiver := .storage vatRef) (retVar := "_fluxRet") (name := "flux")
        (target := flipperVatAddress evmGuy.accountMap evmGuy.executionEnv) (sendVal := 0)
        (args := [.storage ilkRef, thisAddr, .storage (bidsF (.var "id") "usr"),
          wrap256 (.binary .sub (.storage (bidsF (.var "id") "lot")) (.var "lot"))])
        (argVals := dentFluxArgValsOf evmGuy I) (out := outFlux) (perm := true)
        (value := []) hguardFlux hvat hargsFlux hcallFlux' hdecFlux
  have hlotVar :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmFlux (.var "lot") = .ok (.int (Int.ofNat (dentLot I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmFlux) (locals := dentLocalsAfterRefundFlux σ I)
      (name := "lot") (value := dentLot I) (dentLocalsAfterRefundFlux_get_lot σ I)
  have hassignLot :
      assignStorageRef? config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmFlux .storage (bidsF (.var "id") "lot")
        (.int (Int.ofNat (dentLot I).toNat)) =
          .ok ({ contract := contract, locals := dentLocalsAfterRefundFlux σ I }, evmLot) := by
    simpa [evmLot] using
      assign_bidLotStorage evmFlux (dentId I) (dentLot I)
        (dentLocalsAfterRefundFlux_get_id σ I) (dentLocalsAfterRefundFlux_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmLot (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmLot.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmLot) (locals := dentLocalsAfterRefundFlux σ I)
      (I := I) (dentLocalsAfterRefundFlux_get_ttl σ I)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxOwner)
  have hgeTicFalse :
      evalExpr? config
          { contract := contract,
            locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I }
          evmLot (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
    have htic := evalExpr_dentAfterRefundTicVarWithTicFrom (evm := evmLot)
      (σpre := σ) (σtic := evmLot.accountMap) (I := I)
    have hnow := evalExpr_tendNow48
      (evm := evmLot)
      (locals := dentLocalsAfterRefundWithTicFrom σ evmLot.accountMap I) (I := I)
      (by simpa [evmLot, storageStore_executionEnv] using hfluxTs)
    have hlt : (tendTicNewWord evmLot.accountMap I).toNat < (tendNow48 I).toNat :=
      tendTicNewWord_lt_now48_overflow (by simpa [evmLot] using hoverTic)
    exact evalExpr_ge_uint256_false htic hnow hlt
  have hpost :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefundFlux σ I }
        evmFlux
        ([ .assign .storage (bidsF (.var "id") "lot") (.var "lot") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.assign hlotVar hassignLot) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hgeTicFalse)
  have htail :
      ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
        dentAfterDecreaseFluxTailStmts .reverted := by
    have hjoined :
        ExecBlock config { contract := contract, locals := dentLocalsAfterRefund σ I } evmGuy
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
    simpa [locals, evm0, evmGuy] using
      (flipperDentSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund)
        hwv hguy hticGuard hendGuard hbidGuard htabGuard hlotGuard hfitLot hfitBeg
        hdec hcaller hrefundCode hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.Flipper
