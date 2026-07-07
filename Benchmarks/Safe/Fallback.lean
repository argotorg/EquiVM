import Benchmarks.Safe.Routines
import Reasoning.ExternalCall

/-! # Safe fallback refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Safe

theorem safeFallbackSelectorDispatchNone {I : ExecutionEnv}
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false) :
    selectorDispatchMsg contract I.calldata = none := by
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  apply dispatchList_none_of_all_ne
  intro t ht
  change t ∈ transitions at ht
  simp [transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, safeVersionSelectorBytes]; exact hnm 0 (by decide)
  · rw [selectorOf, safeAddOwnerWithThresholdSelectorBytes]; exact hnm 1 (by decide)
  · rw [selectorOf, safeApproveHashSelectorBytes]; exact hnm 2 (by decide)
  · rw [selectorOf, safeApprovedHashesSelectorBytes]; exact hnm 3 (by decide)
  · rw [selectorOf, safeChangeThresholdSelectorBytes]; exact hnm 4 (by decide)
  · rw [selectorOf, safeCheckNSignaturesSelectorBytes]; exact hnm 5 (by decide)
  · rw [selectorOf, safeCheckNSignaturesWithExecutorSelectorBytes]; exact hnm 6 (by decide)
  · rw [selectorOf, safeCheckSignaturesSelectorBytes]; exact hnm 7 (by decide)
  · rw [selectorOf, safeCheckSignaturesWithExecutorSelectorBytes]; exact hnm 8 (by decide)
  · rw [selectorOf, safeDisableModuleSelectorBytes]; exact hnm 9 (by decide)
  · rw [selectorOf, safeDomainSeparatorSelectorBytes]; exact hnm 10 (by decide)
  · rw [selectorOf, safeEnableModuleSelectorBytes]; exact hnm 11 (by decide)
  · rw [selectorOf, safeExecTransactionSelectorBytes]; exact hnm 12 (by decide)
  · rw [selectorOf, safeExecTransactionFromModuleSelectorBytes]; exact hnm 13 (by decide)
  · rw [selectorOf, safeExecTransactionFromModuleReturnDataSelectorBytes]; exact hnm 14 (by decide)
  · rw [selectorOf, safeGetModulesPaginatedSelectorBytes]; exact hnm 15 (by decide)
  · rw [selectorOf, safeGetOwnersSelectorBytes]; exact hnm 16 (by decide)
  · rw [selectorOf, safeGetStorageAtSelectorBytes]; exact hnm 17 (by decide)
  · rw [selectorOf, safeGetThresholdSelectorBytes]; exact hnm 18 (by decide)
  · rw [selectorOf, safeGetTransactionHashSelectorBytes]; exact hnm 19 (by decide)
  · rw [selectorOf, safeIsModuleEnabledSelectorBytes]; exact hnm 20 (by decide)
  · rw [selectorOf, safeIsOwnerSelectorBytes]; exact hnm 21 (by decide)
  · rw [selectorOf, safeNonceSelectorBytes]; exact hnm 22 (by decide)
  · rw [selectorOf, safeRemoveOwnerSelectorBytes]; exact hnm 23 (by decide)
  · rw [selectorOf, safeSetFallbackHandlerSelectorBytes]; exact hnm 24 (by decide)
  · rw [selectorOf, safeSetGuardSelectorBytes]; exact hnm 25 (by decide)
  · rw [selectorOf, safeSetModuleGuardSelectorBytes]; exact hnm 26 (by decide)
  · rw [selectorOf, safeSetupSelectorBytes]; exact hnm 27 (by decide)
  · rw [selectorOf, safeSignedMessagesSelectorBytes]; exact hnm 28 (by decide)
  · rw [selectorOf, safeSimulateAndRevertSelectorBytes]; exact hnm 29 (by decide)
  · rw [selectorOf, safeSwapOwnerSelectorBytes]; exact hnm 30 (by decide)

theorem safeFallbackReceiveDispatchNone {I : ExecutionEnv}
    (hcalldata : I.calldata.size ≠ 0) :
    receiveDispatchMsg contract I.calldata = none := by
  simp [receiveDispatchMsg, hcalldata]

theorem safeFallbackCallargs {I : ExecutionEnv} :
    fallbackCallargs I.calldata fallbackTransition.params =
      some ((∅ : Store).insert "calldata" (.bytes I.calldata)) := by
  rfl

theorem safeFallbackReturnConvention :
    fallbackReturnConvention fallbackTransition = some .rawBytes := by
  rfl

abbrev safeFallbackCallargsStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "calldata" (.bytes I.calldata)

abbrev safeFallbackHandlerWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner fallbackHandlerSlot

abbrev safeFallbackHandlerSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I fallbackHandlerSlot

abbrev safeFallbackAfterWordStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (safeFallbackCallargsStore I).insert "handlerWord"
    (.int (Int.ofNat (safeFallbackHandlerWord evm).toNat))

abbrev safeFallbackAfterHandlerStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (safeFallbackAfterWordStore evm I).insert "handler"
    (.address (AccountAddress.ofNat (safeFallbackHandlerWord evm).toNat))

abbrev safeFallbackSenderPacked (I : ExecutionEnv) : ByteArray :=
  ByteArray.mk ((EVM.word I.source).toBytesBE.drop 12 |>.toArray)

abbrev safeFallbackPackedCalldata (I : ExecutionEnv) : ByteArray :=
  ByteArray.mk ((I.calldata.toList ++ (EVM.word I.source).toBytesBE.drop 12).toArray)

theorem byteArray_readWithPadding_huge (b : ByteArray) (addr len : ℕ)
    (h : 2 ^ 64 ≤ len) :
    b.readWithPadding addr len = ByteArray.empty := by
  unfold ByteArray.readWithPadding
  rw [if_pos h]
  rfl

theorem safeFallbackSenderPackedList_length (I : ExecutionEnv) :
    ((EVM.word I.source).toBytesBE.drop 12).length = 20 := by
  have hlen32 : (EVM.Word.toBytesBE (EVM.word I.source)).length = 32 := by
    have h := word_toBytesBE_toByteArray_size (EVM.word I.source)
    simpa [list_toByteArray_size] using h
  rw [List.length_drop, hlen32]

theorem safeFallbackPackedCalldata_size (I : ExecutionEnv) :
    (safeFallbackPackedCalldata I).size = I.calldata.size + 20 := by
  unfold safeFallbackPackedCalldata
  change (I.calldata.toList ++ (EVM.word I.source).toBytesBE.drop 12).toArray.size =
    I.calldata.size + 20
  rw [List.size_toArray, List.length_append, safeFallbackSenderPackedList_length I]
  rw [byteArray_toList_eq, Array.length_toList]
  rfl

theorem safeFallbackPackedCalldata_ne_empty (I : ExecutionEnv) :
    safeFallbackPackedCalldata I ≠ ByteArray.empty := by
  intro h
  have hsize := congrArg ByteArray.size h
  rw [safeFallbackPackedCalldata_size] at hsize
  simp at hsize

abbrev safeFallbackAfterCallStore (evm : EVM.State) (I : ExecutionEnv)
    (ok : Bool) (out : ByteArray) : Store :=
  ((safeFallbackAfterHandlerStore evm I).insert "handlerSuccess" (.bool ok)).insert
    "handlerReturn" (.bytes out)

theorem safeFallbackEvalHandlerWord (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := safeFallbackCallargsStore I } evm
      (.storage fallbackHandlerRawRef) =
    .ok (.int (Int.ofNat (safeFallbackHandlerWord evm).toNat)) := by
  let er : EvaledStorageRef :=
    { base := "_rawStorage",
      steps := [.mindex (.int (Int.ofNat fallbackHandlerSlot.toNat))] }
  have hbase :
      (safeFallbackCallargsStore I).get? fallbackHandlerRawRef.base = none := by
    simp [safeFallbackCallargsStore, fallbackHandlerRawRef, rawStorageRef]
  have her :
      evalStorageRef config { contract := contract, locals := safeFallbackCallargsStore I } evm
        fallbackHandlerRawRef = .ok er := by
    simp [er, fallbackHandlerRawRef, rawStorageRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, valueToKey?,
      config]
  have hty : storageTypeAt? contract.storage er = some uint256St := by
    simp [er, storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St, uint256Int]
  have hloc :
      config.storage.layout er = fun _ => some (wordLoc fallbackHandlerSlot (.int uint256Int)) := by
    funext evm'
    simp [er, config, storageLayout, solidityStorageLayout, storageLayoutRaw]
    change wordLoc (keyValueToWord (.int (Int.ofNat fallbackHandlerSlot.toNat)))
        (.int uint256Int) = wordLoc fallbackHandlerSlot (.int uint256Int)
    rw [keyValueToWord_uint256 fallbackHandlerSlot]
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (safeStorageLocLoad_uint256 evm fallbackHandlerSlot)

theorem safeFallbackAfterWordStore_get_handlerWord (evm : EVM.State) (I : ExecutionEnv) :
    (safeFallbackAfterWordStore evm I).get? "handlerWord" =
      some (.int (Int.ofNat (safeFallbackHandlerWord evm).toNat)) := by
  rw [safeFallbackAfterWordStore]
  exact store_get_self _ _ _

theorem safeFallbackAfterWordStore_index_handlerWord (evm : EVM.State) (I : ExecutionEnv) :
    (safeFallbackAfterWordStore evm I)["handlerWord"] =
      .int (Int.ofNat (safeFallbackHandlerWord evm).toNat) := by
  unfold safeFallbackAfterWordStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem safeFallbackAfterHandlerStore_get_handlerWord (evm : EVM.State) (I : ExecutionEnv) :
    (safeFallbackAfterHandlerStore evm I).get? "handlerWord" =
      some (.int (Int.ofNat (safeFallbackHandlerWord evm).toNat)) := by
  rw [safeFallbackAfterHandlerStore]
  rw [store_get_ne _ _ (by decide)]
  exact safeFallbackAfterWordStore_get_handlerWord evm I

theorem safeFallbackAfterHandlerStore_index_handlerWord (evm : EVM.State) (I : ExecutionEnv) :
    (safeFallbackAfterHandlerStore evm I)["handlerWord"] =
      .int (Int.ofNat (safeFallbackHandlerWord evm).toNat) := by
  unfold safeFallbackAfterHandlerStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem safeFallbackAfterHandlerStore_get_handler (evm : EVM.State) (I : ExecutionEnv) :
    (safeFallbackAfterHandlerStore evm I).get? "handler" =
      some (.address (AccountAddress.ofNat (safeFallbackHandlerWord evm).toNat)) := by
  rw [safeFallbackAfterHandlerStore]
  exact store_get_self _ _ _

theorem safeFallbackAfterHandlerStore_index_handler (evm : EVM.State) (I : ExecutionEnv) :
    (safeFallbackAfterHandlerStore evm I)["handler"] =
      .address (AccountAddress.ofNat (safeFallbackHandlerWord evm).toNat) := by
  unfold safeFallbackAfterHandlerStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem safeFallbackAfterCallStore_get_success (evm : EVM.State) (I : ExecutionEnv)
    (ok : Bool) (out : ByteArray) :
    (safeFallbackAfterCallStore evm I ok out).get? "handlerSuccess" = some (.bool ok) := by
  rw [safeFallbackAfterCallStore]
  rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem safeFallbackAfterCallStore_get_return (evm : EVM.State) (I : ExecutionEnv)
    (ok : Bool) (out : ByteArray) :
    (safeFallbackAfterCallStore evm I ok out).get? "handlerReturn" = some (.bytes out) := by
  rw [safeFallbackAfterCallStore]
  exact store_get_self _ _ _

theorem safeFallbackAfterHandlerStore_get_calldata (evm : EVM.State) (I : ExecutionEnv) :
    (safeFallbackAfterHandlerStore evm I).get? "calldata" = some (.bytes I.calldata) := by
  rw [safeFallbackAfterHandlerStore]
  rw [store_get_ne _ _ (by decide)]
  rw [safeFallbackAfterWordStore]
  rw [store_get_ne _ _ (by decide)]
  rw [safeFallbackCallargsStore]
  exact store_get_self _ _ _

theorem safeFallbackEvalHandlerCast (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := safeFallbackAfterWordStore evm I } evm
      (.cast (.var "handlerWord") addrSt) =
    .ok (.address (AccountAddress.ofNat (safeFallbackHandlerWord evm).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := safeFallbackAfterWordStore evm I } evm
          (.var "handlerWord") =
        .ok (.int (Int.ofNat (safeFallbackHandlerWord evm).toNat)) := by
    simp [evalExpr?, safeFallbackAfterWordStore, EvalResult.ofOption]
  have hnonneg : ¬ Int.ofNat (safeFallbackHandlerWord evm).toNat < 0 :=
    not_lt_of_ge (Int.natCast_nonneg _)
  rw [evalExpr?]
  rw [hvar]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, castValue?, addrSt]
  rw [if_neg hnonneg]
  rfl

theorem safeFallbackEvalHandlerWordEqZero_true (evm : EVM.State) (I : ExecutionEnv)
    (hzero : safeFallbackHandlerWord evm = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
      (eqE (.var "handlerWord") (.intLit 0)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
          (.var "handlerWord") =
        .ok (.int (Int.ofNat (safeFallbackHandlerWord evm).toNat)) := by
    simp [evalExpr?, Std.HashMap.get?_eq_getElem?, safeFallbackAfterHandlerStore_index_handlerWord,
      EvalResult.ofOption]
  unfold eqE
  rw [evalExpr?] <;> first | (intro h; cases h) | skip
  rw [hvar]
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, hzero]

theorem safeFallbackEvalHandlerWordEqZero_false (evm : EVM.State) (I : ExecutionEnv)
    (hnonzero : safeFallbackHandlerWord evm ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
      (eqE (.var "handlerWord") (.intLit 0)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
          (.var "handlerWord") =
        .ok (.int (Int.ofNat (safeFallbackHandlerWord evm).toNat)) := by
    simp [evalExpr?, Std.HashMap.get?_eq_getElem?, safeFallbackAfterHandlerStore_index_handlerWord,
      EvalResult.ofOption]
  have htoNat : (safeFallbackHandlerWord evm).toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  unfold eqE
  rw [evalExpr?] <;> first | (intro h; cases h) | skip
  rw [hvar]
  simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?, htoNat]

theorem safeFallbackEvalHandlerVar (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
      (.var "handler") =
    .ok (.address (AccountAddress.ofNat (safeFallbackHandlerWord evm).toNat)) := by
  rw [evalExpr?]
  rw [safeFallbackAfterHandlerStore_get_handler]
  rfl

theorem safeFallbackEvalZeroValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
      (.intLit 0) = .ok (.int 0) := by
  simp [evalExpr?, pure]

theorem safeFallbackEvalPackedCalldata (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
      (.abiEncodePacked [(bytesTy, .var "calldata"), (addr, sender)]) =
    .ok (.bytes (safeFallbackPackedCalldata I)) := by
  have hcalldata :
      evalExpr? config { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
        (.var "calldata") = .ok (.bytes I.calldata) := by
    rw [evalExpr?]
    rw [safeFallbackAfterHandlerStore_get_calldata]
    rfl
  unfold safeFallbackPackedCalldata
  rw [evalExpr?]
  simp [evalPackedArgs?, hcalldata, encodePackedValue?, bytesTy, addr, sender, evalExpr?,
    envValue, hsource, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem safeFallbackEvalSuccessVar (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
  evalExpr? config
    { contract := contract, locals := safeFallbackAfterCallStore evm I true out } evm
    (.var "handlerSuccess") = .ok (.bool true) := by
  rw [evalExpr?]
  rw [safeFallbackAfterCallStore_get_success]
  rfl

theorem safeFallbackEvalSuccessVarAt (storeEvm evalEvm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
  evalExpr? config
    { contract := contract, locals := safeFallbackAfterCallStore storeEvm I true out } evalEvm
    (.var "handlerSuccess") = .ok (.bool true) := by
  rw [evalExpr?]
  rw [safeFallbackAfterCallStore_get_success]
  rfl

theorem safeFallbackEvalFailureVar (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
  evalExpr? config
    { contract := contract, locals := safeFallbackAfterCallStore evm I false out } evm
    (.var "handlerSuccess") = .ok (.bool false) := by
  rw [evalExpr?]
  rw [safeFallbackAfterCallStore_get_success]
  rfl

theorem safeFallbackEvalFailureVarAt (storeEvm evalEvm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
  evalExpr? config
    { contract := contract, locals := safeFallbackAfterCallStore storeEvm I false out } evalEvm
    (.var "handlerSuccess") = .ok (.bool false) := by
  rw [evalExpr?]
  rw [safeFallbackAfterCallStore_get_success]
  rfl

theorem safeFallbackEvalReturnVar (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
  evalExpr? config
    { contract := contract, locals := safeFallbackAfterCallStore evm I true out } evm
    (.var "handlerReturn") = .ok (.bytes out) := by
  rw [evalExpr?]
  rw [safeFallbackAfterCallStore_get_return]
  rfl

theorem safeFallbackEvalReturnVarAt (storeEvm evalEvm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
  evalExpr? config
    { contract := contract, locals := safeFallbackAfterCallStore storeEvm I true out } evalEvm
    (.var "handlerReturn") = .ok (.bytes out) := by
  rw [evalExpr?]
  rw [safeFallbackAfterCallStore_get_return]
  rfl

theorem safeFallbackGuardReverts {cA gh bl σ σ₀ A I} {g : Sat256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray} {aw : UInt256}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩ R mem aw rdata
      (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hov : R.length + 3 ≤ 1024) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcond : UInt256.isZero I.weiValue = ⟨0⟩ := isZero_eq_zero_of_ne hwv
  have hfall := h.jumpdest (by native_decide) (by omega)
    |>.callvalue (by native_decide) (by simp; omega)
    |>.dup1 (by native_decide) (by simp; omega)
    |>.iszero (by native_decide) (by simp; omega)
    |>.push2 ⟨546⟩ (by native_decide) (by simp; omega)
    |>.jumpiNT (by native_decide) hcond (by simp; omega)
  exact RD.revertStub hfall (by native_decide) (by native_decide) (by native_decide)
    (by simp; omega)

theorem safeFallbackHandlerZeroStops {cA gh bl σ σ₀ A I} {g : Sat256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray} {aw : UInt256}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩ R mem aw rdata
      (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩)
    (hzero : safeFallbackHandlerSlotWord σ I = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) ByteArray.empty := by
  have hcond : UInt256.isZero I.weiValue ≠ ⟨0⟩ := by rw [hwv]; decide
  have h546 := h.jumpdest (by native_decide) (by omega)
    |>.callvalue (by native_decide) (by simp; omega)
    |>.dup1 (by native_decide) (by simp; omega)
    |>.iszero (by native_decide) (by simp; omega)
    |>.push2 ⟨546⟩ (by native_decide) (by simp; omega)
    |>.jumpiT (by native_decide) hcond (by native_decide) (by simp; omega)
  have h581 := h546.jumpdest (by native_decide) (by simp; omega)
    |>.pop (by native_decide) (by omega)
    |>.pushConst fallbackHandlerSlot (op := .PUSH32) (width := 32) (by decide)
      (by native_decide) (by simp; omega)
  obtain ⟨k582, C582, h582⟩ := h581.sload (by native_decide) (by simp; omega)
  have h582' : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨582⟩
      (safeFallbackHandlerSlotWord σ I :: R) mem aw rdata (cA, σ) k582 C582 := by
    simpa [safeFallbackHandlerSlotWord, solcSlotWord,
      show ({ val := 546 } + { val := 1 } + { val := 1 } +
          UInt256.ofNat (Nat.succ 32) + { val := 1 }) = (⟨582⟩ : UInt256) by
        native_decide] using h582
  rw [hzero] at h582'
  have h587 := h582'.dup1 (by native_decide) (by simp; omega)
    |>.push2 ⟨588⟩ (by native_decide) (by simp; omega)
    |>.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
      (by simp; omega)
  exact h587.stop (by native_decide) (by simp; omega)

theorem safeFallbackBodyReverts_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeFallbackCallargsStore I) fallbackTransition.body .reverted := by
  simpa [fallbackTransition, nonpayable, initState] using
    bodyReverts_nonPayable (cfg := config) (contract := contract)
      (evm := initState cA gh bl σ σ₀ g A I)
      (locals := safeFallbackCallargsStore I)
      (rest :=
        [ .letDecl "handlerWord" (some uint256) (.storage fallbackHandlerRawRef),
          .letDecl "handler" (some addr) (.cast (.var "handlerWord") addrSt),
          .ite (eqE (.var "handlerWord") (.intLit 0))
            [ .return [emptyBytes] ]
            [ .lowLevelCall (.var "handler") (.intLit 0)
                (.abiEncodePacked [(bytesTy, .var "calldata"), (addr, sender)])
                "handlerSuccess" "handlerReturn",
              .require (.var "handlerSuccess"),
              .return [.var "handlerReturn"] ] ])
      (by simpa [initState] using hwv)

theorem safeFallbackBodyReturns_zero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : safeFallbackHandlerWord evm = ⟨0⟩) :
    ExecTransitionBody config contract evm (safeFallbackCallargsStore I) fallbackTransition.body
      (.returned { contract := contract, locals := safeFallbackAfterHandlerStore evm I } evm
        (some [.bytes ByteArray.empty])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [fallbackTransition, nonpayable, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (safeFallbackEvalHandlerWord evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (safeFallbackEvalHandlerCast evm I)) ?_
  refine ExecBlock.consReturn ?_
  refine ExecStmt.iteTrue (safeFallbackEvalHandlerWordEqZero_true evm I hzero) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (by simp [emptyBytes, evalExpr?, pure])))

theorem safeFallbackBodyReturns_callSuccess (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : safeFallbackHandlerWord evm ≠ ⟨0⟩)
    (hsource : evm.executionEnv.source = I.source)
    (hcall : callViaEVM evm
      (EVM.address (AccountAddress.ofNat (safeFallbackHandlerWord evm).toNat))
      0 (safeFallbackPackedCalldata I) (true, evm', out)) :
    ExecTransitionBody config contract evm (safeFallbackCallargsStore I) fallbackTransition.body
      (.returned { contract := contract, locals := safeFallbackAfterCallStore evm I true out }
        evm' (some [.bytes out])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [fallbackTransition, nonpayable, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (safeFallbackEvalHandlerWord evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (safeFallbackEvalHandlerCast evm I)) ?_
  refine ExecBlock.consReturn ?_
  refine ExecStmt.iteFalse (safeFallbackEvalHandlerWordEqZero_false evm I hnonzero) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (safeFallbackEvalHandlerVar evm I)
      (safeFallbackEvalZeroValue evm I)
      (safeFallbackEvalPackedCalldata evm I hsource)
      hcall) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (safeFallbackEvalSuccessVarAt evm evm' I out)) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (safeFallbackEvalReturnVarAt evm evm' I out)))

theorem safeFallbackBodyReverts_callFailure (evm evm' : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : safeFallbackHandlerWord evm ≠ ⟨0⟩)
    (hsource : evm.executionEnv.source = I.source)
    (hcall : callViaEVM evm
      (EVM.address (AccountAddress.ofNat (safeFallbackHandlerWord evm).toNat))
      0 (safeFallbackPackedCalldata I) (false, evm', out)) :
    ExecTransitionBody config contract evm (safeFallbackCallargsStore I) fallbackTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [fallbackTransition, nonpayable, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (safeFallbackEvalHandlerWord evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (safeFallbackEvalHandlerCast evm I)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteFalse (safeFallbackEvalHandlerWordEqZero_false evm I hnonzero) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (safeFallbackEvalHandlerVar evm I)
      (safeFallbackEvalZeroValue evm I)
      (safeFallbackEvalPackedCalldata evm I hsource)
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (safeFallbackEvalFailureVarAt evm evm' I out))

theorem safeFallbackCallFailureTail {cA gh bl σ σ₀ A I} {g : Sat256}
    {R : List UInt256} {mem : ByteArray} {aw fp hw : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨615⟩
      (⟨0⟩ :: fp :: hw :: R) mem aw ByteArray.empty (cA, σ) k C)
    (hov : R.length + 5 ≤ 1024) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h617 := h.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  have h620 := h617.returndatasize (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
  have hmemout :
      ByteArray.empty.write 0 mem fp.toNat (UInt256.ofNat ByteArray.empty.size).toNat = mem := by
    simpa using byteArray_write_len_zero ByteArray.empty mem 0 fp.toNat
  have hawout :
      UInt256.ofNat
          (MachineState.M aw.toNat fp.toNat (UInt256.ofNat ByteArray.empty.size).toNat) = aw := by
    rw [show (UInt256.ofNat ByteArray.empty.size).toNat = 0 by native_decide]
    simpa [MachineState.M] using u256_ofNat_toNat aw
  have h621 := h620.returndatacopy 0 mem aw (by native_decide) (by decide)
    (fun s haws hstks => by
      set_option linter.unusedSimpArgs false in
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [hawout]
      simp)
    hmemout hawout (by evm_ov)
  have h626 := h621.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨629⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have h628 := h626.returndatasize (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  exact h628.rev 0 (by native_decide)
    (fun s haws hstks => by
      set_option linter.unusedSimpArgs false in
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [hawout]
      simp)
    (by evm_ov)

theorem safeFallbackDepthLimitReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {R : List UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨535⟩ R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩)
    (hnonzero : safeFallbackHandlerSlotWord σ I ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 9 ≤ 1024) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hcond : UInt256.isZero I.weiValue ≠ ⟨0⟩ := by rw [hwv]; decide
  have h546 := h.jumpdest (by native_decide) (by omega)
    |>.callvalue (by native_decide) (by simp; omega)
    |>.dup1 (by native_decide) (by simp; omega)
    |>.iszero (by native_decide) (by simp; omega)
    |>.push2 ⟨546⟩ (by native_decide) (by simp; omega)
    |>.jumpiT (by native_decide) hcond (by native_decide) (by simp; omega)
  have h581 := h546.jumpdest (by native_decide) (by simp; omega)
    |>.pop (by native_decide) (by omega)
    |>.pushConst fallbackHandlerSlot (op := .PUSH32) (width := 32) (by decide)
      (by native_decide) (by simp; omega)
  obtain ⟨k582, C582, h582⟩ := h581.sload (by native_decide) (by simp; omega)
  have h582' : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨582⟩
      (safeFallbackHandlerSlotWord σ I :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k582 C582 := by
    simpa [safeFallbackHandlerSlotWord, solcSlotWord,
      show ({ val := 546 } + { val := 1 } + { val := 1 } +
          UInt256.ofNat (Nat.succ 32) + { val := 1 }) = (⟨582⟩ : UInt256) by
        native_decide] using h582
  have h588 := h582'.dup1 (by native_decide) (by simp; omega)
    |>.push2 ⟨588⟩ (by native_decide) (by simp; omega)
    |>.jumpiT (by native_decide) hnonzero (by native_decide) (by simp; omega)
  have h591 := h588.jumpdest (by native_decide) (by simp; omega)
    |>.push1 ⟨64⟩ (by native_decide) (by simp; omega)
  have h592 := h591.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost solcFreePtrMem_mload64 (by native_decide) (by simp; omega)
  have h595 := h592.calldatasize (by native_decide) (by simp; omega)
    |>.push0 (by native_decide) (by simp; omega)
    |>.dup3 (by native_decide) (by simp; omega)
  let memCd : ByteArray :=
    I.calldata.write 0 solcFreePtrMem (⟨128⟩ : UInt256).toNat
      (UInt256.ofNat I.calldata.size).toNat
  let awCd : UInt256 :=
    UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
      (UInt256.ofNat I.calldata.size).toNat)
  have h596 := h595.calldatacopy (Cₘ awCd - Cₘ (UInt256.ofNat 3)) memCd awCd
    (by native_decide)
    (fun s haws hstks => by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        List.getElem!_cons_zero, List.getElem!_cons_succ, awCd])
    (by rfl) (by rfl) (by simp; omega)
  have h603pre := h596.caller (by native_decide) (by simp; omega)
    |>.push1 ⟨96⟩ (by native_decide) (by simp; omega)
    |>.shl (by native_decide) (by simp; omega)
    |>.calldatasize (by native_decide) (by simp; omega)
    |>.dup3 (by native_decide) (by simp; omega)
    |>.add (by native_decide) (by simp; omega)
  let senderShifted : UInt256 := UInt256.shiftLeft (UInt256.ofNat I.source.val) ⟨96⟩
  let memCall : ByteArray :=
    senderShifted.toByteArray.write 0 memCd
      ((⟨128⟩ : UInt256) + UInt256.ofNat I.calldata.size).toNat 32
  let awCall : UInt256 :=
    UInt256.ofNat (MachineState.M awCd.toNat
      ((⟨128⟩ : UInt256) + UInt256.ofNat I.calldata.size).toNat 32)
  have h604 := h603pre.mstore (Cₘ awCall - Cₘ awCd) memCall awCall
    (by native_decide)
    (fun s haws hstks => by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        List.getElem!_cons_zero, awCall])
    (by rfl) (by rfl) (by simp; omega)
  have h613 := h604.push0 (by native_decide) (by simp; omega)
    |>.push0 (by native_decide) (by simp; omega)
    |>.push1 ⟨20⟩ (by native_decide) (by simp; omega)
    |>.calldatasize (by native_decide) (by simp; omega)
    |>.add (by native_decide) (by simp; omega)
    |>.dup4 (by native_decide) (by simp; omega)
    |>.push0 (by native_decide) (by simp; omega)
    |>.dup7 (by native_decide) (by simp; omega)
  obtain ⟨gasArg, h614⟩ := h613.gas (by native_decide) (by simp; omega)
  obtain ⟨_, _, h615⟩ := RD.callDepthLimit h614 (by native_decide) hdepth
    (by simp; omega)
  exact safeFallbackCallFailureTail h615 (by omega)

theorem safeReEquivFallbackRev {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode)
    (hrev : RDrev safeBytecode g (initState cA gh bl σ_evm σ₀ g A I))
    (hsel : selectorDispatchMsg contract I.calldata = none)
    (hreceive : receiveDispatchMsg contract I.calldata = none)
    (hbody : ExecTransitionBody config contract
      (initState cA gh bl σ_solm σ₀ g A I) (safeFallbackCallargsStore I)
      fallbackTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  refine RDrev.reEquivElim (cfg := config) (contract := contract) hcode hrev ?_
  intro g' o hxi
  exact reEquiv_fallbackExecution hsel hreceive rfl safeFallbackCallargs
    safeFallbackReturnConvention
    (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody)
    (execResultsEquiv.revert hxi rfl)

theorem safeReEquivFallbackRet {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {o : ByteArray} {cs : Frame} {evm'' : EVM.State} {retVal}
    (hcode : I.code = safeBytecode)
    (hret : RDret safeBytecode g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (hsel : selectorDispatchMsg contract I.calldata = none)
    (hreceive : receiveDispatchMsg contract I.calldata = none)
    (hbody : ExecTransitionBody config contract
      (initState cA gh bl σ_solm σ₀ g A I) (safeFallbackCallargsStore I)
      fallbackTransition.body (.returned cs evm'' retVal))
    (hCreated : cA = evm''.createdAccounts)
    (hAccounts : accountMapEquiv σ_evm evm''.accountMap)
    (hretData : returnDataEquiv o retVal .rawBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  refine RDret.reEquivElim (cfg := config) (contract := contract) hcode hret ?_
  intro g' A' hxi
  exact reEquiv_fallbackExecution hsel hreceive rfl safeFallbackCallargs
    safeFallbackReturnConvention
    (by simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody)
    (execResultsEquiv.success hxi rfl hCreated hAccounts hretData)

theorem safeFallbackBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hcalldata : I.calldata.size ≠ 0)
    (hnm : ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel : selectorDispatchMsg contract I.calldata = none :=
    safeFallbackSelectorDispatchNone hnm
  have hreceive : receiveDispatchMsg contract I.calldata = none :=
    safeFallbackReceiveDispatchNone hcalldata
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hslotEq :
        safeFallbackHandlerSlotWord σ_evm I = safeFallbackHandlerSlotWord σ_solm I := by
      simpa [safeFallbackHandlerSlotWord, solcSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner fallbackHandlerSlot ⟨0⟩
    by_cases hword0 : safeFallbackHandlerSlotWord σ_evm I = ⟨0⟩
    · have hword0Solm : safeFallbackHandlerSlotWord σ_solm I = ⟨0⟩ := by
        rw [← hslotEq]
        exact hword0
      have hzeroSolm :
          safeFallbackHandlerWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) = ⟨0⟩ := by
        simpa [safeFallbackHandlerWord, safeFallbackHandlerSlotWord, solcSlotWord, initState,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hword0Solm
      have hbody := safeFallbackBodyReturns_zero
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simpa [initState] using hwv) hzeroSolm
      by_cases hsz4 : 4 ≤ I.calldata.size
      · obtain ⟨_, _, h535⟩ := safeReachFallbackNoMatch
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hnm
        have hret := safeFallbackHandlerZeroStops h535 hwv hword0 (by simp)
        exact safeReEquivFallbackRet hcode hret hsel hreceive hbody
          (by simp [initState]) (by simpa [initState] using hAccounts)
          (returnDataEquiv.rawBytes rfl)
      · have hshort : I.calldata.size < 4 := by omega
        obtain ⟨_, _, h535⟩ := safeReachFallbackShort
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (I := I) (g := Sat256.ofUInt256 g) hcode hshort hcalldata
        have hret := safeFallbackHandlerZeroStops h535 hwv hword0 (by simp)
        exact safeReEquivFallbackRet hcode hret hsel hreceive hbody
          (by simp [initState]) (by simpa [initState] using hAccounts)
          (returnDataEquiv.rawBytes rfl)
    · by_cases hdepth : I.depth = 1024
      · let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hnonzeroSolm : safeFallbackHandlerSlotWord σ_solm I ≠ ⟨0⟩ := by
          intro hz
          apply hword0
          rw [hslotEq]
          exact hz
        have hnonzeroSolmWord : safeFallbackHandlerWord evmSolm ≠ ⟨0⟩ := by
          simpa [evmSolm, safeFallbackHandlerWord, safeFallbackHandlerSlotWord,
            solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage] using hnonzeroSolm
        let target := EVM.address (AccountAddress.ofNat (safeFallbackHandlerWord evmSolm).toNat)
        have hcallSolm : callViaEVM evmSolm target 0 (safeFallbackPackedCalldata I)
            (false,
              { evmSolm with substate := (evmSolm.addAccessedAccount target).substate },
              ByteArray.empty) := by
          apply callViaEVM.callNotMade (perm := true) rfl rfl
          rintro ⟨_, hne⟩
          exact hne (by simpa [evmSolm, initState] using hdepth)
        have hbody := safeFallbackBodyReverts_callFailure evmSolm
          { evmSolm with substate := (evmSolm.addAccessedAccount target).substate } I
          ByteArray.empty (by simpa [evmSolm, initState] using hwv)
          hnonzeroSolmWord (by simp [evmSolm, initState]) (by simpa [target] using hcallSolm)
        by_cases hsz4 : 4 ≤ I.calldata.size
        · obtain ⟨_, _, h535⟩ := safeReachFallbackNoMatch
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hnm
          have hrev := safeFallbackDepthLimitReverts h535 hwv hword0 hdepth (by simp)
          exact safeReEquivFallbackRev hcode hrev hsel hreceive hbody
        · have hshort : I.calldata.size < 4 := by omega
          obtain ⟨_, _, h535⟩ := safeReachFallbackShort
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) hcode hshort hcalldata
          have hrev := safeFallbackDepthLimitReverts h535 hwv hword0 hdepth (by simp)
          exact safeReEquivFallbackRev hcode hrev hsel hreceive hbody
      · sorry
  · by_cases hsz4 : 4 ≤ I.calldata.size
    · obtain ⟨_, _, h535⟩ := safeReachFallbackNoMatch
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hnm
      have hrev := safeFallbackGuardReverts h535 hwv (by simp)
      exact safeReEquivFallbackRev hcode hrev hsel hreceive
        (safeFallbackBodyReverts_nonpayable (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv)
    · have hshort : I.calldata.size < 4 := by omega
      obtain ⟨_, _, h535⟩ := safeReachFallbackShort
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hcode hshort hcalldata
      have hrev := safeFallbackGuardReverts h535 hwv (by simp)
      exact safeReEquivFallbackRev hcode hrev hsel hreceive
        (safeFallbackBodyReverts_nonpayable (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv)

end Benchmarks.Safe
