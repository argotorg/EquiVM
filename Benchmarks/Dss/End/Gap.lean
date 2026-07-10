import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `gap(bytes32)` mapping getter -/

abbrev endGapConcreteSelector : ByteArray := selectorBytes 0xe6 0xee 0x62 0xaa
abbrev endGapEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gap", steps := [.mindex (endBytes32ArgKey I)] }
abbrev endGapSlotFor (I : ExecutionEnv) : UInt256 :=
  gapSlot (endBytes32ArgKey I)

abbrev endGapHighSplitPc : UInt256 := ⟨43⟩
abbrev endGapHigh2SplitPc : UInt256 := ⟨54⟩
abbrev endGapFirstArmPc : UInt256 := ⟨65⟩
abbrev endGapEntryPc : UInt256 := ⟨1216⟩
abbrev endGapDecodedPc : UInt256 := ⟨1238⟩
abbrev endGapRoutinePc : UInt256 := ⟨9573⟩

theorem endGapSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endGapSlotFor I = solcMappingSlot ⟨13⟩ (endBytes32ArgWord I) := by
  unfold endGapSlotFor gapSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey hsz36]

theorem endDecode_gap_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (gapTransition.params.map Param.name)
      (transitionSignature gapTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (endBytes32ArgValue I)) := by
  simpa [config, gapTransition, endBytes32ArgValue, endBytes32ArgBytes, bytes32,
    bytes32Width, abiBytes32, abiBytes32Width] using
    (endDecode_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem endDecode_gap_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (gapTransition.params.map Param.name)
      (transitionSignature gapTransition).paramTypes I.calldata = none := by
  simpa [config, gapTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    (endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem endGapHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endGapHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endGapHigh2SplitWellFormed :
    selectorSplitWellFormed endBytecode endGapHigh2SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endGapArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endGapFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals
    dsimp [armWellFormed]
    repeat' first | apply And.intro | native_decide

theorem endReachGapBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endGapConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGapEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe6ee62aa⟩ :=
    endSelWord_eq_of_beq I hsz 0xe6 0xee 0x62 0xaa ⟨0xe6ee62aa⟩
      (by native_decide) (by simpa [selIs, endGapConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGapHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endGapHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h54 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGapHigh2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endGapHighSplitPc, endGapHigh2SplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 endGapHighSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h65 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGapFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    simpa [endGapHigh2SplitPc, endGapFirstArmPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54 endGapHigh2SplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGapFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGapFirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endGapEntryPc 1 h65
    (fun j hj => endGapArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endGapBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some gapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (gapTransition.params.map Param.name)
        (transitionSignature gapTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (endBytes32ArgValue I)))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endGapEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := endBytes32ArgWord I
  let slot := solcMappingSlot ⟨13⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (endBytes32ArgValue I)
  have hslot : endGapSlotFor I = slot := by
    simp [slot, key, endGapSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals gapTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord (endGapSlotFor I) σ_solm I).toNat))])) := by
    simpa [gapTransition, endGapSlotFor, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := gapRef (.var "arg0")) (er := endGapEvaledRef I)
        (slot := endGapSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, gapRef])
        (by
          have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
            have htlen : I.calldata.toList.length = I.calldata.size := by
              rw [byteArray_toList_eq, Array.length_toList]
              rfl
            rw [htlen]
            simp [bytes32Width]
            omega
          simp [endGapEvaledRef, endBytes32ArgValue, endBytes32ArgKey, evalStorageRef,
            evalStorageRefSteps, evalStorageRefStep, gapRef, evalExpr?, valueToKey?,
            EvalResult.ofOption, EvalResult.bind, pure, bind, locals, hargLen])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endGapEntryPc) (ret := endWordReturnPc)
    (decoded := endGapDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endGapDecodedPc) (ret := endWordReturnPc)
    (routine := endGapRoutinePc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := endGapRoutinePc) (baseSlot := ⟨13⟩) (key := key)
    (ret := endWordReturnPc) (R := [sel])
    (by simpa [key, endBytes32ArgWord] using hroutine)
    (by
      unfold solcSingleMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (endSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := endWordReturnPc) (val := endSlotWord slot σ_evm I) (ret := endWordReturnPc)
      (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨13⟩ key)
        (endSlotWord slot σ_evm I))
      (by simpa [slot, endSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨13⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨13⟩ key) (solcMappingHashMem_read64 ⟨13⟩ key))
      (by
        exact solcScratchReturnMem_read128 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨13⟩ key))
      (by simp)
    simpa [slot, endSlotWord] using hret'
  have hword : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (endSlotWord (endGapSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (endSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (endSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (endSlotWord slot σ_evm I).toNat))])
        gapTransition.returnType := by
    rw [show gapTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (endSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem endGapBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some gapTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endGapEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endGapEntryPc) (ret := endWordReturnPc)
    (decoded := endGapDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (endDecode_gap_none_short hsz4 hshort)

theorem endGapBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf gapTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endGapConcreteSelector := by
    simpa [endGapSelectorBytes, endGapConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endGapConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some gapTransition :=
    endDispatchGap hsel
  have hreach := endReachGapBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact endGapBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (endDecode_gap_ok hsz36) hreach hAccounts
  · exact endGapBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
