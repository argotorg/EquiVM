import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `gap(bytes32)` mapping getter -/

abbrev endGapConcreteSelector : ByteArray := selectorBytes 0xe6 0xee 0x62 0xaa
abbrev endGapEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "gap", steps := [.mindex (endBytes32ArgKey I)] }
abbrev endGapSlotFor (I : ExecutionEnv) : UInt256 :=
  gapSlot (endBytes32ArgKey I)

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
    (decodeCalldataWithMode_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem endDecode_gap_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (gapTransition.params.map Param.name)
      (transitionSignature gapTransition).paramTypes I.calldata = none := by
  simpa [config, gapTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

set_option maxHeartbeats 1000000 in
theorem endGapArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endGapFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals
    dsimp [armWellFormed]
    repeat' first | apply And.intro | native_decide

theorem endReachGapBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endGapConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState σ σ₀ g A I)
        endGapEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  have hword : endSelWord I = ⟨0xe6ee62aa⟩ :=
    endSelWord_eq_of_beq I hsz 0xe6 0xee 0x62 0xaa ⟨0xe6ee62aa⟩
      (by native_decide) (by simpa [selIs, endGapConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup65FirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
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
  exact RD.dispatchTo endGapEntryPc 1 hfirst
    (fun j hj => endGapArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endGapBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some gapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (gapTransition.params.map Param.name)
        (transitionSignature gapTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (endBytes32ArgValue I)))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) endGapEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let key := endBytes32ArgWord I
  let slot := solcMappingSlot ⟨13⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (endBytes32ArgValue I)
  have hslot : endGapSlotFor I = slot := by
    simp [slot, key, endGapSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals gapTransition.body
        (.returned { contract := contract, locals := locals }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt (endGapSlotFor I) σ I).toNat))])) := by
    simpa [gapTransition, endGapSlotFor, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      endUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
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
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := endWordReturnPc) (val := solcSlotWordAt slot σ I) (ret := endWordReturnPc)
      (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨13⟩ key)
        (solcSlotWordAt slot σ I))
      (by simpa [slot, solcSlotWordAt] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨13⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨13⟩ key) (solcMappingHashMem_read64 ⟨13⟩ key))
      (by
        exact solcScratchReturnMem_read128 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨13⟩ key))
      (by simp)
    simpa [slot, solcSlotWordAt] using hret'
  have hval :
      some [Value.int (Int.ofNat (solcSlotWordAt (endGapSlotFor I) σ I).toNat)] =
        some [Value.int (Int.ofNat (solcSlotWordAt slot σ I).toNat)] := by
    rw [hslot]
  rw [hval] at hbody
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        gapTransition.returnType := by
    rw [show gapTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  exact hret.reEquivExecution hcode hdispatch hdecode hbody henc

theorem endGapBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some gapTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) endGapEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
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

theorem endGapBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf gapTransition)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsel' : selIs I endGapConcreteSelector := by
    simpa [endGapSelectorBytes, endGapConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endGapConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some gapTransition :=
    endDispatchGap hsel
  have hreach := endReachGapBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact endGapBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (endDecode_gap_ok hsz36) hreach
  · exact endGapBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
