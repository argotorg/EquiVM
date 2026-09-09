import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `fix(bytes32)` mapping getter -/

abbrev endFixConcreteSelector : ByteArray := selectorBytes 0x63 0xfa 0xd8 0x5e
abbrev endFixEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "fix", steps := [.mindex (endBytes32ArgKey I)] }
abbrev endFixSlotFor (I : ExecutionEnv) : UInt256 :=
  fixSlot (endBytes32ArgKey I)

abbrev endFixHighSplitPc : UInt256 := ⟨283⟩
abbrev endFixGroupJumpdestPc : UInt256 := ⟨342⟩
abbrev endFixFirstArmPc : UInt256 := ⟨343⟩
abbrev endFixEntryPc : UInt256 := ⟨723⟩
abbrev endFixDecodedPc : UInt256 := ⟨745⟩
abbrev endFixRoutinePc : UInt256 := ⟨5251⟩

theorem endFixSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endFixSlotFor I = solcMappingSlot ⟨15⟩ (endBytes32ArgWord I) := by
  unfold endFixSlotFor fixSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey hsz36]

theorem endDecode_fix_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fixTransition.params.map Param.name)
      (transitionSignature fixTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (endBytes32ArgValue I)) := by
  simpa [config, fixTransition, endBytes32ArgValue, endBytes32ArgBytes, bytes32,
    bytes32Width, abiBytes32, abiBytes32Width] using
    (endDecode_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem endDecode_fix_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (fixTransition.params.map Param.name)
      (transitionSignature fixTransition).paramTypes I.calldata = none := by
  simpa [config, fixTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    (endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem endFixHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endFixHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

set_option maxHeartbeats 1000000 in
theorem endFixArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endFixFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals
    dsimp [armWellFormed]
    repeat' first | apply And.intro | decide +native

theorem endReachFixBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endFixConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endFixEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x63fad85e⟩ :=
    endSelWord_eq_of_beq I hsz 0x63 0xfa 0xd8 0x5e ⟨0x63fad85e⟩
      (by decide +native) (by simpa [selIs, endFixConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endLow1JumpdestPc] using
      RD.selectorSplitTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; decide +native) (by jump_dest) (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by decide +native) (by simp)
  have h283 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endFixHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [endLow1SplitPc, endFixHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h272 endLow1SplitWellFormed
        (by rw [hword]; decide +native) (by simp)
  have h342 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endFixGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    simpa [endFixHighSplitPc, endFixGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h283 endFixHighSplitWellFormed
        (by rw [hword]; decide +native) (by jump_dest) (by simp)
  have h343 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endFixFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5 + 1)
        (C32 + 22 + 1 + 22 + 22 + 1) := by
    simpa [endFixFirstArmPc] using h342.jumpdest (by decide +native) (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endFixFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endFixFirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo endFixEntryPc 1 h343
    (fun j hj => endFixArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem endFixBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fixTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fixTransition.params.map Param.name)
        (transitionSignature fixTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (endBytes32ArgValue I)))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endFixEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := endBytes32ArgWord I
  let slot := solcMappingSlot ⟨15⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (endBytes32ArgValue I)
  have hslot : endFixSlotFor I = slot := by
    simp [slot, key, endFixSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals fixTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord (endFixSlotFor I) σ_solm I).toNat))])) := by
    simpa [fixTransition, endFixSlotFor, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := fixRef (.var "arg0")) (er := endFixEvaledRef I)
        (slot := endFixSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, fixRef])
        (by
          have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
            have htlen : I.calldata.toList.length = I.calldata.size := by
              rw [byteArray_toList_eq, Array.length_toList]
              rfl
            rw [htlen]
            simp [bytes32Width]
            omega
          simp [endFixEvaledRef, endBytes32ArgValue, endBytes32ArgKey, evalStorageRef,
            evalStorageRefSteps, evalStorageRefStep, fixRef, evalExpr?, valueToKey?,
            EvalResult.ofOption, EvalResult.bind, pure, bind, locals, hargLen])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endFixEntryPc) (ret := endWordReturnPc)
    (decoded := endFixDecodedPc) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endFixDecodedPc) (ret := endWordReturnPc)
    (routine := endFixRoutinePc) (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := endFixRoutinePc) (baseSlot := ⟨15⟩) (key := key)
    (ret := endWordReturnPc) (R := [sel])
    (by simpa [key, endBytes32ArgWord] using hroutine)
    (by
      unfold solcSingleMappingGetterWf
      repeat' first | apply And.intro | decide +native)
    (by jump_dest) (by simp)
  have hret :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (endSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := endWordReturnPc) (val := endSlotWord slot σ_evm I) (ret := endWordReturnPc)
      (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨15⟩ key)
        (endSlotWord slot σ_evm I))
      (by simpa [slot, endSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | decide +native)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨15⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨15⟩ key) (solcMappingHashMem_read64 ⟨15⟩ key))
      (by
        exact solcScratchReturnMem_read128 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨15⟩ key))
      (by simp)
    simpa [slot, endSlotWord] using hret'
  have hword : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (endSlotWord (endFixSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (endSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (endSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (endSlotWord slot σ_evm I).toNat))])
        fixTransition.returnType := by
    rw [show fixTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (endSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem endFixBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some fixTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endFixEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endFixEntryPc) (ret := endWordReturnPc)
    (decoded := endFixDecodedPc) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (endDecode_fix_none_short hsz4 hshort)

theorem endFixBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf fixTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endFixConcreteSelector := by
    simpa [endFixSelectorBytes, endFixConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endFixConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some fixTransition :=
    endDispatchFix hsel
  have hreach := endReachFixBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact endFixBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (endDecode_fix_ok hsz36) hreach hAccounts
  · exact endFixBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
