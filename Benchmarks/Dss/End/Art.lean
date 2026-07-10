import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `Art(bytes32)` mapping getter -/

abbrev endArtConcreteSelector : ByteArray := selectorBytes 0xe1 0x34 0x0a 0x3d
abbrev endArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "Art", steps := [.mindex (endBytes32ArgKey I)] }
abbrev endArtSlotFor (I : ExecutionEnv) : UInt256 :=
  ArtSlot (endBytes32ArgKey I)

abbrev endArtHighSplitPc : UInt256 := ⟨43⟩
abbrev endArtHigh2SplitPc : UInt256 := ⟨54⟩
abbrev endArtGroupJumpdestPc : UInt256 := ⟨113⟩
abbrev endArtFirstArmPc : UInt256 := ⟨114⟩
abbrev endArtEntryPc : UInt256 := ⟨1142⟩
abbrev endArtDecodedPc : UInt256 := ⟨1164⟩
abbrev endArtRoutinePc : UInt256 := ⟨8814⟩

theorem endArtSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endArtSlotFor I = solcMappingSlot ⟨14⟩ (endBytes32ArgWord I) := by
  unfold endArtSlotFor ArtSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey hsz36]

theorem endDecode_Art_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (ArtTransition.params.map Param.name)
      (transitionSignature ArtTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (endBytes32ArgValue I)) := by
  simpa [config, ArtTransition, endBytes32ArgValue, endBytes32ArgBytes, bytes32,
    bytes32Width, abiBytes32, abiBytes32Width] using
    (endDecode_legacyBytes32_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem endDecode_Art_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (ArtTransition.params.map Param.name)
      (transitionSignature ArtTransition).paramTypes I.calldata = none := by
  simpa [config, ArtTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    (endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem endArtHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endArtHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endArtHigh2SplitWellFormed :
    selectorSplitWellFormed endBytecode endArtHigh2SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endArtArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endArtFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals
    dsimp [armWellFormed]
    repeat' first | apply And.intro | native_decide

theorem endReachArtBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endArtConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endArtEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe1340a3d⟩ :=
    endSelWord_eq_of_beq I hsz 0xe1 0x34 0x0a 0x3d ⟨0xe1340a3d⟩
      (by native_decide) (by simpa [selIs, endArtConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endArtHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endArtHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h54 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endArtHigh2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endArtHighSplitPc, endArtHigh2SplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 endArtHighSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h113 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endArtGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    simpa [endArtHigh2SplitPc, endArtGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h54 endArtHigh2SplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h114 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endArtFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5 + 1) (C32 + 22 + 22 + 22 + 1) := by
    simpa [endArtFirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endArtFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endArtFirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endArtEntryPc 1 h114
    (fun j hj => endArtArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endArtBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some ArtTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (ArtTransition.params.map Param.name)
        (transitionSignature ArtTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (endBytes32ArgValue I)))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endArtEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := endBytes32ArgWord I
  let slot := solcMappingSlot ⟨14⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (endBytes32ArgValue I)
  have hslot : endArtSlotFor I = slot := by
    simp [slot, key, endArtSlotFor_eq hsz36]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals ArtTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord (endArtSlotFor I) σ_solm I).toNat))])) := by
    simpa [ArtTransition, endArtSlotFor, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := ArtRef (.var "arg0")) (er := endArtEvaledRef I)
        (slot := endArtSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, ArtRef])
        (by
          have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
            have htlen : I.calldata.toList.length = I.calldata.size := by
              rw [byteArray_toList_eq, Array.length_toList]
              rfl
            rw [htlen]
            simp [bytes32Width]
            omega
          simp [endArtEvaledRef, endBytes32ArgValue, endBytes32ArgKey, evalStorageRef,
            evalStorageRefSteps, evalStorageRefStep, ArtRef, evalExpr?, valueToKey?,
            EvalResult.ofOption, EvalResult.bind, pure, bind, locals, hargLen])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endArtEntryPc) (ret := endWordReturnPc)
    (decoded := endArtDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endArtDecodedPc) (ret := endWordReturnPc)
    (routine := endArtRoutinePc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := endArtRoutinePc) (baseSlot := ⟨14⟩) (key := key)
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
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨14⟩ key)
        (endSlotWord slot σ_evm I))
      (by simpa [slot, endSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨14⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨14⟩ key) (solcMappingHashMem_read64 ⟨14⟩ key))
      (by
        exact solcScratchReturnMem_read128 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨14⟩ key))
      (by simp)
    simpa [slot, endSlotWord] using hret'
  have hword : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (endSlotWord (endArtSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (endSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (endSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (endSlotWord slot σ_evm I).toNat))])
        ArtTransition.returnType := by
    rw [show ArtTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (endSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem endArtBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some ArtTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endArtEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endArtEntryPc) (ret := endWordReturnPc)
    (decoded := endArtDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (endDecode_Art_none_short hsz4 hshort)

theorem endArtBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf ArtTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endArtConcreteSelector := by
    simpa [endArtSelectorBytes, endArtConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endArtConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some ArtTransition :=
    endDispatchArt hsel
  have hreach := endReachArtBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact endArtBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (endDecode_Art_ok hsz36) hreach hAccounts
  · exact endArtBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
