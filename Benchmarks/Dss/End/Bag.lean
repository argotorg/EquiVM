import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `bag(address)` mapping getter -/

abbrev endBagConcreteSelector : ByteArray := selectorBytes 0x92 0x55 0xf8 0x09
abbrev endBagArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat
abbrev endBagKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)
abbrev endBagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bag", steps := [.mindex (.address (endBagArg I))] }
abbrev endBagSlotFor (I : ExecutionEnv) : UInt256 :=
  bagSlot (.address (endBagArg I))

abbrev endBagHighSplitPc : UInt256 := ⟨43⟩
abbrev endBagHighJumpdestPc : UInt256 := ⟨162⟩
abbrev endBagMidSplitPc : UInt256 := ⟨163⟩
abbrev endBagGroupJumpdestPc : UInt256 := ⟨222⟩
abbrev endBagFirstArmPc : UInt256 := ⟨223⟩
abbrev endBagEntryPc : UInt256 := ⟨895⟩
abbrev endBagDecodedPc : UInt256 := ⟨917⟩
abbrev endBagRoutinePc : UInt256 := ⟨7476⟩

theorem endBagSlotFor_eq (I : ExecutionEnv) :
    endBagSlotFor I = solcMappingSlot ⟨16⟩ (endBagKey I) := by
  unfold endBagSlotFor endBagArg endBagKey bagSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem endDecode_bag_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (bagTransition.params.map Param.name)
      (transitionSignature bagTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (endBagArg I))) := by
  simpa [config, bagTransition, endBagArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem endDecode_bag_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (bagTransition.params.map Param.name)
      (transitionSignature bagTransition).paramTypes I.calldata = none := by
  simpa [config, bagTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem endBagHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endBagHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endBagMidSplitWellFormed :
    selectorSplitWellFormed endBytecode endBagMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endBagArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endBagFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals
    dsimp [armWellFormed]
    repeat' first | apply And.intro | native_decide

theorem endReachBagBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endBagConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endBagEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x9255f809⟩ :=
    endSelWord_eq_of_beq I hsz 0x92 0x55 0xf8 0x09 ⟨0x9255f809⟩
      (by native_decide) (by simpa [selIs, endBagConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endBagHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endBagHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h162 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endBagHighJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endBagHighSplitPc, endBagHighJumpdestPc] using
      RD.selectorSplitTakenAuto h43 endBagHighSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h163 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endBagMidSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [endBagMidSplitPc] using h162.jumpdest (by native_decide) (by simp)
  have h222 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endBagGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
    simpa [endBagMidSplitPc, endBagGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h163 endBagMidSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h223 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endBagFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5 + 1)
        (C32 + 22 + 22 + 1 + 22 + 1) := by
    simpa [endBagFirstArmPc] using h222.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endBagFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endBagFirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endBagEntryPc 1 h223
    (fun j hj => endBagArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endBagBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some bagTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (bagTransition.params.map Param.name)
        (transitionSignature bagTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (endBagArg I))))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endBagEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := endBagKey I
  let slot := solcMappingSlot ⟨16⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (endBagArg I))
  have hslot : endBagSlotFor I = slot := by
    simp [slot, key, endBagSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals bagTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord (endBagSlotFor I) σ_solm I).toNat))])) := by
    simpa [bagTransition, endBagSlotFor, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := bagRef (.var "arg0")) (er := endBagEvaledRef I)
        (slot := endBagSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, bagRef])
        (by
          simp [endBagEvaledRef, endBagArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, bagRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endBagEntryPc) (ret := endWordReturnPc)
    (decoded := endBagDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := endBytecode) (decoded := endBagDecodedPc) (ret := endWordReturnPc)
    (routine := endBagRoutinePc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := endBytecode) (pc := endBagRoutinePc) (baseSlot := ⟨16⟩) (key := key)
    (ret := endWordReturnPc) (R := [sel])
    (by simpa [key, endBagKey] using hroutine)
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
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨16⟩ key)
        (endSlotWord slot σ_evm I))
      (by simpa [slot, endSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨16⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨16⟩ key) (solcMappingHashMem_read64 ⟨16⟩ key))
      (by
        exact solcScratchReturnMem_read128 (endSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨16⟩ key))
      (by simp)
    simpa [slot, endSlotWord] using hret'
  have hword : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (endSlotWord (endBagSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (endSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (endSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (endSlotWord slot σ_evm I).toNat))])
        bagTransition.returnType := by
    rw [show bagTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (endSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem endBagBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some bagTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endBagEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endBagEntryPc) (ret := endWordReturnPc)
    (decoded := endBagDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (endDecode_bag_none_short hsz4 hshort)

theorem endBagBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf bagTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endBagConcreteSelector := by
    simpa [endBagSelectorBytes, endBagConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endBagConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some bagTransition :=
    endDispatchBag hsel
  have hreach := endReachBagBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact endBagBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (endDecode_bag_ok hsz36) hreach hAccounts
  · exact endBagBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
