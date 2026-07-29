import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `pos(address)` -/

abbrev posMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev posMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev posMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "pos", steps := [.mindex (.address (posMappingArg I))] }

abbrev posMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  posSlot (.address (posMappingArg I))

theorem posMappingSlotFor_eq (I : ExecutionEnv) :
    posMappingSlotFor I = solcMappingSlot ⟨5⟩ (posMappingKey I) := by
  unfold posMappingSlotFor posMappingArg posMappingKey posSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem cureDispatchPos {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 11)) :
    dispatchMsg contract I.calldata = some posTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some posTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes, curePosSelectorBytes]
  native_decide

theorem cureDecode_pos_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (posTransition.params.map Param.name)
      (transitionSignature posTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (posMappingArg I))) := by
  simpa [config, posTransition, posMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem cureDecode_pos_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (posTransition.params.map Param.name)
      (transitionSignature posTransition).paramTypes I.calldata = none := by
  simpa [config, posTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem curePosBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some posTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (posTransition.params.map Param.name)
        (transitionSignature posTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (posMappingArg I))))
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨678⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := posMappingKey I
  let slot := solcMappingSlot ⟨5⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (posMappingArg I))
  have hslot : posMappingSlotFor I = slot := by
    simp [slot, key, posMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals posTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (cureSlotWord (posMappingSlotFor I) σ_solm I).toNat))])) := by
    simpa [posTransition, posMappingSlotFor, cureSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      cureUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := posRef (.var "arg0")) (er := posMappingEvaledRef I)
        (slot := posMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, posRef])
        (by
          simp [posMappingEvaledRef, posMappingArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, posRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := cureBytecode) (sel := sel) (entry := ⟨678⟩) (ret := ⟨343⟩)
    (decoded := ⟨700⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := cureBytecode) (decoded := ⟨700⟩) (ret := ⟨343⟩) (routine := ⟨3326⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := cureBytecode) (pc := ⟨3326⟩) (baseSlot := ⟨5⟩) (key := key)
    (ret := ⟨343⟩) (R := [sel])
    (by simpa [key, posMappingKey] using hroutine)
    (by
      unfold solcSingleMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret cureBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (cureSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨343⟩) (val := cureSlotWord slot σ_evm I) (ret := ⟨343⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨5⟩ key)
        (cureSlotWord slot σ_evm I))
      (by simpa [slot, cureSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨5⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (cureSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨5⟩ key) (solcMappingHashMem_read64 ⟨5⟩ key))
      (by
        exact solcScratchReturnMem_read128 (cureSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨5⟩ key))
      (by simp)
    simpa [slot, cureSlotWord] using hret'
  have hword : cureSlotWord slot σ_evm I = cureSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (cureSlotWord (posMappingSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (cureSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (cureSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (cureSlotWord slot σ_evm I).toNat))])
        posTransition.returnType := by
    rw [show posTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (cureSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem curePosBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some posTransition)
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨678⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := cureBytecode) (sel := sel) (entry := ⟨678⟩) (ret := ⟨343⟩)
    (decoded := ⟨700⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (cureDecode_pos_none_short hsz4 hshort)

theorem curePosBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 11) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some posTransition :=
    cureDispatchPos hsel
  have hreach := cureReachPosBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact curePosBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (cureDecode_pos_ok hsz36) hreach hAccounts
  · exact curePosBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Cure
