import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Cure

/-! ## `amt(address)` -/

abbrev amtMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev amtMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev amtMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "amt", steps := [.mindex (.address (amtMappingArg I))] }

abbrev amtMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  amtSlot (.address (amtMappingArg I))

theorem amtMappingSlotFor_eq (I : ExecutionEnv) :
    amtMappingSlotFor I = solcMappingSlot ⟨6⟩ (amtMappingKey I) := by
  unfold amtMappingSlotFor amtMappingArg amtMappingKey amtSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem cureDispatchAmt {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 0)) :
    dispatchMsg contract I.calldata = some amtTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some amtTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes, cureAmtSelectorBytes]
  native_decide

theorem cureDecode_amt_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (amtTransition.params.map Param.name)
      (transitionSignature amtTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (amtMappingArg I))) := by
  simpa [config, amtTransition, amtMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem cureDecode_amt_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (amtTransition.params.map Param.name)
      (transitionSignature amtTransition).paramTypes I.calldata = none := by
  simpa [config, amtTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem cureAmtBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some amtTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (amtTransition.params.map Param.name)
        (transitionSignature amtTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (amtMappingArg I))))
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := amtMappingKey I
  let slot := solcMappingSlot ⟨6⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (amtMappingArg I))
  have hslot : amtMappingSlotFor I = slot := by
    simp [slot, key, amtMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals amtTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (cureSlotWord (amtMappingSlotFor I) σ_solm I).toNat))])) := by
    simpa [amtTransition, amtMappingSlotFor, cureSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      cureUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := amtRef (.var "arg0")) (er := amtMappingEvaledRef I)
        (slot := amtMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, amtRef])
        (by
          simp [amtMappingEvaledRef, amtMappingArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, amtRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := cureBytecode) (sel := sel) (entry := ⟨305⟩) (ret := ⟨343⟩)
    (decoded := ⟨327⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := cureBytecode) (decoded := ⟨327⟩) (ret := ⟨343⟩) (routine := ⟨911⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := cureBytecode) (pc := ⟨911⟩) (baseSlot := ⟨6⟩) (key := key)
    (ret := ⟨343⟩) (R := [sel])
    (by simpa [key, amtMappingKey] using hroutine)
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
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨6⟩ key)
        (cureSlotWord slot σ_evm I))
      (by simpa [slot, cureSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨6⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (cureSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨6⟩ key) (solcMappingHashMem_read64 ⟨6⟩ key))
      (by
        exact solcScratchReturnMem_read128 (cureSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨6⟩ key))
      (by simp)
    simpa [slot, cureSlotWord] using hret'
  have hword : cureSlotWord slot σ_evm I = cureSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (cureSlotWord (amtMappingSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (cureSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (cureSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (cureSlotWord slot σ_evm I).toNat))])
        amtTransition.returnType := by
    rw [show amtTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (cureSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem cureAmtBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some amtTransition)
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := cureBytecode) (sel := sel) (entry := ⟨305⟩) (ret := ⟨343⟩)
    (decoded := ⟨327⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (cureDecode_amt_none_short hsz4 hshort)

theorem cureAmtBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 0) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some amtTransition :=
    cureDispatchAmt hsel
  have hreach := cureReachAmtBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact cureAmtBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (cureDecode_amt_ok hsz36) hreach hAccounts
  · exact cureAmtBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Cure
