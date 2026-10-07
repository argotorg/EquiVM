import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `loaded(address)` -/

abbrev loadedMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev loadedMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev loadedMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "loaded", steps := [.mindex (.address (loadedMappingArg I))] }

abbrev loadedMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  loadedSlot (.address (loadedMappingArg I))

theorem loadedMappingSlotFor_eq (I : ExecutionEnv) :
    loadedMappingSlotFor I = solcMappingSlot ⟨7⟩ (loadedMappingKey I) := by
  unfold loadedMappingSlotFor loadedMappingArg loadedMappingKey loadedSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem cureDispatchLoaded {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 10)) :
    dispatchMsg contract I.calldata = some loadedTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some loadedTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes]
  native_decide

theorem cureDecode_loaded_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (loadedTransition.params.map Param.name)
      (transitionSignature loadedTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (loadedMappingArg I))) := by
  simpa [config, loadedTransition, loadedMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem cureDecode_loaded_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (loadedTransition.params.map Param.name)
      (transitionSignature loadedTransition).paramTypes I.calldata = none := by
  simpa [config, loadedTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem cureLoadedBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some loadedTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (loadedTransition.params.map Param.name)
        (transitionSignature loadedTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (loadedMappingArg I))))
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨873⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let key := loadedMappingKey I
  let slot := solcMappingSlot ⟨7⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (loadedMappingArg I))
  have hslot : loadedMappingSlotFor I = slot := by
    simp [slot, key, loadedMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals loadedTransition.body
        (.returned { contract := contract, locals := locals }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt (loadedMappingSlotFor I) σ I).toNat))])) := by
    simpa [loadedTransition, loadedMappingSlotFor, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      cureUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := loadedRef (.var "arg0")) (er := loadedMappingEvaledRef I)
        (slot := loadedMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, loadedRef])
        (by
          simp [loadedMappingEvaledRef, loadedMappingArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, loadedRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := cureBytecode) (sel := sel) (entry := ⟨873⟩) (ret := ⟨343⟩)
    (decoded := ⟨895⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := cureBytecode) (decoded := ⟨895⟩) (ret := ⟨343⟩) (routine := ⟨3648⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := cureBytecode) (pc := ⟨3648⟩) (baseSlot := ⟨7⟩) (key := key)
    (ret := ⟨343⟩) (R := [sel])
    (by simpa [key, loadedMappingKey] using hroutine)
    (by
      unfold solcSingleMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret cureBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨343⟩) (val := solcSlotWordAt slot σ I) (ret := ⟨343⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨7⟩ key)
        (solcSlotWordAt slot σ I))
      (by simpa [slot, solcSlotWordAt] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨7⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨7⟩ key) (solcMappingHashMem_read64 ⟨7⟩ key))
      (by
        exact solcScratchReturnMem_read128 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨7⟩ key))
      (by simp)
    simpa [slot, solcSlotWordAt] using hret'
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt (loadedMappingSlotFor I) σ I).toNat))])
        loadedTransition.returnType := by
    rw [show loadedTransition.returnType = [uint256] by rfl]
    rw [hslot]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  exact hret.reEquivExecution hcode hdispatch hdecode hbody henc

theorem cureLoadedBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some loadedTransition)
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨873⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := cureBytecode) (sel := sel) (entry := ⟨873⟩) (ret := ⟨343⟩)
    (decoded := ⟨895⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (cureDecode_loaded_none_short hsz4 hshort)

theorem cureLoadedBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 10)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 10) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some loadedTransition :=
    cureDispatchLoaded hsel
  have hreach := cureReachLoadedBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact cureLoadedBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (cureDecode_loaded_ok hsz36) hreach
  · exact cureLoadedBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Cure
