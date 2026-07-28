import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `dai(address)` mapping getter -/

abbrev daiMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev daiMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev daiMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "dai", steps := [.mindex (.address (daiMappingArg I))] }

abbrev daiMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  daiSlot (.address (daiMappingArg I))

theorem daiMappingSlotFor_eq (I : ExecutionEnv) :
    daiMappingSlotFor I = solcMappingSlot ⟨5⟩ (daiMappingKey I) := by
  unfold daiMappingSlotFor daiMappingArg daiMappingKey daiSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem vatDecode_dai_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (daiTransition.params.map Param.name)
      (transitionSignature daiTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (daiMappingArg I))) := by
  simpa [config, daiTransition, daiMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem vatDecode_dai_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (daiTransition.params.map Param.name)
      (transitionSignature daiTransition).paramTypes I.calldata = none := by
  simpa [config, daiTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem vatReachDaiBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 3)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨863⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x6c25b346⟩ :=
    vatSelWord_eq_of_beq I hsz 0x6c 0x25 0xb3 0x46 ⟨0x6c25b346⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms272Body 1 (by omega) ⟨863⟩ hcode hwv hsz hsize
    hroot hlow hlowhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatDaiBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some daiTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (daiTransition.params.map Param.name)
        (transitionSignature daiTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (daiMappingArg I))))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨863⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := daiMappingKey I
  let slot := solcMappingSlot ⟨5⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (daiMappingArg I))
  have hslot : daiMappingSlotFor I = slot := by
    simp [slot, key, daiMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals daiTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vatSlotWord (daiMappingSlotFor I) σ_solm I).toNat))])) := by
    simpa [daiTransition, daiMappingSlotFor, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      vatUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := daiRef (.var "arg0")) (er := daiMappingEvaledRef I)
        (slot := daiMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, daiRef])
        (by
          simp [daiMappingEvaledRef, daiMappingArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, daiRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨863⟩) (ret := ⟨465⟩)
    (decoded := ⟨885⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨885⟩) (ret := ⟨465⟩) (routine := ⟨2957⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := vatBytecode) (pc := ⟨2957⟩) (baseSlot := ⟨5⟩)
    (key := key) (ret := ⟨465⟩) (R := [sel])
    (by simpa [key, daiMappingKey] using hroutine)
    (by
      unfold solcSingleMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (vatSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨465⟩) (val := vatSlotWord slot σ_evm I) (ret := ⟨465⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨5⟩ key)
        (vatSlotWord slot σ_evm I))
      (by simpa [slot, vatSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨5⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (vatSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨5⟩ key) (solcMappingHashMem_read64 ⟨5⟩ key))
      (by
        exact solcScratchReturnMem_read128 (vatSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨5⟩ key))
      (by simp)
    simpa [slot, vatSlotWord] using hret'
  have hword : vatSlotWord slot σ_evm I = vatSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (vatSlotWord (daiMappingSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (vatSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat))])
        daiTransition.returnType := by
    rw [show daiTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (vatSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem vatDaiBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some daiTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨863⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨863⟩) (ret := ⟨465⟩)
    (decoded := ⟨885⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (vatDecode_dai_none_short hsz4 hshort)

theorem vatDaiBodyCore : VatBodyTheorem 3 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some daiTransition :=
    vatDispatchDai hsel
  have hreach := vatReachDaiBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatDaiBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (vatDecode_dai_ok hsz36) hreach hAccounts
  · exact vatDaiBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
