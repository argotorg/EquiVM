import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `wards(address)` mapping getter -/

abbrev wardsMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev wardsMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev wardsMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (wardsMappingArg I))] }

abbrev wardsMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (wardsMappingArg I))

theorem wardsMappingSlotFor_eq (I : ExecutionEnv) :
    wardsMappingSlotFor I = solcMappingSlot ⟨0⟩ (wardsMappingKey I) := by
  unfold wardsMappingSlotFor wardsMappingArg wardsMappingKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem vatDecode_wards_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))) := by
  simpa [config, wardsTransition, wardsMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem vatDecode_wards_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  simpa [config, wardsTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem vatReachWardsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 27)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1357⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xbf353dbb⟩ :=
    vatSelWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb ⟨0xbf353dbb⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms114Body 1 (by omega) ⟨1357⟩ hcode hwv hsz hsize
    hroot hhigh hhighhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatWardsBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
        (transitionSignature wardsTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1357⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := wardsMappingKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (wardsMappingArg I))
  have hslot : wardsMappingSlotFor I = slot := by
    simp [slot, key, wardsMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals wardsTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vatSlotWord (wardsMappingSlotFor I) σ_solm I).toNat))])) := by
    simpa [wardsTransition, wardsMappingSlotFor, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      vatUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := wardsRef (.var "arg0")) (er := wardsMappingEvaledRef I)
        (slot := wardsMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, wardsRef])
        (by
          simp [wardsMappingEvaledRef, wardsMappingArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, wardsRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1357⟩) (ret := ⟨465⟩)
    (decoded := ⟨1379⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨1379⟩) (ret := ⟨465⟩) (routine := ⟨6066⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcZeroSlotMappingGetter
    (code := vatBytecode) (pc := ⟨6066⟩) (key := key) (ret := ⟨465⟩) (R := [sel])
    (by simpa [key, wardsMappingKey] using hroutine)
    (by
      unfold solcZeroSlotMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (vatSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨465⟩) (val := vatSlotWord slot σ_evm I) (ret := ⟨465⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨0⟩ key)
        (vatSlotWord slot σ_evm I))
      (by simpa [slot, vatSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨0⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (vatSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨0⟩ key) (solcMappingHashMem_read64 ⟨0⟩ key))
      (by
        exact solcScratchReturnMem_read128 (vatSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨0⟩ key))
      (by simp)
    simpa [slot, vatSlotWord] using hret'
  have hword : vatSlotWord slot σ_evm I = vatSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (vatSlotWord (wardsMappingSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (vatSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (vatSlotWord slot σ_evm I).toNat))])
        wardsTransition.returnType := by
    rw [show wardsTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (vatSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem vatWardsBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1357⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1357⟩) (ret := ⟨465⟩)
    (decoded := ⟨1379⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (vatDecode_wards_none_short hsz4 hshort)

theorem vatWardsBodyCore : VatBodyTheorem 27 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 27) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some wardsTransition :=
    vatDispatchWards hsel
  have hreach := vatReachWardsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatWardsBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (vatDecode_wards_ok hsz36) hreach hAccounts
  · exact vatWardsBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
