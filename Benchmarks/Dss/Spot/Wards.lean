import Benchmarks.Dss.Spot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

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

theorem spotDecode_wards_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))) := by
  simpa [config, wardsTransition, wardsMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem spotDecode_wards_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  simpa [config, wardsTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem spotReachWardsBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 11)) :
    ∃ k C, RD spotBytecode I g (initState σ σ₀ g A I)
        ⟨446⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : spotSelWord I = ⟨0xbf353dbb⟩ :=
    spotSelWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb ⟨0xbf353dbb⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc 3))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachHighBody 3 (by omega) ⟨446⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem spotWardsBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
        (transitionSignature wardsTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨446⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let key := wardsMappingKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (wardsMappingArg I))
  have hslot : wardsMappingSlotFor I = slot := by
    simp [slot, key, wardsMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals wardsTransition.body
        (.returned { contract := contract, locals := locals }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt (wardsMappingSlotFor I) σ I).toNat))])) := by
    simpa [wardsTransition, wardsMappingSlotFor, solcSlotWordAt, initState,
      Solm.EVM.storageLoad, State.lookupAccount, locals, key] using
      spotUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
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
    (code := spotBytecode) (sel := sel) (entry := ⟨446⟩) (ret := ⟨336⟩)
    (decoded := ⟨468⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := spotBytecode) (decoded := ⟨468⟩) (ret := ⟨336⟩) (routine := ⟨1782⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcZeroSlotMappingGetter
    (code := spotBytecode) (pc := ⟨1782⟩) (key := key) (ret := ⟨336⟩) (R := [sel])
    (by simpa [key, wardsMappingKey] using hroutine)
    (by
      unfold solcZeroSlotMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret spotBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨336⟩) (val := solcSlotWordAt slot σ I) (ret := ⟨336⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨0⟩ key)
        (solcSlotWordAt slot σ I))
      (by simpa [slot, solcSlotWordAt] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨0⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨0⟩ key) (solcMappingHashMem_read64 ⟨0⟩ key))
      (by
        exact solcScratchReturnMem_read128 (solcSlotWordAt slot σ I)
          (solcMappingHashMem_size ⟨0⟩ key))
      (by simp)
    simpa [slot, solcSlotWordAt] using hret'
  have hword : solcSlotWordAt slot σ I = solcSlotWordAt slot σ I := rfl
  have hval :
      some [Value.int (Int.ofNat (solcSlotWordAt (wardsMappingSlotFor I) σ I).toNat)] =
        some [Value.int (Int.ofNat (solcSlotWordAt slot σ I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        wardsTransition.returnType := by
    rw [show wardsTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval henc

theorem spotWardsBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨446⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := spotBytecode) (sel := sel) (entry := ⟨446⟩) (ret := ⟨336⟩)
    (decoded := ⟨468⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (spotDecode_wards_none_short hsz4 hshort)

theorem spotWardsBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 11)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 11) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some wardsTransition :=
    spotDispatchWards hsel
  have hreach := spotReachWardsBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact spotWardsBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (spotDecode_wards_ok hsz36) hreach
  · exact spotWardsBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Spot
