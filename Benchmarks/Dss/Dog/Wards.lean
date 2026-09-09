import Benchmarks.Dss.Dog.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

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

theorem dogDecode_wards_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))) := by
  simpa [config, wardsTransition, wardsMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem dogDecode_wards_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  simpa [config, wardsTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4
      hshort)

theorem dogReachWardsBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 16)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨512⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xbf353dbb⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb ⟨0xbf353dbb⟩
      (by decide +native) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hhighTgt : armTgt code (⟨43⟩ : UInt256) = ⟨113⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by decide +native)]
    decide +native
  have h113 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [hhighTgt] using
      RD.selectorSplitTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh
        (by
          rw [hhighTgt]
          exact dogPatchedDJumpPrefix1405 ⟨113⟩ hpatch (by decide +native))
        (by simp)
  have h114 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa using
      h113.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨113⟩) hpatch (by decide +native)]
          decide +native)
        (by simp only [List.length_singleton]; omega)
  have hhole : UInt256.eq (dogSelectorWord 1) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hwards : UInt256.eq (dogSelectorWord 16) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have h125 := by
    simpa [selArmNextPc] using
      h114.selectorArmNotTaken (selNat := dogSelectorWord 1) (tgt := (⟨504⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hhole
        (by simp)
  have h512 := by
    simpa using
      h125.selectorArmTaken (selNat := dogSelectorWord 16) (tgt := (⟨512⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
          decide +native)
        hwards
        (dogPatchedDJumpPrefix1405 ⟨512⟩ hpatch (by decide +native))
        (by simp)
  exact ⟨_, _, h512⟩

theorem dogWardsBodyCoreOk
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some wardsTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (wardsTransition.params.map Param.name)
        (transitionSignature wardsTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨512⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := wardsMappingKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (wardsMappingArg I))
  have hslot : wardsMappingSlotFor I = slot := by
    simp [slot, key, wardsMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        wardsTransition.body
        (.returned { contract := contract v, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat
            (dogSlotWord (wardsMappingSlotFor I) σ_solm I).toNat))])) := by
    simpa [wardsTransition, wardsMappingSlotFor, dogSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, locals, key] using
      dogUint256GetterBodyReturns v
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
    (code := code) (sel := sel) (entry := ⟨512⟩) (ret := ⟨448⟩)
    (decoded := ⟨534⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (dogPatchedDJumpPrefix1405 ⟨534⟩ hpatch (by decide +native)) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := code) (decoded := ⟨534⟩) (ret := ⟨448⟩) (routine := ⟨1918⟩)
    (R := [sel]) hdecoded
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (dogPatchedJumpDest hpatch (by decide +native)) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcZeroSlotMappingGetter
    (code := code) (pc := ⟨1918⟩) (key := key) (ret := ⟨448⟩) (R := [sel])
    (by simpa [key, wardsMappingKey] using hroutine)
    (by
      unfold solcZeroSlotMappingGetterWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by decide +native) (by decide +native)]
          decide +native)
    (dogPatchedDJumpPrefix1405 ⟨448⟩ hpatch (by decide +native))
    (by simp)
  have hret :
      RDret code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (dogSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨448⟩) (val := dogSlotWord slot σ_evm I) (ret := ⟨448⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨0⟩ key)
        (dogSlotWord slot σ_evm I))
      (by simpa [slot, dogSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first
          | apply And.intro
          | rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]
            decide +native)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨0⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (dogSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨0⟩ key) (solcMappingHashMem_read64 ⟨0⟩ key))
      (by
        exact solcScratchReturnMem_read128 (dogSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨0⟩ key))
      (by simp)
    simpa [slot, dogSlotWord] using hret'
  have hword : dogSlotWord slot σ_evm I = dogSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (dogSlotWord (wardsMappingSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (dogSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (dogSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (dogSlotWord slot σ_evm I).toNat))])
        wardsTransition.returnType := by
    rw [show wardsTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (dogSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem dogWardsBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some wardsTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨512⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨512⟩) (ret := ⟨448⟩)
    (decoded := ⟨534⟩) (need := ⟨32⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by decide +native)]; decide +native)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_wards_none_short (v := v) hsz4 hshort)

theorem dogWardsBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hpatch : patchRuntime dogBytecode (patches v) = some code)
    (_hcode : I.code = code)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hwv : I.weiValue = ⟨0⟩)
    (_hsel : selIs I (dogSelBytes 16))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 16) rfl _hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some wardsTransition :=
    dogDispatchWards _hsel
  have hreach := dogReachWardsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hpatch _hcode _hwv hsz4 _hsize _hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact dogWardsBodyCoreOk _hpatch _hcode _hwv hsz36 _hsize hdispatch
      (dogDecode_wards_ok (v := v) hsz36) hreach _hAccounts
  · exact dogWardsBodyCoreDecodeFailed_short _hpatch _hcode _hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog
