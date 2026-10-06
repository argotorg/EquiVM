import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `can(address,address)` nested mapping getter -/

abbrev canSrcWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev canSrcMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (canSrcWord I)

abbrev canUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev canUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (canUsrWord I)

abbrev canSrcValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (canSrcWord I).toNat)

abbrev canUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (canUsrWord I).toNat)

abbrev canSrcKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (canSrcWord I).toNat)

abbrev canUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (canUsrWord I).toNat)

abbrev canStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (canSrcValue I)).insert "arg1" (canUsrValue I)

theorem canStore_index_arg0 (I : ExecutionEnv) :
    (canStore I)["arg0"] = canSrcValue I := by
  unfold canStore
  rw [Std.HashMap.getElem_insert]
  simp

def canStorageSlot (I : ExecutionEnv) : UInt256 :=
  canSlot (canSrcKey I) (canUsrKey I)

abbrev canEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "can", steps := [.mindex (canSrcKey I), .mindex (canUsrKey I)] }

theorem canStorageSlot_eq (I : ExecutionEnv) :
    canStorageSlot I = solcMappingSlot (solcMappingSlot ⟨1⟩ (canSrcMaskedWord I))
      (canUsrMaskedWord I) := by
  unfold canStorageSlot canSlot canOwnerSlot canSrcKey canUsrKey canSrcMaskedWord
    canUsrMaskedWord mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address_ofNat_mask]

theorem vatDecode_can_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (canTransition.params.map Param.name)
      (transitionSignature canTransition).paramTypes I.calldata = some (canStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = _
  simpa [canStore, canSrcValue, canUsrValue, canSrcWord, canUsrWord, calldataWord]
    using decodeCalldata_legacyAddress_legacyAddress_ok
      (cd := I.calldata) (x := "arg0") (y := "arg1") hsz68

theorem vatDecode_can_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (canTransition.params.map Param.name)
      (transitionSignature canTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_none_short
    (cd := I.calldata) (x := "arg0") (y := "arg1") hsz4 hshort

theorem vatReachCanBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 2)) :
    ∃ k C, RD vatBytecode I g (initState σ σ₀ g A I)
        ⟨711⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vatSelWord I = ⟨0x4538c4eb⟩ :=
    vatSelWord_eq_of_beq I hsz 0x45 0x38 0xc4 0xeb ⟨0x4538c4eb⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms321Body 0 (by omega) ⟨711⟩ hcode hwv hsz hsize
    hroot hlow hlowhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatCanBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some canTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (canTransition.params.map Param.name)
        (transitionSignature canTransition).paramTypes I.calldata = some (canStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨711⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let slot := solcMappingSlot (solcMappingSlot ⟨1⟩ (canSrcMaskedWord I)) (canUsrMaskedWord I)
  have hslot : canStorageSlot I = slot := by
    simp [slot, canStorageSlot_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (canStore I)
        canTransition.body
        (.returned { contract := contract, locals := canStore I }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt (canStorageSlot I) σ I).toNat))])) := by
    simpa [canTransition, canStorageSlot, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      vatUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (canStore I)
        (ref := canRef (.var "arg0") (.var "arg1")) (er := canEvaledRef I)
        (slot := canStorageSlot I)
        (by simp only [initState]; exact hwv) (by simp [canStore, canRef])
        (by
          simp [canEvaledRef, canSrcValue, canUsrValue, canSrcKey, canUsrKey,
            evalStorageRef, evalStorageRefStep, canRef, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?, canStore_index_arg0])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, canSrcKey,
          canUsrKey, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨711⟩) (ret := ⟨465⟩)
    (decoded := ⟨733⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcTwoAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨733⟩) (ret := ⟨465⟩) (routine := ⟨2439⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcNestedMappingGetter
    (code := vatBytecode) (pc := ⟨2439⟩) (baseSlot := ⟨1⟩)
    (owner := canSrcMaskedWord I) (spender := canUsrMaskedWord I)
    (ret := ⟨465⟩) (R := [sel])
    (by simpa [canSrcMaskedWord, canSrcWord, canUsrMaskedWord, canUsrWord] using hroutine)
    (by
      unfold solcNestedMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨465⟩) (val := solcSlotWordAt slot σ I) (ret := ⟨465⟩) (R := [sel])
      (memout := solcScratchReturnMem
        (solcNestedMappingHashMem ⟨1⟩ (canSrcMaskedWord I) (canUsrMaskedWord I))
        (solcSlotWordAt slot σ I))
      (by simpa [slot, solcSlotWordAt] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        simpa [slot] using
          solcNestedMappingHashMem_mload64 ⟨1⟩ (canSrcMaskedWord I) (canUsrMaskedWord I))
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (solcSlotWordAt slot σ I)
          (solcNestedMappingHashMem_size ⟨1⟩ (canSrcMaskedWord I) (canUsrMaskedWord I))
          (solcNestedMappingHashMem_read64 ⟨1⟩ (canSrcMaskedWord I) (canUsrMaskedWord I)))
      (by
        exact solcScratchReturnMem_read128 (solcSlotWordAt slot σ I)
          (solcNestedMappingHashMem_size ⟨1⟩ (canSrcMaskedWord I) (canUsrMaskedWord I)))
      (by simp)
    simpa [slot, solcSlotWordAt] using hret'
  rw [hslot] at hbody
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        canTransition.returnType := by
    rw [show canTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  exact hret.reEquivExecution hcode hdispatch hdecode hbody henc

theorem vatCanBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some canTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨711⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hdec := vatDecode_can_none_short (I := I) hsz4 hshort
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨711⟩) (ret := ⟨465⟩)
    (decoded := ⟨733⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch hdec

theorem vatCanBodyCore : VatBodyTheorem 2 := by
  intro σ σ₀ A I g hcode hsize _hperm hwv hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some canTransition :=
    vatDispatchCan hsel
  have hreach := vatReachCanBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact vatCanBodyCoreOk hcode hwv hsz68 hsize hdispatch
      (vatDecode_can_ok hsz68) hreach
  · exact vatCanBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
