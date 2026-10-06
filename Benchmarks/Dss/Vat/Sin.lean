import Benchmarks.Dss.Vat.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `sin(address)` mapping getter -/

abbrev sinMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev sinMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev sinMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sin", steps := [.mindex (.address (sinMappingArg I))] }

abbrev sinMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  sinSlot (.address (sinMappingArg I))

theorem sinMappingSlotFor_eq (I : ExecutionEnv) :
    sinMappingSlotFor I = solcMappingSlot ⟨6⟩ (sinMappingKey I) := by
  unfold sinMappingSlotFor sinMappingArg sinMappingKey sinSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem vatDecode_sin_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (sinTransition.params.map Param.name)
      (transitionSignature sinTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (sinMappingArg I))) := by
  simpa [config, sinTransition, sinMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem vatDecode_sin_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (sinTransition.params.map Param.name)
      (transitionSignature sinTransition).paramTypes I.calldata = none := by
  simpa [config, sinTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem vatReachSinBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 22)) :
    ∃ k C, RD vatBytecode I g (initState σ σ₀ g A I)
        ⟨1505⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vatSelWord I = ⟨0xf059212a⟩ :=
    vatSelWord_eq_of_beq I hsz 0xf0 0x59 0x21 0x2a ⟨0xf059212a⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms65Body 1 (by omega) ⟨1505⟩ hcode hwv hsz hsize
    hroot hhigh hhighhigh heq0 htake (by jump_dest) (by native_decide)

theorem vatSinBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some sinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (sinTransition.params.map Param.name)
        (transitionSignature sinTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (sinMappingArg I))))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let key := sinMappingKey I
  let slot := solcMappingSlot ⟨6⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (sinMappingArg I))
  have hslot : sinMappingSlotFor I = slot := by
    simp [slot, key, sinMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals sinTransition.body
        (.returned { contract := contract, locals := locals }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vatSlotWord (sinMappingSlotFor I) σ I).toNat))])) := by
    simpa [sinTransition, sinMappingSlotFor, vatSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      vatUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := sinRef (.var "arg0")) (er := sinMappingEvaledRef I)
        (slot := sinMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, sinRef])
        (by
          simp [sinMappingEvaledRef, sinMappingArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, sinRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1505⟩) (ret := ⟨465⟩)
    (decoded := ⟨1527⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨1527⟩) (ret := ⟨465⟩) (routine := ⟨6172⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := vatBytecode) (pc := ⟨6172⟩) (baseSlot := ⟨6⟩)
    (key := key) (ret := ⟨465⟩) (R := [sel])
    (by simpa [key, sinMappingKey] using hroutine)
    (by
      unfold solcSingleMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (vatSlotWord slot σ I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨465⟩) (val := vatSlotWord slot σ I) (ret := ⟨465⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨6⟩ key)
        (vatSlotWord slot σ I))
      (by simpa [slot, vatSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨6⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (vatSlotWord slot σ I)
          (solcMappingHashMem_size ⟨6⟩ key) (solcMappingHashMem_read64 ⟨6⟩ key))
      (by
        exact solcScratchReturnMem_read128 (vatSlotWord slot σ I)
          (solcMappingHashMem_size ⟨6⟩ key))
      (by simp)
    simpa [slot, vatSlotWord] using hret'
  rw [hslot] at hbody
  have henc :
      returnEquiv (UInt256.toByteArray (vatSlotWord slot σ I))
        (some [(.int (Int.ofNat (vatSlotWord slot σ I).toNat))])
        sinTransition.returnType := by
    rw [show sinTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (vatSlotWord slot σ I))
  exact hret.reEquivExecution hcode hdispatch hdecode hbody henc

theorem vatSinBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some sinTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1505⟩) (ret := ⟨465⟩)
    (decoded := ⟨1527⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (vatDecode_sin_none_short hsz4 hshort)

theorem vatSinBodyCore : VatBodyTheoremAnyPerm 22 := by
  intro σ σ₀ A I g hcode hsize hwv hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 22) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some sinTransition :=
    vatDispatchSin hsel
  have hreach := vatReachSinBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatSinBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (vatDecode_sin_ok hsz36) hreach
  · exact vatSinBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
