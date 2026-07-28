import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

/-! ## `pie(address)` mapping getter (user savings dai, slot 1). Group @223 arm 1. -/

abbrev pieMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev pieMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev pieMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "pie", steps := [.mindex (.address (pieMappingArg I))] }

abbrev pieMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  pieSlot (.address (pieMappingArg I))

theorem pieMappingSlotFor_eq (I : ExecutionEnv) :
    pieMappingSlotFor I = solcMappingSlot ⟨1⟩ (pieMappingKey I) := by
  unfold pieMappingSlotFor pieMappingArg pieMappingKey pieSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem potDecode_pie_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (pieTransition.params.map Param.name)
      (transitionSignature pieTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (pieMappingArg I))) := by
  simpa [config, pieTransition, pieMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem potDecode_pie_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (pieTransition.params.map Param.name)
      (transitionSignature pieTransition).paramTypes I.calldata = none := by
  simpa [config, pieTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem potReachPieBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 11)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨303⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x0bebac86⟩ :=
    potSelWord_eq_of_beq I hsz 0x0b 0xeb 0xac 0x86 ⟨0x0bebac86⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc 1))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG223Body 1 (by omega) ⟨303⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by native_decide)

theorem potPieBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some pieTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (pieTransition.params.map Param.name)
        (transitionSignature pieTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (pieMappingArg I))))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨303⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := pieMappingKey I
  let slot := solcMappingSlot ⟨1⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (pieMappingArg I))
  have hslot : pieMappingSlotFor I = slot := by
    simp [slot, key, pieMappingSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals pieTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (potSlotWord (pieMappingSlotFor I) σ_solm I).toNat))])) := by
    simpa [pieTransition, pieMappingSlotFor, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, key] using
      potUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := pieRef (.var "arg0")) (er := pieMappingEvaledRef I)
        (slot := pieMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, pieRef])
        (by
          simp [pieMappingEvaledRef, pieMappingArg, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, pieRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, locals])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := potBytecode) (sel := sel) (entry := ⟨303⟩) (ret := ⟨341⟩)
    (decoded := ⟨325⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := potBytecode) (decoded := ⟨325⟩) (ret := ⟨341⟩) (routine := ⟨966⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcSingleMappingGetter
    (code := potBytecode) (pc := ⟨966⟩) (baseSlot := ⟨1⟩) (key := key) (ret := ⟨341⟩) (R := [sel])
    (by simpa [key, pieMappingKey] using hroutine)
    (by unfold solcSingleMappingGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret potBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (potSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := ⟨341⟩) (val := potSlotWord slot σ_evm I) (ret := ⟨341⟩) (R := [sel])
      (memout := solcScratchReturnMem (solcMappingHashMem ⟨1⟩ key)
        (potSlotWord slot σ_evm I))
      (by simpa [slot, potSlotWord] using hretPc)
      (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcMappingHashMem_mload64 ⟨1⟩ key)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (potSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨1⟩ key) (solcMappingHashMem_read64 ⟨1⟩ key))
      (by
        exact solcScratchReturnMem_read128 (potSlotWord slot σ_evm I)
          (solcMappingHashMem_size ⟨1⟩ key))
      (by simp)
    simpa [slot, potSlotWord] using hret'
  have hword : potSlotWord slot σ_evm I = potSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (potSlotWord (pieMappingSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (potSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (potSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (potSlotWord slot σ_evm I).toNat))])
        pieTransition.returnType := by
    rw [show pieTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (potSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem potPieBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some pieTransition)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨303⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := potBytecode) (sel := sel) (entry := ⟨303⟩) (ret := ⟨341⟩)
    (decoded := ⟨325⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (potDecode_pie_none_short hsz4 hshort)

theorem potPieBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 11) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some pieTransition := potDispatchPieMap hsel
  have hreach := potReachPieBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact potPieBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (potDecode_pie_ok hsz36) hreach hAccounts
  · exact potPieBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Pot
