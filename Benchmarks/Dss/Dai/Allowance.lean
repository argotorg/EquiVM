import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `allowance(address,address)` -/

abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev allowanceOwnerMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (allowanceOwnerWord I)

abbrev allowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev allowanceSpenderMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (allowanceSpenderWord I)

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (allowanceOwnerValue I)).insert "arg1"
    (allowanceSpenderValue I)

theorem allowanceStore_get_arg0 (I : ExecutionEnv) :
    (allowanceStore I).get? "arg0" = some (allowanceOwnerValue I) := by
  unfold allowanceStore
  rw [store_get_ne
    (L := (∅ : Store).insert "arg0" (allowanceOwnerValue I))
    (k := "arg1") (a := "arg0") (allowanceSpenderValue I) (by decide +native)]
  simp

theorem allowanceStore_get_arg1 (I : ExecutionEnv) :
    (allowanceStore I).get? "arg1" = some (allowanceSpenderValue I) := by
  unfold allowanceStore
  simp

theorem allowanceStore_index_arg0 (I : ExecutionEnv) :
    (allowanceStore I)["arg0"] = allowanceOwnerValue I := by
  unfold allowanceStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem allowanceStore_index_arg1 (I : ExecutionEnv) :
    (allowanceStore I)["arg1"] = allowanceSpenderValue I := by
  unfold allowanceStore
  rw [Std.HashMap.getElem_insert]
  simp

def allowanceStorageSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (allowanceOwnerKey I) (allowanceSpenderKey I)

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (allowanceStorageSlot I) ⟨0⟩)

abbrev allowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (allowanceOwnerKey I), .mindex (allowanceSpenderKey I)] }

theorem allowanceStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    allowanceStorageSlot I =
      mapSlot (allowanceSpenderMaskedWord I) (mapSlot (allowanceOwnerMaskedWord I) ⟨3⟩) := by
  unfold allowanceStorageSlot allowanceSlot allowanceOwnerSlot allowanceOwnerKey
    allowanceSpenderKey allowanceOwnerMaskedWord allowanceSpenderMaskedWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address_ofNat_mask]

theorem daiDecode_allowance_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata =
        some (allowanceStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = _
  simpa [allowanceStore, allowanceOwnerValue, allowanceSpenderValue, allowanceOwnerWord,
    allowanceSpenderWord, calldataWord]
    using decodeCalldata_legacyAddress_legacyAddress_ok
      (cd := I.calldata) (x := "arg0") (y := "arg1") hsz68

theorem daiDecode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [addr, addr]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_none_short
    (cd := I.calldata) (x := "arg0") (y := "arg1") hsz4 hshort

/-- The Solm `allowance(address,address)` body returns `allowance[arg0][arg1]`. -/
theorem daiAllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (allowanceStore I) allowanceTransition.body
      (.returned { contract := contract, locals := allowanceStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (allowanceStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := allowanceStore I })
        (slot := allowanceRef (.var "arg0") (.var "arg1"))
        (er := allowanceEvaledRef I)
        (t := .int uint256Int)
        (loc := wordLoc (allowanceStorageSlot I) (.int uint256Int))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (allowanceStorageSlot I)).toNat))
        (hbase := by
          simp [allowanceStore, allowanceRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, allowanceRef, allowanceEvaledRef,
            allowanceOwnerValue, allowanceSpenderValue, allowanceOwnerKey,
            allowanceSpenderKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
            bind, pure, evalExpr?, allowanceStore_index_arg0])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, allowanceOwnerKey,
            allowanceSpenderKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (allowanceStorageSlot I))])

/-! ## EVM trace -/

theorem daiAllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1170⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3926⟩
        [allowanceSpenderMaskedWord I, allowanceOwnerMaskedWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1192⟩ := RD.daiTwoAddressExternalLenOk
    (entry := ⟨1170⟩) (ret := ⟨524⟩) (routine := ⟨3926⟩) hreach
    dai_two_address_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd3926⟩ := RD.daiTwoAddressExternalMaskAndJumpMasked
    (entry := ⟨1170⟩) (ret := ⟨524⟩) (routine := ⟨3926⟩) (R := [sel])
    rd1192 dai_two_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [allowanceSpenderMaskedWord, allowanceSpenderWord, allowanceOwnerMaskedWord,
      allowanceOwnerWord] using rd3926⟩

theorem daiAllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1170⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiTwoAddressExternalShort
    (entry := ⟨1170⟩) (ret := ⟨524⟩) (routine := ⟨3926⟩)
    hreach dai_two_address_external_entry_wf hsz4 hsize hshort

theorem daiX_allowance_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1170⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  obtain ⟨_, _, rd3926⟩ := daiAllowanceX_decoded (g := g) hsz68 hsize hreach
  obtain ⟨k524, C524, rd524raw⟩ := RD.daiNestedMappingGetter (pc := ⟨3926⟩)
    (baseSlot := ⟨3⟩) (owner := allowanceOwnerMaskedWord I)
    (spender := allowanceSpenderMaskedWord I) (ret := ⟨524⟩) (R := [sel])
    rd3926 dai_nested_mapping_getter_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have hslot := allowanceStorageSlot_eq_mapSlot_masked I
  have hword :
      (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD
            (mapSlot (allowanceSpenderMaskedWord I)
              (mapSlot (allowanceOwnerMaskedWord I) ⟨3⟩)) ⟨0⟩))
        = allowanceWord σ I := by
    unfold allowanceWord
    rw [hslot]
  have rd524 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩
      (allowanceWord σ I :: ⟨524⟩ :: [sel])
      (daiNestedMappingHashMem ⟨3⟩ (allowanceOwnerMaskedWord I)
        (allowanceSpenderMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k524 C524 := by
    simpa [hword] using rd524raw
  exact RD.daiReturnWordFromMem
    (val := allowanceWord σ I) (ret := ⟨524⟩) (R := [sel])
    (mem := daiNestedMappingHashMem ⟨3⟩ (allowanceOwnerMaskedWord I)
      (allowanceSpenderMaskedWord I))
    (memout := daiNestedMappingReturnMem ⟨3⟩ (allowanceOwnerMaskedWord I)
      (allowanceSpenderMaskedWord I) (allowanceWord σ I))
    rd524
    dai_return_word_from_mem_wf
    (daiNestedMappingHashMem_mload64 ⟨3⟩ (allowanceOwnerMaskedWord I)
      (allowanceSpenderMaskedWord I))
    (by rfl)
    (daiNestedMappingReturnMem_mload64 ⟨3⟩ (allowanceOwnerMaskedWord I)
      (allowanceSpenderMaskedWord I) (allowanceWord σ I))
    (daiNestedMappingReturnMem_read128 ⟨3⟩ (allowanceOwnerMaskedWord I)
      (allowanceSpenderMaskedWord I) (allowanceWord σ I))
    (by simp only [List.length_singleton]; omega)

theorem daiAllowanceBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some allowanceTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (allowanceTransition.params.map Param.name)
        (transitionSignature allowanceTransition).paramTypes I.calldata =
          some (allowanceStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1170⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceStorageSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (allowanceStore I)
        allowanceTransition.body
        (.returned { contract := contract, locals := allowanceStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (allowanceWord σ_solm I).toNat))])) := by
    simpa [allowanceWord, allowanceStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiAllowanceBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (daiX_allowance_ok (g := Sat256.ofUInt256 g) hsz68 hsize hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (allowanceWord σ_evm I)))

theorem daiAllowanceBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some allowanceTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1170⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_allowance_none_short (I := I) hsz4 hshort
  exact (daiAllowanceX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `allowance(address,address)` body refines its Solm transition. -/
theorem daiAllowanceBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 0) (by decide +native) hsel
  have hdispatch : dispatchMsg contract I.calldata = some allowanceTransition :=
    daiDispatchAllowance hsel
  have hreach := daiReachAllowanceBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact daiAllowanceBodyCoreOk hcode hsize hwv hsz68 hdispatch
      (daiDecode_allowance_ok hsz68) hreach hAccounts
  · exact daiAllowanceBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
