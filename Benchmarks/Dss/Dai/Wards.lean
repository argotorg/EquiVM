import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `wards(address)` -/

/-- The raw ABI word for `wards`'s `arg0` argument. -/
abbrev wardsArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev wardsArgMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (wardsArgWord I)

abbrev wardsArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (wardsArgWord I).toNat)

abbrev wardsArgKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (wardsArgWord I).toNat)

abbrev wardsStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (wardsArgValue I)

def wardsStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (wardsArgKey I)

def wardsWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (wardsStorageSlot I) ⟨0⟩)

theorem wardsStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    wardsStorageSlot I = mapSlot (wardsArgMaskedWord I) ⟨0⟩ := by
  unfold wardsStorageSlot wardsSlot wardsArgKey wardsArgMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem daiDecode_wards_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = some (wardsStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = _
  simpa [wardsStore, wardsArgValue, wardsArgWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36

theorem daiDecode_wards_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

/-- The Solm `wards(address)` body returns `wards[arg0]`. -/
theorem daiWardsBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (wardsStore I) wardsTransition.body
      (.returned { contract := contract, locals := wardsStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (wardsStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := wardsStore I })
        (slot := wardsRef (.var "arg0"))
        (er := ({ base := "wards", steps := [.mindex (wardsArgKey I)] } :
          EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (wardsStorageSlot I) (.int uint256Int))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (wardsStorageSlot I)).toNat))
        (hbase := by
          simp [wardsStore, wardsRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, wardsRef, wardsStore,
            wardsArgValue, wardsArgKey, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, wardsArgKey,
            uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (wardsStorageSlot I))])

/-! ## EVM trace -/

theorem daiWardsX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1132⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3908⟩
        [wardsArgMaskedWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1154⟩ := RD.daiOneAddressExternalLenOk
    (entry := ⟨1132⟩) (ret := ⟨524⟩) (routine := ⟨3908⟩) hreach
    dai_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd3908⟩ := RD.daiOneAddressExternalMaskAndJumpMasked
    (entry := ⟨1132⟩) (ret := ⟨524⟩) (routine := ⟨3908⟩) (R := [sel])
    rd1154 dai_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [wardsArgMaskedWord, wardsArgWord] using rd3908⟩

theorem daiWardsX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1132⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiOneAddressExternalShort
    (entry := ⟨1132⟩) (ret := ⟨524⟩) (routine := ⟨3908⟩)
    hreach dai_one_address_external_entry_wf hsz4 hsize hshort

theorem daiX_wards_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1132⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (wardsWord σ I)) := by
  obtain ⟨_, _, rd3908⟩ := daiWardsX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨k524, C524, rd524raw⟩ := RD.daiZeroSlotSingleMappingGetter (pc := ⟨3908⟩)
    (key := wardsArgMaskedWord I) (ret := ⟨524⟩) (R := [sel])
    rd3908 dai_zero_slot_single_mapping_getter_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have hslot := wardsStorageSlot_eq_mapSlot_masked I
  have hword :
      (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (mapSlot (wardsArgMaskedWord I) ⟨0⟩) ⟨0⟩))
        = wardsWord σ I := by
    unfold wardsWord
    rw [hslot]
  have rd524 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩
      (wardsWord σ I :: ⟨524⟩ :: [sel])
      (daiMappingHashMem ⟨0⟩ (wardsArgMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k524 C524 := by
    simpa [hword] using rd524raw
  exact RD.daiReturnWordFromMem
    (val := wardsWord σ I) (ret := ⟨524⟩) (R := [sel])
    (mem := daiMappingHashMem ⟨0⟩ (wardsArgMaskedWord I))
    (memout := daiMappingReturnMem ⟨0⟩ (wardsArgMaskedWord I) (wardsWord σ I))
    rd524
    dai_return_word_from_mem_wf
    (daiMappingHashMem_mload64 ⟨0⟩ (wardsArgMaskedWord I))
    (by rfl)
    (daiMappingReturnMem_mload64 ⟨0⟩ (wardsArgMaskedWord I) (wardsWord σ I))
    (daiMappingReturnMem_read128 ⟨0⟩ (wardsArgMaskedWord I) (wardsWord σ I))
    (by simp only [List.length_singleton]; omega)

theorem daiWardsBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
        (transitionSignature wardsTransition).paramTypes I.calldata = some (wardsStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1132⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : wardsWord σ_evm I = wardsWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (wardsStorageSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (wardsStore I)
        wardsTransition.body
        (.returned { contract := contract, locals := wardsStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (wardsWord σ_solm I).toNat))])) := by
    simpa [wardsWord, wardsStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiWardsBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (daiX_wards_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (wardsWord σ_evm I)))

theorem daiWardsBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1132⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_wards_none_short (I := I) hsz4 hshort
  exact (daiWardsX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `wards(address)` body refines its Solm transition. -/
theorem daiWardsBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 21))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 21) (by decide +native) hsel
  have hdispatch : dispatchMsg contract I.calldata = some wardsTransition :=
    daiDispatchWards hsel
  have hreach := daiReachWardsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact daiWardsBodyCoreOk hcode hsize hwv hsz36 hdispatch
      (daiDecode_wards_ok hsz36) hreach hAccounts
  · exact daiWardsBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Dai
