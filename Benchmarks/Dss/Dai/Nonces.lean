import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `nonces(address)` -/

abbrev noncesArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev noncesArgMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (noncesArgWord I)

abbrev noncesArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (noncesArgWord I).toNat)

abbrev noncesArgKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (noncesArgWord I).toNat)

abbrev noncesStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (noncesArgValue I)

def noncesStorageSlot (I : ExecutionEnv) : UInt256 :=
  noncesSlot (noncesArgKey I)

def noncesWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (noncesStorageSlot I) ⟨0⟩)

theorem noncesStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    noncesStorageSlot I = mapSlot (noncesArgMaskedWord I) ⟨4⟩ := by
  unfold noncesStorageSlot noncesSlot noncesArgKey noncesArgMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem daiDecode_nonces_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (noncesTransition.params.map Param.name)
      (transitionSignature noncesTransition).paramTypes I.calldata = some (noncesStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = _
  simpa [noncesStore, noncesArgValue, noncesArgWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36

theorem daiDecode_nonces_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (noncesTransition.params.map Param.name)
      (transitionSignature noncesTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

/-- The Solm `nonces(address)` body returns `nonces[arg0]`. -/
theorem daiNoncesBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (noncesStore I) noncesTransition.body
      (.returned { contract := contract, locals := noncesStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (noncesStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := noncesStore I })
        (slot := noncesRef (.var "arg0"))
        (er := ({ base := "nonces", steps := [.mindex (noncesArgKey I)] } :
          EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (noncesStorageSlot I) (.int uint256Int))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (noncesStorageSlot I)).toNat))
        (hbase := by
          simp [noncesStore, noncesRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, noncesRef, noncesStore,
            noncesArgValue, noncesArgKey, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, noncesArgKey,
            uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (noncesStorageSlot I))])

/-! ## EVM trace -/

theorem daiNoncesX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2410⟩
        [noncesArgMaskedWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd794⟩ := RD.daiOneAddressExternalLenOk
    (entry := ⟨772⟩) (ret := ⟨524⟩) (routine := ⟨2410⟩) hreach
    dai_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd2410⟩ := RD.daiOneAddressExternalMaskAndJumpMasked
    (entry := ⟨772⟩) (ret := ⟨524⟩) (routine := ⟨2410⟩) (R := [sel])
    rd794 dai_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [noncesArgMaskedWord, noncesArgWord] using rd2410⟩

theorem daiNoncesX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiOneAddressExternalShort
    (entry := ⟨772⟩) (ret := ⟨524⟩) (routine := ⟨2410⟩)
    hreach dai_one_address_external_entry_wf hsz4 hsize hshort

theorem daiX_nonces_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨772⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (noncesWord σ I)) := by
  obtain ⟨_, _, rd2410⟩ := daiNoncesX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨k524, C524, rd524raw⟩ := RD.daiSingleMappingGetter (pc := ⟨2410⟩)
    (baseSlot := ⟨4⟩) (key := noncesArgMaskedWord I) (ret := ⟨524⟩) (R := [sel])
    rd2410 dai_single_mapping_getter_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have hslot := noncesStorageSlot_eq_mapSlot_masked I
  have hword :
      (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (mapSlot (noncesArgMaskedWord I) ⟨4⟩) ⟨0⟩))
        = noncesWord σ I := by
    unfold noncesWord
    rw [hslot]
  have rd524 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩
      (noncesWord σ I :: ⟨524⟩ :: [sel])
      (daiMappingHashMem ⟨4⟩ (noncesArgMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k524 C524 := by
    simpa [hword] using rd524raw
  exact RD.daiReturnWordFromMem
    (val := noncesWord σ I) (ret := ⟨524⟩) (R := [sel])
    (mem := daiMappingHashMem ⟨4⟩ (noncesArgMaskedWord I))
    (memout := daiMappingReturnMem ⟨4⟩ (noncesArgMaskedWord I) (noncesWord σ I))
    rd524
    dai_return_word_from_mem_wf
    (daiMappingHashMem_mload64 ⟨4⟩ (noncesArgMaskedWord I))
    (by rfl)
    (daiMappingReturnMem_mload64 ⟨4⟩ (noncesArgMaskedWord I) (noncesWord σ I))
    (daiMappingReturnMem_read128 ⟨4⟩ (noncesArgMaskedWord I) (noncesWord σ I))
    (by simp only [List.length_singleton]; omega)

theorem daiNoncesBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some noncesTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (noncesTransition.params.map Param.name)
        (transitionSignature noncesTransition).paramTypes I.calldata = some (noncesStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨772⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : noncesWord σ_evm I = noncesWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (noncesStorageSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (noncesStore I)
        noncesTransition.body
        (.returned { contract := contract, locals := noncesStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (noncesWord σ_solm I).toNat))])) := by
    simpa [noncesWord, noncesStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiNoncesBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (daiX_nonces_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (noncesWord σ_evm I)))

theorem daiNoncesBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some noncesTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨772⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_nonces_none_short (I := I) hsz4 hshort
  exact (daiNoncesX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `nonces(address)` body refines its Solm transition. -/
theorem daiNoncesBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 10) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some noncesTransition :=
    daiDispatchNonces hsel
  have hreach := daiReachNoncesBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact daiNoncesBodyCoreOk hcode hsize hwv hsz36 hdispatch
      (daiDecode_nonces_ok hsz36) hreach hAccounts
  · exact daiNoncesBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
