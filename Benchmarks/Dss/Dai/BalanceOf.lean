import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `balanceOf(address)` -/

abbrev balanceOfArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev balanceOfArgMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (balanceOfArgWord I)

abbrev balanceOfArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (balanceOfArgWord I).toNat)

abbrev balanceOfArgKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (balanceOfArgWord I).toNat)

abbrev balanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (balanceOfArgValue I)

def balanceOfStorageSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (balanceOfArgKey I)

def balanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (balanceOfStorageSlot I) ⟨0⟩)

theorem balanceOfStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    balanceOfStorageSlot I = mapSlot (balanceOfArgMaskedWord I) ⟨2⟩ := by
  unfold balanceOfStorageSlot balanceOfSlot balanceOfArgKey balanceOfArgMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem daiDecode_balanceOf_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = some (balanceOfStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = _
  simpa [balanceOfStore, balanceOfArgValue, balanceOfArgWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36

theorem daiDecode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0")
    hsz4 hshort

/-- The Solm `balanceOf(address)` body returns `balanceOf[arg0]`. -/
theorem daiBalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (balanceOfStore I) balanceOfTransition.body
      (.returned { contract := contract, locals := balanceOfStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (balanceOfStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := balanceOfStore I })
        (slot := balanceOfRef (.var "arg0"))
        (er := ({ base := "balanceOf", steps := [.mindex (balanceOfArgKey I)] } :
          EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (balanceOfStorageSlot I) (.int uint256Int))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (balanceOfStorageSlot I)).toNat))
        (hbase := by
          simp [balanceOfStore, balanceOfRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, balanceOfRef, balanceOfStore,
            balanceOfArgValue, balanceOfArgKey, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, balanceOfArgKey,
            uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (balanceOfStorageSlot I))])

/-! ## EVM trace -/

theorem daiBalanceOfX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨734⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2392⟩
        [balanceOfArgMaskedWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd756⟩ := RD.daiOneAddressExternalLenOk
    (entry := ⟨734⟩) (ret := ⟨524⟩) (routine := ⟨2392⟩) hreach
    dai_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd2392⟩ := RD.daiOneAddressExternalMaskAndJumpMasked
    (entry := ⟨734⟩) (ret := ⟨524⟩) (routine := ⟨2392⟩) (R := [sel])
    rd756 dai_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [balanceOfArgMaskedWord, balanceOfArgWord] using rd2392⟩

theorem daiBalanceOfX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨734⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiOneAddressExternalShort
    (entry := ⟨734⟩) (ret := ⟨524⟩) (routine := ⟨2392⟩)
    hreach dai_one_address_external_entry_wf hsz4 hsize hshort

theorem daiX_balanceOf_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨734⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  obtain ⟨_, _, rd2392⟩ := daiBalanceOfX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨k524, C524, rd524raw⟩ := RD.daiSingleMappingGetter (pc := ⟨2392⟩)
    (baseSlot := ⟨2⟩) (key := balanceOfArgMaskedWord I) (ret := ⟨524⟩) (R := [sel])
    rd2392 dai_single_mapping_getter_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have hslot := balanceOfStorageSlot_eq_mapSlot_masked I
  have hword :
      (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (mapSlot (balanceOfArgMaskedWord I) ⟨2⟩) ⟨0⟩))
        = balanceOfWord σ I := by
    unfold balanceOfWord
    rw [hslot]
  have rd524 : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩
      (balanceOfWord σ I :: ⟨524⟩ :: [sel])
      (daiMappingHashMem ⟨2⟩ (balanceOfArgMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k524 C524 := by
    simpa [hword] using rd524raw
  exact RD.daiReturnWordFromMem
    (val := balanceOfWord σ I) (ret := ⟨524⟩) (R := [sel])
    (mem := daiMappingHashMem ⟨2⟩ (balanceOfArgMaskedWord I))
    (memout := daiMappingReturnMem ⟨2⟩ (balanceOfArgMaskedWord I) (balanceOfWord σ I))
    rd524
    dai_return_word_from_mem_wf
    (daiMappingHashMem_mload64 ⟨2⟩ (balanceOfArgMaskedWord I))
    (by rfl)
    (daiMappingReturnMem_mload64 ⟨2⟩ (balanceOfArgMaskedWord I) (balanceOfWord σ I))
    (daiMappingReturnMem_read128 ⟨2⟩ (balanceOfArgMaskedWord I) (balanceOfWord σ I))
    (by simp only [List.length_singleton]; omega)

theorem daiBalanceOfBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some balanceOfTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (balanceOfTransition.params.map Param.name)
        (transitionSignature balanceOfTransition).paramTypes I.calldata = some (balanceOfStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨734⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : balanceOfWord σ_evm I = balanceOfWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (balanceOfStorageSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (balanceOfStore I)
        balanceOfTransition.body
        (.returned { contract := contract, locals := balanceOfStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (balanceOfWord σ_solm I).toNat))])) := by
    simpa [balanceOfWord, balanceOfStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiBalanceOfBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (daiX_balanceOf_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (balanceOfWord σ_evm I)))

theorem daiBalanceOfBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some balanceOfTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨734⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_balanceOf_none_short (I := I) hsz4 hshort
  exact (daiBalanceOfX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `balanceOf(address)` body refines its Solm transition. -/
theorem daiBalanceOfBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 2) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some balanceOfTransition :=
    daiDispatchBalanceOf hsel
  have hreach := daiReachBalanceOfBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact daiBalanceOfBodyCoreOk hcode hsize hwv hsz36 hdispatch
      (daiDecode_balanceOf_ok hsz36) hreach hAccounts
  · exact daiBalanceOfBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
