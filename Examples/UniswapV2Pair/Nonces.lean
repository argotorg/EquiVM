import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `nonces(address)` success slice -/

/-- The raw ABI word for `nonces`'s `owner` argument. -/
abbrev noncesOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev noncesOwnerMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (noncesOwnerWord I)

abbrev noncesOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (noncesOwnerWord I).toNat)

abbrev noncesOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (noncesOwnerWord I).toNat)

abbrev noncesStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (noncesOwnerValue I)

def noncesStorageSlot (I : ExecutionEnv) : UInt256 :=
  nonceSlot (noncesOwnerKey I)

def noncesWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (noncesStorageSlot I) ⟨0⟩)

theorem noncesStorageSlot_eq_mapSlot (I : ExecutionEnv)
    (hcanon : (noncesOwnerWord I).toNat < EVM.addressModulus) :
    noncesStorageSlot I = mapSlot (noncesOwnerWord I) ⟨4⟩ := by
  unfold noncesStorageSlot nonceSlot noncesOwnerKey
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem noncesStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    noncesStorageSlot I = mapSlot (noncesOwnerMaskedWord I) ⟨4⟩ := by
  unfold noncesStorageSlot nonceSlot noncesOwnerKey noncesOwnerMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem uniswapDecode_nonces_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldata (noncesTransition.params.map Param.name)
      (transitionSignature noncesTransition).paramTypes I.calldata = some (noncesStore I) := by
  show decodeCalldata ["owner"] [legacyAddr] I.calldata = _
  simpa [noncesStore, noncesOwnerValue, noncesOwnerWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "owner") hsz36

theorem uniswapDecode_nonces_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (noncesTransition.params.map Param.name)
      (transitionSignature noncesTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [legacyAddr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "owner")
    hsz4 hshort

/-- The Solm `nonces(address)` body returns `nonces[owner]`. -/
theorem uniswapNoncesBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (noncesStore I) noncesTransition.body
      (.returned { contract := contract, locals := noncesStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (noncesStorageSlot I)).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (er := ({ base := "nonces", steps := [.mindex (noncesOwnerKey I)] } :
          EvaledStorageRef))
        (loc := wordLoc (noncesStorageSlot I))
        (hbase := by simp [noncesStore, noncesRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, noncesRef, noncesStore,
            noncesOwnerValue, noncesOwnerKey, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by rfl)
        (hloc := by rfl)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm (noncesStorageSlot I)))

/-! ## EVM trace -/

/-- The optimized external wrapper for `nonces(address)` masks the address calldata word and jumps
    to the shared mapping getter routine at pc 4075. -/
theorem uniswapNoncesX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1125⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4075⟩
        [noncesOwnerMaskedWord I, ⟨861⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1147⟩ := RD.uniswapOneAddressGetterLenOk
    (entry := ⟨1125⟩) (routine := ⟨4075⟩) hreach
    uniswap_one_address_getter_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd4075⟩ := RD.uniswapOneAddressGetterMaskAndJumpMasked
    (entry := ⟨1125⟩) (routine := ⟨4075⟩) (R := [sel]) rd1147
    uniswap_one_address_getter_entry_wf
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [noncesOwnerMaskedWord, noncesOwnerWord] using rd4075⟩

/-- Short-calldata path for `nonces(address)` from the dispatcher body entry.

This covers calldata with a selector present but fewer than one ABI word. The dispatcher-level
`calldatasize < 4` branch remains in `Correct.lean`.
-/
theorem uniswapNoncesX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1125⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapOneAddressGetterShort
    (entry := ⟨1125⟩) (routine := ⟨4075⟩)
    hreach uniswap_one_address_getter_entry_wf hsz4 hsize hshort

/-- The EVM `nonces(address)` success path loads the explicit mapping slot and returns it. -/
theorem uniswapX_nonces_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1125⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (noncesWord σ I)) := by
  obtain ⟨_, _, rd4075⟩ := uniswapNoncesX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨k861, C861, rd861raw⟩ := RD.uniswapSingleMappingGetter (pc := ⟨4075⟩)
    (baseSlot := ⟨4⟩) (key := noncesOwnerMaskedWord I) (ret := ⟨861⟩) (R := [sel])
    rd4075 uniswap_single_mapping_getter_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have hslot := noncesStorageSlot_eq_mapSlot_masked I
  have hword :
      (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (mapSlot (noncesOwnerMaskedWord I) ⟨4⟩) ⟨0⟩))
        = noncesWord σ I := by
    unfold noncesWord
    rw [hslot]
  have rd861 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨861⟩
      (noncesWord σ I :: ⟨861⟩ :: [sel])
      (uniswapMappingHashMem ⟨4⟩ (noncesOwnerMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k861 C861 := by
    simpa [hword] using rd861raw
  exact RD.uniswapReturnWord861FromMem
    (val := noncesWord σ I) (ret := ⟨861⟩) (R := [sel])
    (mem := uniswapMappingHashMem ⟨4⟩ (noncesOwnerMaskedWord I))
    (memout := uniswapMappingReturnMem ⟨4⟩ (noncesOwnerMaskedWord I) (noncesWord σ I))
    rd861
    (uniswapMappingHashMem_mload64 ⟨4⟩ (noncesOwnerMaskedWord I))
    (by rfl)
    (uniswapMappingReturnMem_mload64 ⟨4⟩ (noncesOwnerMaskedWord I) (noncesWord σ I))
    (uniswapMappingReturnMem_read128 ⟨4⟩ (noncesOwnerMaskedWord I) (noncesWord σ I))
    (by simp only [List.length_singleton]; omega)

/-- Success refinement slice for `nonces(address)`, including masked noncanonical address calldata
words. -/
theorem uniswapNoncesBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some noncesTransition)
    (hdecode :
      decodeCalldata (noncesTransition.params.map Param.name)
        (transitionSignature noncesTransition).paramTypes I.calldata = some (noncesStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1125⟩ [sel]
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
          (some (.int (Int.ofNat (noncesWord σ_solm I).toNat)))) := by
    simpa [noncesWord, noncesStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapNoncesBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (uniswapX_nonces_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (noncesWord σ_evm I)))

/-- Short-calldata decode-failure refinement slice for `nonces(address)`.

The non-canonical and huge-calldata branches are intentionally not claimed here: the optimized
bytecode masks address words and uses an unsigned static length check, and the `legacyAddr` ABI
annotation models that behavior.
-/
theorem uniswapNoncesBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some noncesTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1125⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_nonces_none_short (I := I) hsz4 hshort
  exact (uniswapNoncesX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- Success `nonces(address)` refinement slice, packaged from selector dispatch through the body
core. -/
theorem uniswapNoncesBodyOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some noncesTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩ rfl hsel
  exact uniswapNoncesBodyCoreOk hcode hsize hwv hsz36 hdispatch
    (uniswapDecode_nonces_ok hsz36)
    (uniswapReachNoncesBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Short-calldata decode-failure `nonces(address)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapNoncesBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩)
    (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some noncesTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩ rfl hsel
  exact uniswapNoncesBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachNoncesBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapNoncesBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some noncesTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact uniswapNoncesBodyOk hcode hsize hwv hsel hsz36 hdispatch hAccounts
  · exact uniswapNoncesBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
