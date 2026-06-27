import Examples.UniswapV2Pair.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `balanceOf(address)` canonical-success slice -/

/-- The raw ABI word for `balanceOf`'s `owner` argument. -/
abbrev balanceOfOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev balanceOfOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)

abbrev balanceOfOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)

abbrev balanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (balanceOfOwnerValue I)

def balanceOfStorageSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (balanceOfOwnerKey I)

def balanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (balanceOfStorageSlot I) ⟨0⟩)

theorem balanceOfStorageSlot_eq_mapSlot (I : ExecutionEnv)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    balanceOfStorageSlot I = mapSlot (balanceOfOwnerWord I) ⟨1⟩ := by
  unfold balanceOfStorageSlot balanceOfSlot balanceOfOwnerKey
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem uniswapDecode_balanceOf_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = some (balanceOfStore I) := by
  show decodeCalldata ["owner"] [addr] I.calldata = _
  simpa [balanceOfStore, balanceOfOwnerValue, balanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "owner") hsz36 hbig hcanon

theorem uniswapDecode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short (cd := I.calldata) (x := "owner")
    hsz4 hshort

theorem uniswapDecode_balanceOf_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr, balanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "owner") hsz36 hbig hnc

theorem uniswapDecode_balanceOf_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge (cd := I.calldata) (x := "owner") hbig

/-- The Solm `balanceOf(address)` body returns `balanceOf[owner]`. -/
theorem uniswapBalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (balanceOfStore I) balanceOfTransition.body
      (.returned { contract := contract, locals := balanceOfStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (balanceOfStorageSlot I)).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (er := ({ base := "balanceOf", steps := [.mindex (balanceOfOwnerKey I)] } :
          EvaledStorageRef))
        (loc := wordLoc (balanceOfStorageSlot I))
        (hbase := by simp [balanceOfStore, balanceOfRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, balanceOfRef, balanceOfStore,
            balanceOfOwnerValue, balanceOfOwnerKey, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by rfl)
        (hloc := by rfl)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm (balanceOfStorageSlot I)))

/-! ## EVM trace -/

/-- The optimized external wrapper for `balanceOf(address)` accepts canonical calldata and jumps to
    the shared mapping getter routine at pc 4051. -/
theorem uniswapBalanceOfX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1079⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4051⟩
        [balanceOfOwnerWord I, ⟨861⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1101⟩ := RD.uniswapOneAddressGetterLenOk
    (entry := ⟨1079⟩) (routine := ⟨4051⟩) hreach
    uniswap_one_address_getter_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd4051⟩ := RD.uniswapOneAddressGetterMaskAndJump
    (entry := ⟨1079⟩) (routine := ⟨4051⟩) (R := [sel]) rd1101
    uniswap_one_address_getter_entry_wf (by simpa [balanceOfOwnerWord] using hcanon)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [balanceOfOwnerWord] using rd4051⟩

/-- The EVM `balanceOf(address)` success path loads the explicit mapping slot and returns it. -/
theorem uniswapX_balanceOf_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1079⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  obtain ⟨_, _, rd4051⟩ := uniswapBalanceOfX_decoded (g := g) hsz36 hsize hcanon hreach
  obtain ⟨k861, C861, rd861raw⟩ := RD.uniswapSingleMappingGetter (pc := ⟨4051⟩)
    (baseSlot := ⟨1⟩) (key := balanceOfOwnerWord I) (ret := ⟨861⟩) (R := [sel])
    rd4051 uniswap_single_mapping_getter_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  have hslot := balanceOfStorageSlot_eq_mapSlot I hcanon
  have hword :
      (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (mapSlot (balanceOfOwnerWord I) ⟨1⟩) ⟨0⟩))
        = balanceOfWord σ I := by
    unfold balanceOfWord
    rw [hslot]
  have rd861 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨861⟩
      (balanceOfWord σ I :: ⟨861⟩ :: [sel])
      (uniswapMappingHashMem ⟨1⟩ (balanceOfOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k861 C861 := by
    simpa [hword] using rd861raw
  exact RD.uniswapReturnWord861FromMem
    (val := balanceOfWord σ I) (ret := ⟨861⟩) (R := [sel])
    (mem := uniswapMappingHashMem ⟨1⟩ (balanceOfOwnerWord I))
    (memout := uniswapMappingReturnMem ⟨1⟩ (balanceOfOwnerWord I) (balanceOfWord σ I))
    rd861
    (uniswapMappingHashMem_mload64 ⟨1⟩ (balanceOfOwnerWord I))
    (by rfl)
    (uniswapMappingReturnMem_mload64 ⟨1⟩ (balanceOfOwnerWord I) (balanceOfWord σ I))
    (uniswapMappingReturnMem_read128 ⟨1⟩ (balanceOfOwnerWord I) (balanceOfWord σ I))
    (by simp only [List.length_singleton]; omega)

/-- Canonical-success refinement slice for `balanceOf(address)`.

The non-canonical address case is intentionally not claimed here: the optimized bytecode masks the
address word, while the current ABI decoder rejects non-canonical address encodings.
-/
theorem uniswapBalanceOfBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (_hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hdispatch : dispatchMsg contract I.calldata = some balanceOfTransition)
    (hdecode :
      decodeCalldata (balanceOfTransition.params.map Param.name)
        (transitionSignature balanceOfTransition).paramTypes I.calldata = some (balanceOfStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1079⟩ [sel]
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
          (some (.int (Int.ofNat (balanceOfWord σ_solm I).toNat)))) := by
    simpa [balanceOfWord, balanceOfStorageSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      uniswapBalanceOfBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (uniswapX_balanceOf_ok (g := Sat256.ofUInt256 g) hsz36 hsize hcanon hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (balanceOfWord σ_evm I)))

end UniswapV2Pair
