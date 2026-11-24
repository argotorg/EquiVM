import Tests.Pipeline.VyperRegistry.Helpers

variable {fork : Ethereum.Fork}

/-!
# Registry `owner()`

Dispatcher bucket 5, arm entry pc 403: the `callvalue` guard and the raw `ownable_owner` word
(slot 0), an address word under `storageWF`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

theorem ownerBody_eq : ownerTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage ownerRef]] := by rfl

/-- `owner()`: the theorem `Correct.lean` routes selector 5 to. -/
theorem registryOwnerBody {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 5)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 5) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachOwnerBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some ownerTransition :=
    registryDispatch_owner (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (ownerTransition.params.map Param.name)
      (transitionSignature ownerTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, ownerTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := registryBlocks.registry_block_403_fallthrough (by simp) (by rw [hwv]; rfl) rd
    have rd2 := registryBlocks.registry_block_408 (by simp) rd1
    have hmemsize : (registryDispatchMem 5).size = 32 := dispatchMem_size 5 (by decide)
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (registryDispatchMem 5) 64
        (by rw [hmemsize]; exact lt_usize _ (by decide)), slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        ownerTransition.body
        (.returned (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address (AccountAddress.ofNat (solcSlotWordAt ⟨0⟩ σ I).toNat)])) := by
      rw [ownerBody_eq]
      refine ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
      rw [evalOwnerRead _ (by simp), storageLoad_initState_ofUInt256_solcSlotWordAt]
    refine rd2.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode ?_)
    rw [addressReturnEncoding]
    show some (UInt256.toByteArray (UInt256.ofNat (AccountAddress.ofNat _).val)) = _
    rw [word_roundtrip hwf.1]
  · have rd1 := registryBlocks.registry_block_403_taken (by simp) (fun h => hwv h) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd (fun _ => by rw [ownerBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperRegistry
