import Tests.Pipeline.VyperRegistry.Helpers

variable {fork : Ethereum.Fork}

/-!
# Registry `totalWeight()`

Dispatcher bucket 3, arm entry pc 1407: the `callvalue` guard and the `uint256` getter of slot 20.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

theorem totalWeightBody_eq : totalWeightTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage { base := "totalWeight", steps := [] }]] := by rfl

/-- `totalWeight()`: the theorem `Correct.lean` routes selector 7 to. -/
theorem registryTotalWeightBody {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 7)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 7) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachTotalWeightBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some totalWeightTransition :=
    registryDispatch_totalWeight (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (totalWeightTransition.params.map Param.name)
      (transitionSignature totalWeightTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, totalWeightTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := registryBlocks.registry_block_1407_fallthrough (by simp) (by rw [hwv]; rfl) rd
    have rd2 := registryBlocks.registry_block_1412 (by simp) rd1
    have hmemsize : (registryDispatchMem 3).size = 32 := dispatchMem_size 3 (by decide)
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (registryDispatchMem 3) 64
        (by rw [hmemsize]; exact lt_usize _ (by decide)), slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        totalWeightTransition.body
        (.returned (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [uint256Value (solcSlotWordAt (UInt256.ofNat 20) σ I)])) := by
      rw [totalWeightBody_eq]
      refine ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
      rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
          (er := { base := "totalWeight", steps := [] }) (physicalSlot := UInt256.ofNat 20) (hbase := by simp)
          (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
          (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
        storageLoad_initState_ofUInt256_solcSlotWordAt]
    exact rd2.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
  · have rd1 := registryBlocks.registry_block_1407_taken (by simp) (fun h => hwv h) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd (fun _ => by rw [totalWeightBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperRegistry
