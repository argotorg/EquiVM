import Tests.Pipeline.VyperRegistry.Helpers

variable {fork : Ethereum.Fork}

/-!
# Registry `count()`

Dispatcher bucket 3, arm entry pc 1379: the `callvalue` guard and `return len(self.ids)`, the raw
length word (slot 2), which the backend reads raw as well.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

theorem countBody_eq : countTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.arrayLength .storage { base := "ids", steps := [] }]] := by rfl

/-- `len(self.ids)` at the initial state. -/
theorem evalIdsLength {σ σ₀ A I} {g : UInt256} (L : Store) (hL : L.get? "ids" = none) :
    evalExpr? config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.arrayLength .storage { base := "ids", steps := [] }) =
      .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 2) σ I)) := by
  rw [evalExpr_arrayLength_vyper (hbackend := rfl) (hcheck := by rfl) (hbase := hL)
      (er := { base := "ids", steps := [] }) (elem := .elem (.int (.uint ⟨256, by decide⟩))) (cap := 16)
      (s := UInt256.ofNat 2)
      (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide)
      (hbounds := rfl) (hanchor := rfl),
    storageLoad_initState_ofUInt256_solcSlotWordAt]

/-- `count()`: the theorem `Correct.lean` routes selector 0 to. -/
theorem registryCountBody {σ σ₀ A I} {g : UInt256} (_hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 0)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 0) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachCountBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some countTransition := registryDispatch_count hsel
  have hdec : config.externalABI.decodeCalldata? (countTransition.params.map Param.name)
      (transitionSignature countTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, countTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := registryBlocks.registry_block_1379_fallthrough (by simp) (by rw [hwv]; rfl) rd
    have rd2 := registryBlocks.registry_block_1384 (by simp) rd1
    have hmemsize : (registryDispatchMem 3).size = 32 := dispatchMem_size 3 (by decide)
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (registryDispatchMem 3) 64
        (by rw [hmemsize]; exact lt_usize _ (by decide)), slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        countTransition.body
        (.returned (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [uint256Value (solcSlotWordAt (UInt256.ofNat 2) σ I)])) := by
      rw [countBody_eq]
      exact ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns
          (evalIdsLength ∅ (by simp)))
    exact rd2.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
  · have rd1 := registryBlocks.registry_block_1379_taken (by simp) (fun h => hwv h) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd (fun _ => by rw [countBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperRegistry
