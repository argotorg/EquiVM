import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `feesCollected()`

Dispatcher bucket 5: the callvalue guard at pc 1383, then `SLOAD 3` and `RETURN`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem feesCollectedBody_eq : feesCollectedTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage { base := "feesCollected", steps := [] }]] := by rfl

/-- `feesCollected()`: the theorem `Correct.lean` routes selector 9 to. -/
theorem vyperVaultFeesCollectedBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 9)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 9) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := vyperVaultReachFeesCollectedBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some feesCollectedTransition :=
    vyperVaultDispatch_feesCollected (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (feesCollectedTransition.params.map Param.name)
      (transitionSignature feesCollectedTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, feesCollectedTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := vyperVaultBlocks.vyperVault_block_1383_fallthrough (by simp) (by simpa using hwv) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1388 (by simp) rd1
    have hmemsize : (vyperVaultDispatchMem 5).size = 32 := by native_decide
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (vyperVaultDispatchMem 5) 64
        (by rw [hmemsize]; exact lt_usize _ (by decide)),
      slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        feesCollectedTransition.body
        (.returned (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat (solcSlotWordAt (UInt256.ofNat 3) σ I).toNat)]))
        (restrictImmutables contract imms) := by
      rw [feesCollectedBody_eq]
      refine ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
      have her : evalStorageRef config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          { base := "feesCollected", steps := [] } = .ok { base := "feesCollected", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
      rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
          (physicalSlot := UInt256.ofNat 3) (hbase := by simp)
          (her := her) (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
        storageLoad_initState_ofUInt256_solcSlotWordAt]
    exact rd2.reEquivExecution hcode' hd hdec hbody
      (returnEquiv_of_encode (uint256ReturnEncoding _))
  · have rd1 := vyperVaultBlocks.vyperVault_block_1383_taken (by simp) (by simpa using hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [feesCollectedBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperVault
