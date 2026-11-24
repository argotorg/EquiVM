import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `totalDeposits()`

Dispatcher bucket 6: the callvalue guard at pc 1355, then `SLOAD 2` and `RETURN`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem totalDepositsBody_eq : totalDepositsTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage { base := "totalDeposits", steps := [] }]] := by rfl

/-- `totalDeposits()`: the theorem `Correct.lean` routes selector 5 to. -/
theorem vyperVaultTotalDepositsBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 5)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 5) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := vyperVaultReachTotalDepositsBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some totalDepositsTransition :=
    vyperVaultDispatch_totalDeposits (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (totalDepositsTransition.params.map Param.name)
      (transitionSignature totalDepositsTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, totalDepositsTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := vyperVaultBlocks.vyperVault_block_1355_fallthrough (by simp) (by simpa using hwv) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1360 (by simp) rd1
    have hmemsize : (vyperVaultDispatchMem 6).size = 32 := by native_decide
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (vyperVaultDispatchMem 6) 64
        (by rw [hmemsize]; exact lt_usize _ (by decide)),
      slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        totalDepositsTransition.body
        (.returned (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.int (Int.ofNat (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat)]))
        (restrictImmutables contract imms) := by
      rw [totalDepositsBody_eq]
      refine ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
      have her : evalStorageRef config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          { base := "totalDeposits", steps := [] } = .ok { base := "totalDeposits", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
      rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
          (physicalSlot := UInt256.ofNat 2) (hbase := by simp)
          (her := her) (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
        storageLoad_initState_ofUInt256_solcSlotWordAt]
    exact rd2.reEquivExecution hcode' hd hdec hbody
      (returnEquiv_of_encode (uint256ReturnEncoding _))
  · have rd1 := vyperVaultBlocks.vyperVault_block_1355_taken (by simp) (by simpa using hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [totalDepositsBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperVault
