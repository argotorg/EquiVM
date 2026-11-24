import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `paused()`

Dispatcher bucket 10, arm entry pc 1165: the callvalue guard, then `SLOAD 4` and `RETURN`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem pausedBody_eq : pausedTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage { base := "paused", steps := [] }]] := by rfl

/-- `paused()`: the theorem `Correct.lean` routes selector 4 to. -/
theorem vyperVaultPausedBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 4)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 4) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := vyperVaultReachPausedBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some pausedTransition :=
    vyperVaultDispatch_paused (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (pausedTransition.params.map Param.name)
      (transitionSignature pausedTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, pausedTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := vyperVaultBlocks.vyperVault_block_1165_fallthrough (by simp) (by simpa using hwv) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1170 (by simp) rd1
    have hmemsize : (vyperVaultDispatchMem 10).size = 32 := by native_decide
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (vyperVaultDispatchMem 10) 64
        (by rw [hmemsize]; exact lt_usize _ (by decide)),
      slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        pausedTransition.body
        (.returned (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [wordToElem .bool (solcSlotWordAt (UInt256.ofNat 4) σ I)]))
        (restrictImmutables contract imms) := by
      rw [pausedBody_eq]
      refine ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
      have her : evalStorageRef config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          { base := "paused", steps := [] } = .ok { base := "paused", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
      rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .bool)
          (loc := vyperWordLoc (UInt256.ofNat 4) .bool) (hbase := by simp)
          (her := her) (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
        storageLocLoad_vyperWord, storageLoad_initState_ofUInt256_solcSlotWordAt]
    refine rd2.reEquivExecution hcode' hd hdec hbody ?_
    rcases hwf with h0 | h1
    · rw [h0]
      exact returnEquiv_of_encode (by simpa [wordToElem] using boolFalseReturnEncoding)
    · rw [h1]
      exact returnEquiv_of_encode (by simpa [wordToElem] using boolTrueReturnEncoding)
  · have rd1 := vyperVaultBlocks.vyperVault_block_1165_taken (by simp) (by simpa using hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [pausedBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperVault
