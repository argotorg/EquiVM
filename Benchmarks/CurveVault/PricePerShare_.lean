import Benchmarks.CurveVault.Dispatch
import Benchmarks.CurveVault.Entry
import Benchmarks.CurveVault.Lock
import Benchmarks.CurveVault.PriceInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultPricePerShare_BodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 12)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 12) rfl hsel
  have hd : dispatchMsg contract I.calldata = some pricePerShare_Transition := by
    apply vaultDispatch_pricePerShare_
    all_goals first | exact hsel | exact selIs_exclusive (by decide +kernel) hsel
  apply vaultGuardedEntry (t := pricePerShare_Transition) (pc := UInt256.ofNat 1506)
    hcode hsize hd rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel : 4 < UInt256.size) (by decide +kernel) (by native_decide)
    (fun h => False.elim (by omega)) (vaultReachPricePerShare_Body hcode hsz hsize hsel)
  intro hvalue _ k C rdBody
  have hdec : config.externalABI.decodeCalldata? (pricePerShare_Transition.params.map Param.name)
      (transitionSignature pricePerShare_Transition).paramTypes I.calldata = some ∅ := by
    change decodeCalldataWithMode .vyper [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let locals : Store := (∅ : Store).insert "_is_floor" (.bool true)
  have hflagEval : evalExpr? config {contract := contract, locals := ∅} evm (.boolLit true) = .ok (.bool true) := by
    simp [evalExpr?, pure]
  have hargEval : evalExprs? config {contract := contract, locals := locals} evm [.var "_is_floor"] = .ok [.bool true] := by
    simp [locals, evalExprs?, evalExpr?, EvalResult.ofOption, bind, pure, EvalResult.bind]
  have hload : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerTransientWord I σ ⟨0⟩ :=
    codeOwnerTransientWord_initState _
  have rd1533 := vaultBlocks.vault_block_1506 (by simp) (by native_decide) rdBody
  by_cases hlocked : codeOwnerTransientWord I σ ⟨0⟩ = ⟨1⟩
  · have rdRevert := vaultBlocks.vault_block_1533_taken (by simp)
      (by change UInt256.eq _ (codeOwnerTransientWord I σ ⟨0⟩) ≠ _
          rw [hlocked]; decide +kernel) (by native_decide) rd1533
    have hrev := vaultBlocks.vault_block_8284 (by simp) rdRevert
    have hsource : ExecTransitionBody fork config contract evm ∅ pricePerShare_Transition.body .reverted :=
      ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
        (ExecBlock.consNormal (ExecStmt.letDecl hflagEval)
          (ExecBlock.consRevert (ExecStmt.requireFalse (vaultLockEval_fail evm locals (by rw [hload]; exact hlocked))))))
    exact hrev.reEquivExecutionRevert hcode hd hdec hsource
  · have hlock : Stele.EVM.transientLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨1⟩ := by rw [hload]; exact hlocked
    have rd1543 := vaultBlocks.vault_block_1533_fallthrough (by simp)
      (u256_eq_of_ne (Ne.symm hlocked)) rd1533
    have hgap : 320 - (vaultDispatchMemory ⟨2572356358⟩).size < USize.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by norm_num))
    have hmem : 352 ≤ ((⟨1⟩ : UInt256).toByteArray.write 0 (vaultDispatchMemory ⟨2572356358⟩) 320 32).size :=
      toByteArray_write_size_ge_off_add32 _ _ 320 hgap
    rcases vaultPriceRoutine (isFloor := true) (locals := locals) SourceState.init hmem
      (by simp [locals]) (by simp [locals]) (by simp [locals])
      (memLoad_write_back _ _ 320 (by decide +kernel) hgap) (by simp) rd1543 with
      ⟨evm', σ', calleeLocals, value, hcallee, hs, hret⟩ | ⟨hcallee, hrev⟩
    · have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
        (callee := vaultPriceFunction) (name := "pricePerShare_body") (args := [.var "_is_floor"])
        (argVals := [.bool true]) (retVar := "__r") hargEval rfl rfl hcallee
      have hsource : ExecTransitionBody fork config contract evm ∅ pricePerShare_Transition.body
          (.returned {contract := contract, locals := locals.insert "__r" (.int (Int.ofNat value.toNat))}
            evm' (some [.int (Int.ofNat value.toNat)])) := by
        apply ExecFuncBody.execBlockRet
        apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
        apply ExecBlock.consNormal (ExecStmt.letDecl hflagEval)
        apply ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock))
        exact ExecBlock.consNormal hcall (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
          simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption]))))
      exact hret.reEquivExecutionGen hcode hd hdec hsource hs.accounts
        (returnEquiv_of_encode (uint256ReturnEncoding _))
    · have hsource : ExecTransitionBody fork config contract evm ∅ pricePerShare_Transition.body .reverted := by
        apply ExecFuncBody.execBlockRevert
        apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
        apply ExecBlock.consNormal (ExecStmt.letDecl hflagEval)
        apply ExecBlock.consNormal (ExecStmt.requireTrue (vaultLockEval_pass evm locals hlock))
        exact ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultPriceFunction)
          (args := [.var "_is_floor"]) (argVals := [.bool true]) hargEval rfl rfl hcallee)
      exact hrev.reEquivExecutionRevert hcode hd hdec hsource

theorem vaultPricePerShare_Body {σ σ₀ A I} {g : UInt256}
    (_hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 12)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I :=
  vaultPricePerShare_BodyCore hcode hsize hsel
end Benchmarks.CurveVault
