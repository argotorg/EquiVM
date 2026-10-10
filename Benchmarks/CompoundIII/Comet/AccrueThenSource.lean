import Benchmarks.CompoundIII.Comet.AccrueRewardsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem accrueIndicesAssign (v : CometWithExtendedAssetListImmutables)
    (initial evm : EVM.State) (elapsed time : UInt256) (borrow : Bool) :
    let frame := accrueIndicesFrame v initial elapsed time
    let w0 := Solm.EVM.storageLoad initial initial.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad initial initial.executionEnv.codeOwner ⟨1⟩
    ExecStmt config frame evm
      (.assign .storage ⟨totalsIndexName borrow, []⟩
        (.tupleGet (.var "__c1") (if borrow then 1 else 0)))
      (.ok frame (storeTotalsIndex evm borrow (accruedIndex v w0 w1 elapsed borrow))) := by
  dsimp only
  apply ExecStmt.assign (value := .int (accruedIndex v
    (Solm.EVM.storageLoad initial initial.executionEnv.codeOwner ⟨0⟩)
    (Solm.EVM.storageLoad initial initial.executionEnv.codeOwner ⟨1⟩) elapsed borrow).toNat)
  · cases borrow <;>
      simp only [evalExpr?, accrueIndicesFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?,
        Bool.false_eq_true, if_false, if_true] <;> rfl
  · apply assignTotalsIndex
    cases borrow <;>
      simp [accrueTimeFrame, totalsIndexName]

theorem accrueThen_source (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (elapsed time : UInt256) (ht : elapsed.toNat < 2^40) :
    internalBlockResult config (accrueTimeFrame v elapsed time) evm accrueThenBlock
      (accrueThenOutcome v evm elapsed time) := by
  let f0 := accrueTimeFrame v elapsed time
  let f1 := accrueIndicesFrame v evm elapsed time
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let evmB := storeTotalsIndex evm true (accruedIndex v w0 w1 elapsed true)
  let evmI := accrueIndicesState evm v elapsed
  have he : evalExpr? config f0 evm (.var "timeElapsed") = .ok (.int elapsed.toNat) := by
    simp only [evalExpr?, f0, accrueTimeFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  by_cases hv : AccrueIndicesValid v evm elapsed
  · have hcall := accruedIndices_call_ok v f0 evm elapsed _ "__c1" rfl rfl he ht hv
    have hb := accrueIndicesAssign v evm evm elapsed time true
    have hs := accrueIndicesAssign v evm evmB elapsed time false
    apply internalBlockResult.prepend hcall
    by_cases hperm : evm.executionEnv.perm = true
    · simp only [accrueThenOutcome, if_pos hv, hperm, if_true]
      apply internalBlockResult.prepend hb
      apply internalBlockResult.prepend hs
      have het : evalExpr? config f1 evmI (.var "timeElapsed") = .ok (.int elapsed.toNat) := by
        simp only [evalExpr?, f1, accrueIndicesFrame, accrueTimeFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl
      have hen : evalExpr? config f1 evmI (.var "now_") = .ok (.int time.toNat) := by
        simp only [evalExpr?, f1, accrueIndicesFrame, accrueTimeFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl
      have hr := accrueRewards_source v f1 evmI elapsed time rfl rfl het hen
        (by intro b; cases b <;>
          simp [f1, accrueIndicesFrame, accrueTimeFrame, totalsPrincipalName])
        (by intro b; cases b <;>
          simp [f1, accrueIndicesFrame, accrueTimeFrame, trackingIndexName])
        (by simp [f1, accrueIndicesFrame, accrueTimeFrame])
      by_cases hrvalid : AccrueRewardsValid v evmI elapsed
      · rw [if_pos hrvalid] at hr ⊢
        exact ⟨_, hr⟩
      · rw [if_neg hrvalid] at hr ⊢
        exact hr
    · have hp : evm.executionEnv.perm = false := Bool.eq_false_iff.mpr hperm
      simp only [accrueThenOutcome, if_pos hv, hp, Bool.false_eq_true, if_false]
      exact ExecBlock.consStatic (execStmt_assign_static hb hp)
  · simp only [accrueThenOutcome, if_neg hv]
    exact ExecBlock.consRevert
      (accruedIndices_call_revert v f0 evm elapsed _ "__c1" rfl rfl he ht hv)

end Benchmarks.CompoundIII.Comet
