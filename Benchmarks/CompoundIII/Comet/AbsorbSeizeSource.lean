import Benchmarks.CompoundIII.Comet.AbsorbSeizeModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem absorbSeize_source (frame : Frame) (evm : State) (account asset : AccountAddress)
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "account" = some (.address account))
    (hb : frame.locals.get? "asset" = some (.address asset))
    (hU : frame.locals.get? "userCollateral" = none)
    (hT : frame.locals.get? "totalsCollateral" = none) :
    ExecBlock config frame evm absorbSeizeBlock
      (internalFrameResult (absorbSeizeFrame frame evm account asset)
        (absorbSeizeOutcome evm account asset)) := by
  let seized := withdrawCollateralBalance evm account asset
  let ready := absorbSeizeFrame frame evm account asset
  let cleared := absorbSeizeUserState evm account asset
  have hread := evalUserCollateral frame evm account asset (.var "account") (.var "asset") false
    hc hU (by simp only [evalExpr?, ha, EvalResult.ofOption])
    (by simp only [evalExpr?, hb, EvalResult.ofOption])
  have hget (key : String) (hne : "seizeAmount" ≠ key) :
      ready.locals.get? key = frame.locals.get? key := by
    simp only [ready, absorbSeizeFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, if_neg hne]
  have ha' : ready.locals.get? "account" = some (.address account) := (hget _ (by decide)).trans ha
  have hb' : ready.locals.get? "asset" = some (.address asset) := (hget _ (by decide)).trans hb
  have hu' : ready.locals.get? "userCollateral" = none := (hget _ (by decide)).trans hU
  have ht' : ready.locals.get? "totalsCollateral" = none := (hget _ (by decide)).trans hT
  have hw := assignUserCollateralBalance ready evm account asset (.var "account") (.var "asset") ⟨0⟩
    hc hu' (by simp only [evalExpr?, ha', EvalResult.ofOption])
    (by simp only [evalExpr?, hb', EvalResult.ofOption])
  have hz : evalExpr? config ready evm (.intLit 0) = .ok (.int (⟨0⟩ : UInt256).toNat) := by
    simp only [evalExpr?, pure]; rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl hread)
  cases hperm : evm.executionEnv.perm
  · rw [absorbSeizeOutcome, hperm]
    exact ExecBlock.consStatic (ExecStmt.assignStatic hz hw hperm)
  · rw [absorbSeizeOutcome, hperm]
    dsimp only [ite_true, absorbSeizeTotalOutcome]
    have ht : evalExpr? config ready cleared
        (.storage ⟨"totalsCollateral", [.mindex (.var "asset"), .field "totalSupplyAsset"]⟩) =
        .ok (.int (withdrawCollateralTotal cleared asset).toNat) := by
      simpa only [← hc] using evalTotalsCollateralFieldVar cleared ready.locals ready.immutables
        asset false "asset" ht' hb'
    have hseized : evalExpr? config ready cleared (.var "seizeAmount") =
        .ok (.int seized.toNat) := by
      simp only [evalExpr?, ready, absorbSeizeFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
    by_cases hs : seized.toNat ≤ (withdrawCollateralTotal cleared asset).toNat
    · rw [if_pos hs]
      have he := checkedNarrowSubSourceOk ⟨128, by decide⟩ ht hseized (low128_lt _) hs
      have hwT := assignTotalsCollateralBalance ready cleared asset (.var "asset")
        (UInt256.sub (withdrawCollateralTotal cleared asset) seized) hc ht'
        (by simp only [evalExpr?, hb', EvalResult.ofOption])
      exact ExecBlock.consNormal (ExecStmt.assign hz hw)
        (ExecBlock.consNormal (ExecStmt.assign he hwT) .nil)
    · rw [if_neg hs]
      have he := checkedNarrowSubSourceUnderflow ⟨128, by decide⟩ ht hseized (Nat.lt_of_not_ge hs)
      exact ExecBlock.consNormal (ExecStmt.assign hz hw)
        (ExecBlock.consRevert (ExecStmt.assignExprRevert he))

end Benchmarks.CompoundIII.Comet
