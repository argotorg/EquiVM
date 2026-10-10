import Benchmarks.UniswapV4PoolManager.PoolDonateDeltaSource
import Benchmarks.UniswapV4PoolManager.PoolDonateTailSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolDonateResult (f : Frame) (evm : State) (id amount0 amount1 : UInt256) : ExecResult :=
  if poolLiquidityWord evm id = ⟨0⟩ then .reverted
  else if amount0.toNat < 2^127 ∧ amount1.toNat < 2^127 then
    if (amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false then .staticViolation
    else .returned f (poolDonatePost evm id amount0 amount1) (some [.int (EVM.signed (poolDonateDelta amount0 amount1))])
  else .reverted

theorem poolDonateBody {f : Frame} {evm : State} {id amount0 amount1 : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "state" = some (poolRefValue id))
    (h0 : f.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (h1 : f.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat))) :
    ∃ f', ExecFuncBody config f evm poolDonateFunction.body (poolDonateResult f' evm id amount0 amount1) := by
  let f0 := wordLocal f "delta" ⟨0⟩
  let f1 := wordLocal f0 "liquidity" (poolLiquidityWord evm id)
  have hdelta : ExecStmt config f evm poolDonateFunction.body[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hliq : ExecStmt config f0 evm poolDonateFunction.body[1]! (.ok f1 evm) :=
    ExecStmt.letDecl (poolLiquidity_read
      ((store_get_ne _ _ (by decide : ("delta" == "state") = false)).trans hs))
  have hguard : evalExpr? config f1 evm (.binary .eq (.var "liquidity") (.intLit 0)) =
      .ok (.bool (decide (poolLiquidityWord evm id = ⟨0⟩))) :=
    evalEqWords (evalLocalValue (store_get_self _ _ _))
      (by simp only [evalExpr?, pure]; rfl)
  by_cases hz : poolLiquidityWord evm id = ⟨0⟩
  · simp only [poolDonateResult, if_pos hz]
    exact ⟨f, .execBlockRevert (ExecBlock.consNormal hdelta (ExecBlock.consNormal hliq
      (ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hguard)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))⟩
  have hpre : ExecBlock config f evm (poolDonateFunction.body.take 3) (.ok f1 evm) :=
    ExecBlock.consNormal hdelta (ExecBlock.consNormal hliq (execBlock_singleton
      (ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hguard) ExecBlock.nil)))
  have hf1 : f1.contract = contract := by dsimp only [f1, f0, wordLocal]; exact hf
  have hs1 : f1.locals.get? "state" = some (poolRefValue id) :=
    (store_get_ne2 _ _ _ (by decide : ("delta" == "state") = false)
      (by decide : ("liquidity" == "state") = false)).trans hs
  have ha1 : f1.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("delta" == "amount0") = false)
      (by decide : ("liquidity" == "amount0") = false)).trans h0
  have hb1 : f1.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("delta" == "amount1") = false)
      (by decide : ("liquidity" == "amount1") = false)).trans h1
  have hd1 : f1.locals.get? "delta" = some (.int 0) :=
    (store_get_ne _ _ (by decide : ("liquidity" == "delta") = false)).trans (store_get_self _ _ _)
  have hcast := poolDonateDeltaSource (evm := evm) hf1 ha1 hb1 hd1
  by_cases hfit : amount0.toNat < 2^127 ∧ amount1.toNat < 2^127
  swap
  · rw [if_neg hfit] at hcast
    simp only [poolDonateResult, if_neg hz, if_neg hfit]
    exact ⟨f, .execBlockRevert (execBlock_append hpre (execBlock_reverted_append hcast))⟩
  rw [if_pos hfit] at hcast
  let f2 := poolDonateDeltaFrame f1 amount0 amount1
  have hf2 : f2.contract = contract := by dsimp only [f2, poolDonateDeltaFrame]; exact hf1
  have hkeep := poolDonateDeltaFrame_get f1 amount0 amount1
  have hs2 : f2.locals.get? "state" = some (poolRefValue id) :=
    (hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hs1
  have ha2 : f2.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)) :=
    (hkeep _ (by decide) (by decide) (by decide) (by decide)).trans ha1
  have hb2 : f2.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)) :=
    (hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hb1
  have hl2 : f2.locals.get? "liquidity" = some (.int (Int.ofNat (poolLiquidityWord evm id).toNat)) :=
    (hkeep _ (by decide) (by decide) (by decide) (by decide)).trans (store_get_self _ _ _)
  obtain ⟨f', htail⟩ := poolDonateTailSource (evm := evm) hf2 hs2 ha2 hb2 hl2 (store_get_self _ _ _)
  by_cases hstatic : (amount0 ≠ ⟨0⟩ ∨ amount1 ≠ ⟨0⟩) ∧ evm.executionEnv.perm = false
  · rw [if_pos hstatic] at htail
    simp only [poolDonateResult, if_neg hz, if_pos hfit, if_pos hstatic]
    exact ⟨f', .execBlockStatic (execBlock_append hpre (execBlock_append hcast htail))⟩
  · rw [if_neg hstatic] at htail
    simp only [poolDonateResult, if_neg hz, if_pos hfit, if_neg hstatic]
    exact ⟨f', .execBlockRet (execBlock_append hpre (execBlock_append hcast htail))⟩

theorem poolDonate_lookup : lookupCallable? contract "Pool_donate" = some poolDonateFunction.toCallable := rfl

theorem poolDonateCall {f : Frame} {evm : State} {id amount0 amount1 : UInt256} {es e0 e1 : Expr}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (h0 : evalExpr? config f evm e0 = .ok (.int (Int.ofNat amount0.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (Int.ofNat amount1.toNat))) (dest : Ident) :
    ∃ f', ExecStmt config f evm (.internalCall "Pool_donate" [es, e0, e1] dest)
      (resumeCallResult f dest (poolDonateResult f' evm id amount0 amount1)) := by
  let cf : Frame := {f with locals := (((∅ : Store).insert "amount1" (.int (Int.ofNat amount1.toNat))).insert
    "amount0" (.int (Int.ofNat amount0.toNat))).insert "state" (poolRefValue id)}
  have hcf : cf.contract = contract := hf
  obtain ⟨f', hb⟩ := poolDonateBody (f := cf) (evm := evm) hcf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("state" == "amount0") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("amount0" == "amount1") = false)
      (by decide : ("state" == "amount1") = false)).trans (store_get_self _ _ _))
  refine ⟨f', ?_⟩
  exact internalCallFunctionExec (argVals := [poolRefValue id, .int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])
    (by simp only [evalExprs?, hs, h0, h1, bind, EvalResult.bind, pure])
    (by rw [hf]; exact poolDonate_lookup) rfl hb

end Benchmarks.UniswapV4PoolManager
