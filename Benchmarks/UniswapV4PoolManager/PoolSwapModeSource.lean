import Benchmarks.UniswapV4PoolManager.PoolSwapFinishSource
import Benchmarks.UniswapV4PoolManager.LocalBytes
import Benchmarks.UniswapV4PoolManager.ConditionalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapModeValid (fee specified : UInt256) : Prop :=
  ¬(1000000 ≤ fee.toNat ∧ 0 < EVM.signed specified)
instance (fee specified : UInt256) : Decidable (poolSwapModeValid fee specified) :=
  inferInstanceAs (Decidable (¬(_ ∧ _)))

theorem poolSwapModeSource {f : Frame} {evm : State} {fee : UInt256} {p : PoolSwapParamsWords}
    (hf : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p)) :
    ExecStmt config f evm poolSwapFunction.body[23]!
      (if poolSwapModeValid fee p.amountSpecified then .ok f evm else .reverted) := by
  have hfee := evalNatGeLiteral (k := 1000000) (evalLocalValue (cfg := config) (evm := evm) hf)
  have hpos : evalExpr? config f evm (.binary .gt (.field (.var "params") "amountSpecified") (.intLit 0)) =
      .ok (.bool (decide (0 < EVM.signed p.amountSpecified))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalStructField (evalLocalValue hp) rfl]
    simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hg : 1000000 ≤ fee.toNat
  · have houter : evalExpr? config f evm (.binary .ge (.var "swapFee") (.intLit 1000000)) = .ok (.bool true) := by
      simpa only [decide_eq_true hg] using hfee
    by_cases hs : 0 < EVM.signed p.amountSpecified
    · rw [if_neg (show ¬poolSwapModeValid fee p.amountSpecified from fun hh => hh ⟨hg, hs⟩)]
      exact ExecStmt.iteTrue houter (ExecBlock.consRevert (ExecStmt.iteTrue
        (by simpa only [decide_eq_true hs] using hpos) (ExecBlock.consRevert (ExecStmt.requireFalse
          (by simp only [evalExpr?, pure])))))
    · rw [if_pos (show poolSwapModeValid fee p.amountSpecified from fun hh => hs hh.2)]
      exact ExecStmt.iteTrue houter (execBlock_singleton (ExecStmt.iteFalse
        (by simpa only [decide_eq_false hs] using hpos) ExecBlock.nil))
  · rw [if_pos (show poolSwapModeValid fee p.amountSpecified from fun hh => hg hh.1)]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hg] using hfee) ExecBlock.nil

theorem poolSwapZeroSource {f : Frame} {evm : State} {fee : UInt256} {p : PoolSwapParamsWords} {r : PoolSwapResultWords}
    (hf : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) :
    ExecStmt config f evm poolSwapFunction.body[24]!
      (if p.amountSpecified = ⟨0⟩ then .returned f evm (some (poolSwapReturnValues ⟨0⟩ fee ⟨0⟩ r)) else .ok f evm) := by
  have hg : evalExpr? config f evm (.binary .eq (.field (.var "params") "amountSpecified") (.intLit 0)) =
      .ok (.bool (decide (p.amountSpecified = ⟨0⟩))) := by
    simpa only [signed_eq_zero_iff] using evalIntEq
      (evalStructField (field := "amountSpecified") (evalLocalValue (cfg := config) (evm := evm) hp) rfl)
      (show evalExpr? config f evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
  by_cases hz : p.amountSpecified = ⟨0⟩
  · rw [if_pos hz]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hg)
    apply ExecBlock.consReturn
    apply ExecStmt.return
    change evalExprs? config f evm [.intLit 0, .intLit 0, .var "swapFee", .var "result"] = _
    simp only [evalExprs?, evalLocalValue hf, evalLocalValue hr, evalExpr?, pure, bind, EvalResult.bind]
    rfl
  · rw [if_neg hz]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hg) ExecBlock.nil

end Benchmarks.UniswapV4PoolManager
