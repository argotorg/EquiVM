import Benchmarks.UniswapV4PoolManager.PoolSwapFeeWords
import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax
import Benchmarks.UniswapV4PoolManager.SimpleMulDivSource
import Benchmarks.UniswapV4PoolManager.WordBorrowSource
import Benchmarks.UniswapV4PoolManager.WordBoolean

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapGrowthFrame (f : Frame) (s : PoolSwapStepWords) (liquidity : UInt256) : Frame :=
  if liquidity = ⟨0⟩ then f
  else valueLocal (wordLocal f "__c20" (simpleMulDiv s.feeAmount (UInt256.ofNat (2^128)) liquidity))
    "step" (poolSwapStepValue (poolSwapGrowthStep s liquidity))

theorem poolSwapGrowthSource {f : Frame} {evm : State} {s : PoolSwapStepWords} {r : PoolSwapResultWords}
    (hf : f.contract = contract)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) :
    ExecStmt config f evm poolSwapLoopBody[17]! (.ok (poolSwapGrowthFrame f s r.liquidity) evm) := by
  have hg : evalExpr? config f evm (.binary .gt (.field (.var "result") "liquidity") (.intLit 0)) =
      .ok (.bool (decide (r.liquidity ≠ ⟨0⟩))) := by
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordPositive_iff] using
      evalWordGt (evalStructField (field := "liquidity") (evalLocalValue hr) rfl)
      (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
  by_cases hz : r.liquidity = ⟨0⟩
  · rw [poolSwapGrowthFrame, if_pos hz]
    exact ExecStmt.iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hg) ExecBlock.nil
  · rw [poolSwapGrowthFrame, if_neg hz]
    let f1 := wordLocal f "__c20" (simpleMulDiv s.feeAmount (UInt256.ofNat (2^128)) r.liquidity)
    have hcall := simpleMulDivCall hf (evalStructField (field := "feeAmount") (evalLocalValue (evm := evm) hs) rfl)
      (show evalExpr? config f evm (.intLit (2^128)) = .ok (.int (Int.ofNat (UInt256.ofNat (2^128)).toNat)) by
        simp only [evalExpr?, pure]; rfl)
      (evalStructField (field := "liquidity") (evalLocalValue hr) rfl) "__c20"
    have hs1 : f1.locals.get? "step" = some (poolSwapStepValue s) :=
      (store_get_ne _ _ (by decide : ("__c20" == "step") = false)).trans hs
    have hstore : ExecStmt config f1 evm
        (.assign .localVar {base := "step", steps := [.field "feeGrowthGlobalX128"]}
          (.cast (.binary .add (.field (.var "step") "feeGrowthGlobalX128") (.var "__c20"))
            (.elem (.int (.uint ⟨256, by decide⟩)))))
        (.ok (valueLocal f1 "step" (poolSwapStepValue (poolSwapGrowthStep s r.liquidity))) evm) := by
      simpa only [poolSwapGrowthStep, if_neg hz] using
        ExecStmt.assign (evalWordAdd (evalStructField (field := "feeGrowthGlobalX128") (evalLocalValue hs1) rfl)
          (evalLocalValue (store_get_self _ _ _))) (assignLocalField hs1 rfl rfl)
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hg)
      (ExecBlock.consNormal hcall (execBlock_singleton hstore))

end Benchmarks.UniswapV4PoolManager
