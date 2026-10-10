import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax
import Benchmarks.UniswapV4PoolManager.PoolFeeGrowthStorage
import Benchmarks.UniswapV4PoolManager.WordConditionalSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapZeroStep : PoolSwapStepWords := ⟨⟨0⟩, ⟨0⟩, false, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩⟩
def poolSwapInitialStep (evm : State) (id : UInt256) (zeroForOne : Bool) : PoolSwapStepWords :=
  {poolSwapZeroStep with feeGrowthGlobal := if zeroForOne then poolFeeGrowthWord evm id false else poolFeeGrowthWord evm id true}
def poolSwapStepInitFrame (f : Frame) (evm : State) (id : UInt256) (zeroForOne : Bool) : Frame :=
  valueLocal (valueLocal f "step" (poolSwapStepValue poolSwapZeroStep)) "step" (poolSwapStepValue (poolSwapInitialStep evm id zeroForOne))

theorem poolSwapStepInitSource {f : Frame} {evm : State} {id : UInt256} {zeroForOne : Bool}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ExecBlock config f evm ((poolSwapFunction.body.drop 26).take 2)
      (.ok (poolSwapStepInitFrame f evm id zeroForOne) evm) := by
  let f1 := valueLocal f "step" (poolSwapStepValue poolSwapZeroStep)
  have h0 : ExecStmt config f evm poolSwapFunction.body[26]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, evalStructFields?, bind, EvalResult.bind, pure]; rfl)
  have hs1 : f1.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne _ _ (by decide : ("step" == "self") = false)).trans hs
  have hz1 : f1.locals.get? "zeroForOne" = some (.bool zeroForOne) :=
    (store_get_ne _ _ (by decide : ("step" == "zeroForOne") = false)).trans hz
  have hz' : evalExpr? config f1 evm (.var "zeroForOne") = .ok (.bool (decide (zeroForOne = true))) := by
    simpa only [Bool.decide_coe] using evalLocalValue (cfg := config) (evm := evm) hz1
  have h1 : ExecStmt config f1 evm poolSwapFunction.body[27]! (.ok (poolSwapStepInitFrame f evm id zeroForOne) evm) :=
    ExecStmt.assign (evalWordConditional hz' (poolFeeGrowth_read hs1 false) (poolFeeGrowth_read hs1 true))
      (assignLocalField (store_get_self _ _ _) rfl rfl)
  exact ExecBlock.consNormal h0 (execBlock_singleton h1)

end Benchmarks.UniswapV4PoolManager
