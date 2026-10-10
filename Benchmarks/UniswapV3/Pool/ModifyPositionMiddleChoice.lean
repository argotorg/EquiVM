import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleModel
import Benchmarks.UniswapV3.Pool.ModifyPositionGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionMiddleChoiceSource (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) (result : ExecResult) (hz : a.delta ≠ 0)
    (hlo : a.lower ≤ slot0TickValue evm.accountMap evm.executionEnv)
    (hhi : slot0TickValue evm.accountMap evm.executionEnv < a.upper)
    (hout : ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) modifyPositionMiddleBody result) :
    ExecStmt config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) modifyPositionFunction.body[8]! result := by
  apply ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using
    evalModifyPositionNonzero (immStore v) a evm (modifyPositionUpdatedState v a evm))
  apply execBlock_singleton
  have hnlo : ¬slot0TickValue evm.accountMap evm.executionEnv < a.lower := by omega
  apply ExecStmt.iteFalse (by simpa only [Bool.false_eq_true, if_false, decide_eq_false hnlo] using
    evalModifyPositionRangeGuard (immStore v) a evm (modifyPositionUpdatedState v a evm) false)
  apply execBlock_singleton
  exact ExecStmt.iteTrue (by simpa only [if_true, decide_eq_true hhi] using
    evalModifyPositionRangeGuard (immStore v) a evm (modifyPositionUpdatedState v a evm) true) hout

end Benchmarks.UniswapV3.Pool
