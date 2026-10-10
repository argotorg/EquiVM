import Benchmarks.UniswapV3.Pool.OracleObserveLoopSource
import Benchmarks.UniswapV3.Pool.OracleObserveAllocationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleObserveInitialLocals (imms : Store) (time : UInt256) (secondsAgos : List UInt256)
    (tick : Int) (index liquidity card : UInt256) : Store :=
  (oracleObserveAllocatedFrame imms time secondsAgos tick index liquidity card).locals.insert "i" (.int 0)

theorem oracleObserveInitialGets (imms : Store) (time : UInt256) (secondsAgos : List UInt256)
    (tick : Int) (index liquidity card : UInt256) :
    let locals := oracleObserveInitialLocals imms time secondsAgos tick index liquidity card
    OracleObserveBindings locals time secondsAgos tick index liquidity card ∧
      locals.get? "i" = some (.int (Int.ofNat 0)) ∧
      locals.get? "tickCumulatives" = some (.array (List.replicate secondsAgos.length (.int 0))) ∧
      locals.get? "secondsPerLiquidityCumulativeX128s" =
        some (.array (List.replicate secondsAgos.length (.int 0))) := by
  refine ⟨(oracleObserveAllocatedBindings imms time secondsAgos tick index liquidity card).insert_aux
    "i" _ (by decide), ?_, ?_, ?_⟩
  all_goals simp [oracleObserveInitialLocals, oracleObserveAllocatedFrame, oracleObserveTicksFrame,
    Std.HashMap.getElem_insert]

theorem oracleObserveForExec (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256) (result : ExecResult)
    (hloop : ExecForLoop config
      {contract := contract
       locals := oracleObserveInitialLocals imms time secondsAgos tick index liquidity card
       immutables := imms} evm oracleObserveCondition oracleObservePost oracleObserveLoopBody result) :
    ExecStmt config (oracleObserveAllocatedFrame imms time secondsAgos tick index liquidity card) evm
      oracleObserveFunction.body[7]! result := by
  rw [oracleObserveFor]
  apply ExecStmt.for _ hloop
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem oracleObserveReturns (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (ticks seconds : List Value) (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) (hb : secondsAgos.length ≤ 2 ^ 64 - 1)
    (hrun : OracleObserveLoopRun time secondsAgos tick index liquidity card evm.accountMap evm.executionEnv
      0 (List.replicate secondsAgos.length (.int 0)) (List.replicate secondsAgos.length (.int 0))
      ticks seconds) :
    ∃ frame, ExecFuncBody config (oracleObserveFrame imms time secondsAgos tick index liquidity card)
      evm oracleObserveFunction.body (.returned frame evm (some [.array ticks, .array seconds])) := by
  obtain ⟨hbase, hi, ht, hs⟩ := oracleObserveInitialGets imms time secondsAgos tick index liquidity card
  obtain ⟨locals, hloop, ht', hs'⟩ := oracleObserveLoopOfRun imms evm time secondsAgos tick
    index liquidity card 0 _ _ ticks seconds hc htick (by omega) hrun _ hbase hi ht hs
    (by simp) (by simp)
  let finalFrame : Frame := {contract := contract, locals := locals, immutables := imms}
  refine ⟨finalFrame, ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 7 oracleObserveFunction.body]
  apply execBlock_append_ok (oracleObserveAllocatePrefix imms evm time secondsAgos tick
    index liquidity card hn hb)
  refine ExecBlock.consNormal (oracleObserveForExec imms evm time secondsAgos tick
    index liquidity card _ hloop) (ExecBlock.consReturn (ExecStmt.return ?_))
  have et := evalExpr_var_get (cfg := config) (frame := finalFrame) (evm := evm) ht'
  have es := evalExpr_var_get (cfg := config) (frame := finalFrame) (evm := evm) hs'
  dsimp only [finalFrame] at et es
  simp only [evalExprs?, et, es, bind, EvalResult.bind, pure]

theorem oracleObserveLoopReverts (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) (hb : secondsAgos.length ≤ 2 ^ 64 - 1)
    (hfail : OracleObserveLoopFailure time secondsAgos tick index liquidity card evm.accountMap evm.executionEnv
      0 (List.replicate secondsAgos.length (.int 0)) (List.replicate secondsAgos.length (.int 0))) :
    ExecFuncBody config (oracleObserveFrame imms time secondsAgos tick index liquidity card)
      evm oracleObserveFunction.body .reverted := by
  obtain ⟨hbase, hi, ht, hs⟩ := oracleObserveInitialGets imms time secondsAgos tick index liquidity card
  have hloop := oracleObserveLoopOfFailure imms evm time secondsAgos tick index liquidity card
    0 _ _ hc htick (by omega) hfail _ hbase hi ht hs (by simp) (by simp)
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 7 oracleObserveFunction.body]
  apply execBlock_append_ok (oracleObserveAllocatePrefix imms evm time secondsAgos tick
    index liquidity card hn hb)
  exact ExecBlock.consRevert (oracleObserveForExec imms evm time secondsAgos tick index liquidity card _ hloop)

end Benchmarks.UniswapV3.Pool
