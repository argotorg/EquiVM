import Benchmarks.UniswapV3.Pool.ObservePrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def observeResultFrame (v : UniswapV3PoolImmutables) (secondsAgos : List UInt256) (I : ExecutionEnv)
    (ticks seconds : List Value) : Frame :=
  { observeReadyFrame v secondsAgos I with
    locals := (observeReadyFrame v secondsAgos I).locals.insert "__c2" (.tuple [.array ticks, .array seconds]) }

theorem observeSourceReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (secondsAgos : List UInt256) (ticks seconds : List Value) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hn : secondsAgos.length ≤ 2 ^ 64 - 1)
    (hc : (slot0FieldWord 25 2 evm.accountMap evm.executionEnv).toNat ≠ 0)
    (hrun : OracleObserveLoopRun (blockTimestampWord evm.executionEnv) secondsAgos
      (slot0TickValue evm.accountMap evm.executionEnv) (slot0FieldWord 23 2 evm.accountMap evm.executionEnv)
      (poolLiquidityWord evm.accountMap evm.executionEnv) (slot0FieldWord 25 2 evm.accountMap evm.executionEnv)
      evm.accountMap evm.executionEnv 0 (List.replicate secondsAgos.length (.int 0))
      (List.replicate secondsAgos.length (.int 0)) ticks seconds) :
    ExecTransitionBody config contract evm (observeLocals secondsAgos) observeTransition.body
      (.returned (observeResultFrame v secondsAgos evm.executionEnv ticks seconds) evm
        (some [.array ticks, .array seconds])) (immStore v) := by
  obtain ⟨callee, hbody⟩ := oracleObserveReturns (immStore v) evm (blockTimestampWord evm.executionEnv)
    secondsAgos (slot0TickValue evm.accountMap evm.executionEnv)
    (slot0FieldWord 23 2 evm.accountMap evm.executionEnv) (poolLiquidityWord evm.accountMap evm.executionEnv)
    (slot0FieldWord 25 2 evm.accountMap evm.executionEnv) ticks seconds hc
    (u256LandMaskToNatLtOfToNat _ _ (by decide)) (normalizeSint_bounds ⟨24, by decide⟩ _) hn hrun
  have hcall : ExecStmt config (observeReadyFrame v secondsAgos evm.executionEnv) evm
      (.internalCall "Oracle_observe" observeCallArgs "__c2")
      (.ok (observeResultFrame v secondsAgos evm.executionEnv ticks seconds) evm) :=
    internalCallFunctionReturn (callee := oracleObserveFunction) (calleeSolm := callee)
      (value := some [.array ticks, .array seconds]) (evalObserveCallArgs v evm secondsAgos)
      oracleObserveLookup (oracleObserveBind _ _ _ _ _ _) hbody
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 5 observeTransition.body]
  apply execBlock_append_ok (observeReadyPrefix v evm secondsAgos hwv hself)
  refine ExecBlock.consNormal hcall (ExecBlock.consReturn (ExecStmt.return ?_))
  simp only [evalExprs?, evalExpr?, observeResultFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption, tupleGetValue?,
    bind, EvalResult.bind, pure]
  rfl

theorem observeSourceReverts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (secondsAgos : List UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hn : secondsAgos.length ≤ 2 ^ 64 - 1)
    (hf : OracleObserveFailure (blockTimestampWord evm.executionEnv) secondsAgos
      (slot0TickValue evm.accountMap evm.executionEnv) (slot0FieldWord 23 2 evm.accountMap evm.executionEnv)
      (poolLiquidityWord evm.accountMap evm.executionEnv) (slot0FieldWord 25 2 evm.accountMap evm.executionEnv)
      evm.accountMap evm.executionEnv) :
    ExecTransitionBody config contract evm (observeLocals secondsAgos) observeTransition.body .reverted (immStore v) := by
  have hbody := oracleObserveFailureReverts (immStore v) evm (blockTimestampWord evm.executionEnv)
    secondsAgos (slot0TickValue evm.accountMap evm.executionEnv)
    (slot0FieldWord 23 2 evm.accountMap evm.executionEnv) (poolLiquidityWord evm.accountMap evm.executionEnv)
    (slot0FieldWord 25 2 evm.accountMap evm.executionEnv)
    (u256LandMaskToNatLtOfToNat _ _ (by decide)) (normalizeSint_bounds ⟨24, by decide⟩ _) hn hf
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 observeTransition.body]
  apply execBlock_append_ok (observeReadyPrefix v evm secondsAgos hwv hself)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (evalObserveCallArgs v evm secondsAgos) oracleObserveLookup
    (oracleObserveBind _ _ _ _ _ _) hbody

end Benchmarks.UniswapV3.Pool
