import Benchmarks.UniswapV4PoolManager.PoolUpdateTickSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolUpdateTickCallResult (f : Frame) (evm : EVM.State) (id : UInt256) (tick delta : Int)
    (upper : Bool) (ret : Ident) : ExecResult :=
  resumeCallResult f ret (poolUpdateTickResult f evm id tick delta upper)

theorem poolUpdateTickCall {f : Frame} {evm : EVM.State} {es et ed eu : Expr}
    {id : UInt256} {tick delta : Int} {upper : Bool}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (ht : evalExpr? config f evm et = .ok (.int tick))
    (hd : evalExpr? config f evm ed = .ok (.int delta))
    (hu : evalExpr? config f evm eu = .ok (.bool upper)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Pool_updateTick" [es, et, ed, eu] ret)
      (poolUpdateTickCallResult f evm id tick delta upper ret) := by
  obtain ⟨f', hb⟩ := poolUpdateTickBody
    (f := {f with locals := ((((∅ : Store).insert "upper" (.bool upper)).insert
      "liquidityDelta" (.int delta)).insert "tick" (.int tick)).insert "self" (poolRefValue id)})
    (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "tick") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("tick" == "liquidityDelta") = false)
      (by decide : ("self" == "liquidityDelta") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("liquidityDelta" == "upper") = false)
      (by decide : ("tick" == "upper") = false) (by decide : ("self" == "upper") = false)).trans (store_get_self _ _ _))
  have hcall := internalCallFunctionExec (caller := f) (name := "Pool_updateTick") (retVar := ret)
    (args := [es, et, ed, eu]) (argVals := [poolRefValue id, .int tick, .int delta, .bool upper])
    (by simp only [evalExprs?, hs, ht, hd, hu, bind, EvalResult.bind, pure])
    (by rw [hf]; exact poolUpdateTick_lookup) rfl hb
  simpa only [poolUpdateTickCallResult, poolUpdateTickResult, poolUpdateTickFinishResult,
    poolUpdateTickTailResult, resumeCallResult_ite, resumeCallResult_returned,
    resumeCallResult_reverted, resumeCallResult_static] using hcall

end Benchmarks.UniswapV4PoolManager
