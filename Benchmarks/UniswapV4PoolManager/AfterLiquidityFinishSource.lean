import Benchmarks.UniswapV4PoolManager.BalanceDeltaCombineSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def afterLiquidityFinishFrame (f : Frame) (delta hookDelta : UInt256) : Frame :=
  let result := Value.int (EVM.signed (balanceDeltaCombineWord true delta hookDelta))
  {f with locals := ((f.locals.insert "hookDelta" (.int (EVM.signed hookDelta))).insert
    "remaining" result).insert "callerDelta" result}
def afterLiquidityFinishResult (f : Frame) (evm : State) (delta hookDelta : UInt256) : ExecResult :=
  if balanceDeltaCombineFits true delta hookDelta then .ok (afterLiquidityFinishFrame f delta hookDelta) evm
  else .reverted
def afterLiquidityFinishStmts : List Stmt :=
  [.assign .localVar {base := "hookDelta"} (.var "result"),
   .internalCall "BalanceDelta_sub" [.var "callerDelta", .var "hookDelta"] "remaining",
   .assign .localVar {base := "callerDelta"} (.var "remaining")]

theorem afterLiquidityFinish {f : Frame} {evm : State} {delta hookDelta : UInt256} {old : Value}
    (hf : f.contract = contract) (hd : f.locals.get? "callerDelta" = some (.int (EVM.signed delta)))
    (hh : f.locals.get? "hookDelta" = some old) (hr : f.locals.get? "result" = some (.int (EVM.signed hookDelta))) :
    ExecBlock config f evm afterLiquidityFinishStmts (afterLiquidityFinishResult f evm delta hookDelta) := by
  have hs := ExecStmt.assign (evalLocalValue (cfg := config) (evm := evm) hr) (assignLocalValue hh)
  let f1 := {f with locals := f.locals.insert "hookDelta" (.int (EVM.signed hookDelta))}
  have hd1 : f1.locals.get? "callerDelta" = some (.int (EVM.signed delta)) :=
    (store_get_ne _ _ (by decide : ("hookDelta" == "callerDelta") = false)).trans hd
  have hc := balanceDeltaCombineCall (f := f1) (evm := evm) hf
    (evalLocalValue hd1) (evalLocalValue (store_get_self _ _ _)) true "remaining"
  by_cases hfit : balanceDeltaCombineFits true delta hookDelta
  · rw [if_pos hfit] at hc
    rw [afterLiquidityFinishResult, if_pos hfit]
    exact ExecBlock.consNormal hs (ExecBlock.consNormal hc
      (execBlock_singleton (ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
        (assignLocalValue ((store_get_ne _ _ (by decide : ("remaining" == "callerDelta") = false)).trans hd1)))))
  · rw [if_neg hfit] at hc
    rw [afterLiquidityFinishResult, if_neg hfit]
    exact ExecBlock.consNormal hs (ExecBlock.consRevert hc)

end Benchmarks.UniswapV4PoolManager
