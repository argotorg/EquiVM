import Benchmarks.UniswapV4PoolManager.PoolModifyAmountResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFinishResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) (fees : UInt256) : ExecResult :=
  continueBlockResult (fun f1 post => .returned f1 post
    (some [.int (EVM.signed (poolModifyAmountsDeltaWord evm id p)), .int (EVM.signed fees)]))
    (poolModifyAmountsResult f evm id p)

theorem poolModifyFinish {f : Frame} {evm : State} {id fees : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some (.int 0)) (hf : f.locals.get? "feeDelta" = some (.int (EVM.signed fees))) :
    ExecBlock config f evm (poolModifyFunction.body.drop 24) (poolModifyFinishResult f evm id p fees) := by
  have hamt := poolModifyAmounts (evm := evm) hc ht hdlo hdhi hd
  apply execBlock_continue (execBlock_singleton hamt)
  intro f1 post hpost
  have hdelta := poolModifyAmountsResult_delta hd hpost
  have hfee := (poolModifyAmountsResult_fee hpost).trans hf
  apply ExecBlock.consReturn
  apply ExecStmt.return
  change evalExprs? config f1 post [.var "delta", .var "feeDelta"] = _
  simp only [evalExprs?, evalLocalValue hdelta, evalLocalValue hfee, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV4PoolManager
