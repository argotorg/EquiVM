import Benchmarks.UniswapV4PoolManager.PoolModifyFeeFrames
import Benchmarks.UniswapV4PoolManager.PoolModifyClears
import Benchmarks.UniswapV4PoolManager.PoolModifyFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyAfterFeesResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (fl fu : Bool) (fees : UInt256) : ExecResult :=
  continueBlockResult (fun f1 post => poolModifyFinishResult f1 post id p fees)
    (poolModifyClearsResult f evm id p fl fu)

theorem poolModifyAfterFees {f : Frame} {evm : State} {id fees : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {gl gu : UInt256} (hc : PoolModifyContext f id p)
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu)) (ht : poolTicksValid p.lower p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some (.int 0)) (hf : f.locals.get? "feeDelta" = some (.int (EVM.signed fees))) :
    ExecBlock config f evm (poolModifyFunction.body.drop 23) (poolModifyAfterFeesResult f evm id p fl fu fees) := by
  have hclear := poolModifyClears (evm := evm) hc hs
  apply execBlock_continue (execBlock_singleton hclear)
  intro f1 post hpost
  exact poolModifyFinish (poolModifyClearsResult_context hc hpost) ht hdlo hdhi
    ((poolModifyClearsResult_get hpost "delta" (by intro u; cases u <;> decide)
      (by intro u; cases u <;> decide)).trans hd)
    ((poolModifyClearsResult_get hpost "feeDelta" (by intro u; cases u <;> decide)
      (by intro u; cases u <;> decide)).trans hf)

def poolModifyAccountingResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool) : ExecResult :=
  continueBlockResult (fun f1 post => poolModifyAfterFeesResult f1 post id p fl fu (poolModifyFeeDeltaWord evm id p))
    (poolModifyFeesResult f evm id p)

theorem poolModifyAccounting {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams} {oldFee : Value}
    {fl fu : Bool} {gl gu : UInt256} (hc : PoolModifyContext f id p)
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu)) (ht : poolTicksValid p.lower p.upper)
    (hlo : int24Canonical p.lower) (hup : int24Canonical p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some (.int 0)) (hf : f.locals.get? "feeDelta" = some oldFee) :
    ExecBlock config f evm (poolModifyFunction.body.drop 8) (poolModifyAccountingResult f evm id p fl fu) := by
  have hfees := poolModifyFees (evm := evm) hc hlo hup hf
  apply execBlock_continue hfees
  intro f1 post hpost
  exact poolModifyAfterFees (poolModifyFeesResult_context hc hpost)
    ((poolModifyFeesResult_get hpost "state" (Or.inr rfl)).trans hs) ht hdlo hdhi
    ((poolModifyFeesResult_get hpost "delta" (Or.inl rfl)).trans hd) (poolModifyFeesResult_fee hpost)

end Benchmarks.UniswapV4PoolManager
