import Benchmarks.UniswapV4PoolManager.PoolModifyAccounting
import Benchmarks.UniswapV4PoolManager.PoolModifyTickOutput
import Benchmarks.UniswapV4PoolManager.PoolModifyPreludeFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyAfterPreludeResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  continueBlockResult (fun f1 post => poolModifyAccountingResult f1 post id p
    (poolModifyTicksFlipped evm id p false) (poolModifyTicksFlipped evm id p true)) (poolModifyTicksResult f evm id p)

theorem poolModifyAfterPrelude {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams} {oldFee : Value}
    (hc : PoolModifyContext f id p)
    (hs : f.locals.get? "state" = some (poolModifyStateValue false ⟨0⟩ false ⟨0⟩)) (ht : poolTicksValid p.lower p.upper)
    (hlo : int24Canonical p.lower) (hup : int24Canonical p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some (.int 0)) (hf : f.locals.get? "feeDelta" = some oldFee) :
    ExecBlock config f evm (poolModifyFunction.body.drop 7) (poolModifyAfterPreludeResult f evm id p) := by
  have hticks := poolModifyTicks (evm := evm) hc hs ht
  apply execBlock_continue (execBlock_singleton hticks)
  intro f1 post hpost
  obtain ⟨gl, gu, hstate⟩ := poolModifyTicksResult_flips hs hpost
  exact poolModifyAccounting (poolModifyTicksResult_context hc hpost) hstate ht hlo hup hdlo hdhi
    ((poolModifyTicksResult_get hpost "delta" (Or.inl rfl)).trans hd)
    ((poolModifyTicksResult_get hpost "feeDelta" (Or.inr rfl)).trans hf)

def poolModifyBlockResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  if poolTicksValid p.lower p.upper then poolModifyAfterPreludeResult (poolModifyPreludeFrame f p) evm id p else .reverted
def poolModifyResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  finishBlockResult (poolModifyBlockResult f evm id p)

theorem poolModifyBlock {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolModifyParamsValue p))
    (hlo : int24Canonical p.lower) (hup : int24Canonical p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127) :
    ExecBlock config f evm poolModifyFunction.body (poolModifyBlockResult f evm id p) := by
  have hpre := poolModifyPrelude (evm := evm) hf hp
  by_cases ht : poolTicksValid p.lower p.upper
  · rw [if_pos ht] at hpre
    rw [poolModifyBlockResult, if_pos ht]
    have htail := poolModifyAfterPrelude (evm := evm) (poolModifyPreludeFrame_context hf hs hp)
      (store_get_self _ _ _) ht hlo hup hdlo hdhi (poolModifyPreludeFrame_delta f p) (poolModifyPreludeFrame_fee f p)
    exact execBlock_append hpre htail
  · rw [if_neg ht] at hpre
    rw [poolModifyBlockResult, if_neg ht]
    exact execBlock_reverted_append (s2 := poolModifyFunction.body.drop 7) hpre

theorem poolModifyBody {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolModifyParamsValue p))
    (hlo : int24Canonical p.lower) (hup : int24Canonical p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127) :
    ExecFuncBody config f evm poolModifyFunction.body (poolModifyResult f evm id p) :=
  execFuncBody_block (poolModifyBlock hf hs hp hlo hup hdlo hdhi)

end Benchmarks.UniswapV4PoolManager
