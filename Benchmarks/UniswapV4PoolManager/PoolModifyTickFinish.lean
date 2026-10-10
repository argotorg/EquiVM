import Benchmarks.UniswapV4PoolManager.PoolModifyLimits
import Benchmarks.UniswapV4PoolManager.PoolModifyBitmaps

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyTickFinishResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) : ExecResult :=
  continueBlockResult (fun f1 post => poolModifyBitmapsResult f1 post id p fl fu)
    (poolModifyLimitsResult f evm p.delta (EVM.signed p.spacing) gl gu)

theorem poolModifyTickFinish {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {gl gu : UInt256} (hc : PoolModifyContext f id p)
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu))
    (ht : poolTicksValid p.lower p.upper) :
    ExecBlock config f evm [poolModifyLimitsStmt, poolModifyFlipStmt false, poolModifyFlipStmt true]
      (poolModifyTickFinishResult f evm id p fl gl fu gu) := by
  have hl := poolModifyLimits (evm := evm) hc.contract hc.params hc.liquidityDelta hs
  apply execBlock_continue (execBlock_singleton hl)
  intro f1 post hpost
  exact poolModifyBitmaps (evm := post) (poolModifyLimitsResult_context hc hpost)
    ((poolModifyLimitsResult_get hpost "state" (by decide)).trans hs) ht

theorem poolModifyTickFinishResult_context {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {fl fu : Bool} {gl gu : UInt256} (hc : PoolModifyContext f id p)
    (h : poolModifyTickFinishResult f evm id p fl gl fu gu = .ok f' post) : PoolModifyContext f' id p := by
  obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
  exact poolModifyBitmapsResult_context (poolModifyLimitsResult_context hc hlo) hup

theorem poolModifyTickFinishResult_get {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {fl fu : Bool} {gl gu : UInt256}
    (h : poolModifyTickFinishResult f evm id p fl gl fu gu = .ok f' post)
    (name : Ident) (hm : ("maxLiquidityPerTick" == name) = false)
    (ha : ∀ upper, (poolModifyFlipAlias upper == name) = false)
    (hr : ∀ upper, (poolModifyFlipRet upper == name) = false) : f'.locals.get? name = f.locals.get? name := by
  obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
  exact (poolModifyBitmapsResult_get hup name ha hr).trans (poolModifyLimitsResult_get hlo name hm)

end Benchmarks.UniswapV4PoolManager
