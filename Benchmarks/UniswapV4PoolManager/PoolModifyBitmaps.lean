import Benchmarks.UniswapV4PoolManager.PoolModifyBitmap

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyBitmapsResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (fl fu : Bool) : ExecResult :=
  continueBlockResult (fun f1 post =>
    poolModifyFlipResult f1 post id (EVM.signed p.upper) (EVM.signed p.spacing) true fu)
    (poolModifyFlipResult f evm id (EVM.signed p.lower) (EVM.signed p.spacing) false fl)

theorem poolModifyBitmaps {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {gl gu : UInt256} (hc : PoolModifyContext f id p)
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu))
    (ht : poolTicksValid p.lower p.upper) :
    ExecBlock config f evm [poolModifyFlipStmt false, poolModifyFlipStmt true]
      (poolModifyBitmapsResult f evm id p fl fu) := by
  have hlo := poolModifyFlip (upper := false) (evm := evm) hc.contract hc.self hc.params hc.lower hs
    (poolTicksValid_bounds ht).1
  apply execBlock_continue (execBlock_singleton hlo)
  intro f1 post hpost
  have hc1 := poolModifyFlipResult_context hc hpost
  exact execBlock_singleton (poolModifyFlip (upper := true) (evm := post)
    hc1.contract hc1.self hc1.params hc1.upper
    ((poolModifyFlipResult_get hpost "state" (by decide) (by decide)).trans hs)
    (poolTicksValid_bounds ht).2)

theorem poolModifyBitmapsResult_context {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {fl fu : Bool} (hc : PoolModifyContext f id p)
    (h : poolModifyBitmapsResult f evm id p fl fu = .ok f' post) : PoolModifyContext f' id p := by
  obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
  exact poolModifyFlipResult_context (poolModifyFlipResult_context hc hlo) hup

theorem poolModifyBitmapsResult_get {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {fl fu : Bool}
    (h : poolModifyBitmapsResult f evm id p fl fu = .ok f' post)
    (name : Ident) (ha : ∀ upper, (poolModifyFlipAlias upper == name) = false)
    (hr : ∀ upper, (poolModifyFlipRet upper == name) = false) : f'.locals.get? name = f.locals.get? name := by
  obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
  exact (poolModifyFlipResult_get hup name (ha true) (hr true)).trans
    (poolModifyFlipResult_get hlo name (ha false) (hr false))

end Benchmarks.UniswapV4PoolManager
