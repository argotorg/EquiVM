import Benchmarks.UniswapV4PoolManager.PoolModifyRegionAmount
import Benchmarks.UniswapV4PoolManager.PoolModifyLiquidity
import Benchmarks.UniswapV4PoolManager.BalanceDeltaAssign
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyInsidePackBlock : List Stmt :=
  [.internalCall "toBalanceDelta" [.var "__c23", .var "__c26"] "__c27",
   .assign .localVar {base := "delta"} (.var "__c27")]
def poolModifyInsideSecondBlock : List Stmt :=
  poolModifyRegionAmountBlock true ++ (poolModifyInsidePackBlock ++ poolModifyLiquidityBlock)
def poolModifyInsideBlock : List Stmt := poolModifyRegionAmountBlock false ++ poolModifyInsideSecondBlock
def poolModifyInsidePackFrame (f : Frame) (p : PoolModifyParams) (sqrtPrice : UInt256) : Frame :=
  balanceDeltaAssignFrame f "__c27" "delta"
    (poolModifyRegionWord false p sqrtPrice) (poolModifyRegionWord true p sqrtPrice)
def poolModifyInsideFinishResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (sqrtPrice : UInt256) : ExecResult :=
  poolModifyLiquidityResult (poolModifyInsidePackFrame f p sqrtPrice) evm id p.delta
def poolModifyInsideSecondResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (sqrtPrice : UInt256) : ExecResult :=
  continueBlockResult (fun f1 post => poolModifyInsideFinishResult f1 post id p sqrtPrice)
    (poolModifyRegionAmountResult f evm true p sqrtPrice)
def poolModifyInsideResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams)
    (sqrtPrice : UInt256) : ExecResult :=
  continueBlockResult (fun f1 post => poolModifyInsideSecondResult f1 post id p sqrtPrice)
    (poolModifyRegionAmountResult f evm false p sqrtPrice)

theorem poolModifyInsideFinish {f : Frame} {evm : State} {id sqrtPrice : UInt256} {p : PoolModifyParams} {old : Value}
    (hc : PoolModifyContext f id p)
    (h0 : f.locals.get? "__c23" = some (.int (EVM.signed (poolModifyRegionWord false p sqrtPrice))))
    (h1 : f.locals.get? "__c26" = some (.int (EVM.signed (poolModifyRegionWord true p sqrtPrice))))
    (hd : f.locals.get? "delta" = some old) :
    ExecBlock config f evm (poolModifyInsidePackBlock ++ poolModifyLiquidityBlock)
      (poolModifyInsideFinishResult f evm id p sqrtPrice) := by
  have hpack := balanceDeltaAssign (f := f) (evm := evm) (ret := "__c27") hc.contract
    (evalLocalValue h0) (evalLocalValue h1) hd (by decide)
  have hcf : PoolModifyContext (poolModifyInsidePackFrame f p sqrtPrice) id p :=
    (hc.insert "__c27" _ (by decide)).insert "delta" _ (by decide)
  exact execBlock_append hpack (poolModifyLiquidity (evm := evm) hcf)

theorem poolModifyInsideSecond {f : Frame} {evm : State} {id sqrtPrice : UInt256} {p : PoolModifyParams} {old : Value}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (hprice : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat))) (hb : sqrtPrice.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (h0 : f.locals.get? "__c23" = some (.int (EVM.signed (poolModifyRegionWord false p sqrtPrice))))
    (hd : f.locals.get? "delta" = some old) :
    ExecBlock config f evm poolModifyInsideSecondBlock (poolModifyInsideSecondResult f evm id p sqrtPrice) := by
  have hsecond := poolModifyRegionAmount (evm := evm) hc ht hprice hb hdlo hdhi true
  apply execBlock_continue hsecond
  intro f1 post hpost
  obtain ⟨rfl, hstate⟩ := poolModifyRegionAmountResult_normal hpost
  subst post
  apply poolModifyInsideFinish (poolModifyRegionAmountFrame_context hc true sqrtPrice)
  · exact (poolModifyRegionAmountFrame_get _ true _ _ "__c23" (by decide) (by decide) (by decide)).trans h0
  · exact store_get_self _ _ _
  · exact (poolModifyRegionAmountFrame_get _ true _ _ "delta" (by decide) (by decide) (by decide)).trans hd

theorem poolModifyInside {f : Frame} {evm : State} {id sqrtPrice : UInt256} {p : PoolModifyParams} {old : Value}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (hprice : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat))) (hb : sqrtPrice.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some old) :
    ExecBlock config f evm poolModifyInsideBlock (poolModifyInsideResult f evm id p sqrtPrice) := by
  have hfirst := poolModifyRegionAmount (evm := evm) hc ht hprice hb hdlo hdhi false
  apply execBlock_continue hfirst
  intro f1 post hpost
  obtain ⟨rfl, hstate⟩ := poolModifyRegionAmountResult_normal hpost
  subst post
  exact poolModifyInsideSecond (poolModifyRegionAmountFrame_context hc false sqrtPrice) ht
    ((poolModifyRegionAmountFrame_get _ false _ _ "sqrtPriceX96" (by decide) (by decide) (by decide)).trans hprice)
    hb hdlo hdhi (store_get_self _ _ _)
    ((poolModifyRegionAmountFrame_get _ false _ _ "delta" (by decide) (by decide) (by decide)).trans hd)

end Benchmarks.UniswapV4PoolManager
