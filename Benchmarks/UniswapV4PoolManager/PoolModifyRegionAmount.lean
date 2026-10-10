import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.CheckedSignedAmount
import Benchmarks.UniswapV4PoolManager.TickSqrtSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyRegionTickName (one : Bool) : Ident := if one then "tickLower" else "tickUpper"
def poolModifyRegionTick (one : Bool) (p : PoolModifyParams) : Int := EVM.signed (if one then p.lower else p.upper)
def poolModifyRegionSqrtRet (one : Bool) : Ident := if one then "__c24" else "__c21"
def poolModifyRegionAmountRet (one : Bool) : Ident := if one then "__c25" else "__c22"
def poolModifyRegionCastRet (one : Bool) : Ident := if one then "__c26" else "__c23"
def poolModifyRegionPrice (one : Bool) (p : PoolModifyParams) : UInt256 := tickSqrtPrice (poolModifyRegionTick one p)
def poolModifyRegionA (one : Bool) (p : PoolModifyParams) (sqrtPrice : UInt256) : UInt256 :=
  if one then poolModifyRegionPrice one p else sqrtPrice
def poolModifyRegionB (one : Bool) (p : PoolModifyParams) (sqrtPrice : UInt256) : UInt256 :=
  if one then sqrtPrice else poolModifyRegionPrice one p
def poolModifyRegionWord (one : Bool) (p : PoolModifyParams) (sqrtPrice : UInt256) : UInt256 :=
  signedAmountWord one (poolModifyRegionA one p sqrtPrice) (poolModifyRegionB one p sqrtPrice) p.delta
def poolModifyRegionAmountBlock (one : Bool) : List Stmt :=
  .internalCall "TickMath_getSqrtPriceAtTick" [.var (poolModifyRegionTickName one)] (poolModifyRegionSqrtRet one) ::
  checkedSignedAmountBlock one
    (if one then .var (poolModifyRegionSqrtRet one) else .var "sqrtPriceX96")
    (if one then .var "sqrtPriceX96" else .var (poolModifyRegionSqrtRet one))
    (.var "liquidityDelta") (poolModifyRegionAmountRet one) (poolModifyRegionCastRet one)
def poolModifyRegionAmountResult (f : Frame) (evm : State) (one : Bool) (p : PoolModifyParams)
    (sqrtPrice : UInt256) : ExecResult :=
  checkedSignedAmountResult (wordLocal f (poolModifyRegionSqrtRet one) (poolModifyRegionPrice one p)) evm one
    (poolModifyRegionA one p sqrtPrice) (poolModifyRegionB one p sqrtPrice) p.delta
    (poolModifyRegionAmountRet one) (poolModifyRegionCastRet one)
def poolModifyRegionAmountFrame (f : Frame) (one : Bool) (p : PoolModifyParams) (sqrtPrice : UInt256) : Frame :=
  checkedSignedAmountFrame (wordLocal f (poolModifyRegionSqrtRet one) (poolModifyRegionPrice one p))
    (poolModifyRegionAmountRet one) (poolModifyRegionCastRet one) (poolModifyRegionWord one p sqrtPrice)

theorem poolModifyRegionAmount {f : Frame} {evm : State} {id sqrtPrice : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (hprice : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat))) (hb : sqrtPrice.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127) (one : Bool) :
    ExecBlock config f evm (poolModifyRegionAmountBlock one) (poolModifyRegionAmountResult f evm one p sqrtPrice) := by
  have htick : f.locals.get? (poolModifyRegionTickName one) = some (.int (poolModifyRegionTick one p)) := by
    cases one with
    | false => exact hc.upper
    | true => exact hc.lower
  have hbound : (poolModifyRegionTick one p).natAbs ≤ 887272 := by
    cases one with
    | false => exact (poolTicksValid_bounds ht).2
    | true => exact (poolTicksValid_bounds ht).1
  have hcall := tickSqrtCall (f := f) (evm := evm) hc.contract (evalLocalValue htick)
    (by omega : (poolModifyRegionTick one p).natAbs < 2^256) (poolModifyRegionSqrtRet one)
  rw [if_pos hbound] at hcall
  let f1 := wordLocal f (poolModifyRegionSqrtRet one) (poolModifyRegionPrice one p)
  have hc1 : PoolModifyContext f1 id p := hc.insert (poolModifyRegionSqrtRet one) _ (by cases one <;> decide)
  have hp1 : f1.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)) :=
    (store_get_ne _ _ (by cases one <;> decide : (poolModifyRegionSqrtRet one == "sqrtPriceX96") = false)).trans hprice
  have ht1 : f1.locals.get? (poolModifyRegionSqrtRet one) = some (.int (Int.ofNat (poolModifyRegionPrice one p).toNat)) :=
    store_get_self _ _ _
  have hpr : (poolModifyRegionPrice one p).toNat < 2^160 := tickSqrtPrice_lt_160 hbound
  apply ExecBlock.consNormal hcall
  apply checkedSignedAmount hc1.contract
  · dsimp only [poolModifyRegionA]
    split_ifs <;> assumption
  · dsimp only [poolModifyRegionB]
    split_ifs <;> assumption
  · exact hdlo
  · exact hdhi
  · dsimp only [poolModifyRegionA]
    split_ifs <;> first | exact evalLocalValue hp1 | exact evalLocalValue ht1
  · dsimp only [poolModifyRegionB]
    split_ifs <;> first | exact evalLocalValue hp1 | exact evalLocalValue ht1
  · exact evalLocalValue hc1.liquidityDelta

theorem poolModifyRegionAmountResult_normal {f f' : Frame} {evm post : State} {one : Bool}
    {p : PoolModifyParams} {sqrtPrice : UInt256}
    (h : poolModifyRegionAmountResult f evm one p sqrtPrice = .ok f' post) :
    f' = poolModifyRegionAmountFrame f one p sqrtPrice ∧ post = evm := checkedSignedAmountResult_normal h

theorem poolModifyRegionAmountFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (one : Bool) (sqrtPrice : UInt256) :
    PoolModifyContext (poolModifyRegionAmountFrame f one p sqrtPrice) id p :=
  ((hc.insert (poolModifyRegionSqrtRet one) _ (by cases one <;> decide)).insert (poolModifyRegionAmountRet one)
    _ (by cases one <;> decide)).insert (poolModifyRegionCastRet one) _ (by cases one <;> decide)

theorem poolModifyRegionAmountFrame_get (f : Frame) (one : Bool) (p : PoolModifyParams) (sqrtPrice : UInt256)
    (name : Ident) (hs : (poolModifyRegionSqrtRet one == name) = false)
    (ha : (poolModifyRegionAmountRet one == name) = false) (hc : (poolModifyRegionCastRet one == name) = false) :
    (poolModifyRegionAmountFrame f one p sqrtPrice).locals.get? name = f.locals.get? name :=
  store_get_ne3 _ _ _ _ hs ha hc

end Benchmarks.UniswapV4PoolManager
