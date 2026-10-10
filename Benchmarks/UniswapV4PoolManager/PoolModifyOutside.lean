import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.CheckedSignedAmount
import Benchmarks.UniswapV4PoolManager.BalanceDeltaAssign
import Benchmarks.UniswapV4PoolManager.TickSqrtSource
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyOutsideLowerRet (one : Bool) : Ident := if one then "__c29" else "__c16"
def poolModifyOutsideUpperRet (one : Bool) : Ident := if one then "__c30" else "__c17"
def poolModifyOutsideAmountRet (one : Bool) : Ident := if one then "__c31" else "__c18"
def poolModifyOutsideCastRet (one : Bool) : Ident := if one then "__c32" else "__c19"
def poolModifyOutsidePackRet (one : Bool) : Ident := if one then "__c33" else "__c20"
def poolModifyOutsidePackBlock (one : Bool) : List Stmt :=
  [.internalCall "toBalanceDelta"
    [if one then .intLit 0 else .var (poolModifyOutsideCastRet one),
     if one then .var (poolModifyOutsideCastRet one) else .intLit 0] (poolModifyOutsidePackRet one),
   .assign .localVar {base := "delta"} (.var (poolModifyOutsidePackRet one))]
def poolModifyOutsidePricesBlock (one : Bool) : List Stmt :=
  [.internalCall "TickMath_getSqrtPriceAtTick" [.var "tickLower"] (poolModifyOutsideLowerRet one),
   .internalCall "TickMath_getSqrtPriceAtTick" [.var "tickUpper"] (poolModifyOutsideUpperRet one)]
def poolModifyOutsideTailBlock (one : Bool) : List Stmt :=
  checkedSignedAmountBlock one (.var (poolModifyOutsideLowerRet one)) (.var (poolModifyOutsideUpperRet one))
    (.var "liquidityDelta") (poolModifyOutsideAmountRet one) (poolModifyOutsideCastRet one) ++
  poolModifyOutsidePackBlock one
def poolModifyOutsideBlock (one : Bool) : List Stmt :=
  poolModifyOutsidePricesBlock one ++ poolModifyOutsideTailBlock one
def poolModifyOutsideWord (one : Bool) (p : PoolModifyParams) : UInt256 :=
  signedAmountWord one (tickSqrtPrice (EVM.signed p.lower)) (tickSqrtPrice (EVM.signed p.upper)) p.delta
def poolModifyOutsidePricesFrame (f : Frame) (one : Bool) (p : PoolModifyParams) : Frame :=
  wordLocal (wordLocal f (poolModifyOutsideLowerRet one) (tickSqrtPrice (EVM.signed p.lower)))
    (poolModifyOutsideUpperRet one) (tickSqrtPrice (EVM.signed p.upper))
def poolModifyOutsideTailResult (f : Frame) (evm : State) (one : Bool) (p : PoolModifyParams) : ExecResult :=
  continueBlockResult (fun f1 post => .ok (balanceDeltaAssignFrame f1 (poolModifyOutsidePackRet one) "delta"
    (if one then ⟨0⟩ else poolModifyOutsideWord one p) (if one then poolModifyOutsideWord one p else ⟨0⟩)) post)
    (checkedSignedAmountResult f evm one
      (tickSqrtPrice (EVM.signed p.lower)) (tickSqrtPrice (EVM.signed p.upper)) p.delta
      (poolModifyOutsideAmountRet one) (poolModifyOutsideCastRet one))
def poolModifyOutsideResult (f : Frame) (evm : State) (one : Bool) (p : PoolModifyParams) : ExecResult :=
  poolModifyOutsideTailResult (poolModifyOutsidePricesFrame f one p) evm one p

theorem poolModifyOutsidePack {f : Frame} {evm : State} {w : UInt256} {one : Bool} {old : Value}
    (hf : f.contract = contract)
    (hw : f.locals.get? (poolModifyOutsideCastRet one) = some (.int (EVM.signed w)))
    (hd : f.locals.get? "delta" = some old) :
    ExecBlock config f evm (poolModifyOutsidePackBlock one)
      (.ok (balanceDeltaAssignFrame f (poolModifyOutsidePackRet one) "delta"
        (if one then ⟨0⟩ else w) (if one then w else ⟨0⟩)) evm) := by
  have hz : evalExpr? config f evm (.intLit 0) = .ok (.int (EVM.signed (⟨0⟩ : UInt256))) := by
    simp only [evalExpr?, pure]; rfl
  cases one with
  | false => exact balanceDeltaAssign hf (evalLocalValue hw) hz hd (by decide)
  | true => exact balanceDeltaAssign hf hz (evalLocalValue hw) hd (by decide)

theorem poolModifyOutsidePrices {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper) (one : Bool) :
    ExecBlock config f evm (poolModifyOutsidePricesBlock one) (.ok (poolModifyOutsidePricesFrame f one p) evm) := by
  let f0 := wordLocal f (poolModifyOutsideLowerRet one) (tickSqrtPrice (EVM.signed p.lower))
  have hticks := poolTicksValid_bounds ht
  have hlo := tickSqrtCall (f := f) (evm := evm) hc.contract (evalLocalValue hc.lower)
    (by omega : (EVM.signed p.lower).natAbs < 2^256) (poolModifyOutsideLowerRet one)
  rw [if_pos hticks.1] at hlo
  have hc0 : PoolModifyContext f0 id p := hc.insert (poolModifyOutsideLowerRet one) _ (by exact Bool.rec (by decide) (by decide) one)
  have hup := tickSqrtCall (f := f0) (evm := evm) hc0.contract (evalLocalValue hc0.upper)
    (by omega : (EVM.signed p.upper).natAbs < 2^256) (poolModifyOutsideUpperRet one)
  rw [if_pos hticks.2] at hup
  exact ExecBlock.consNormal hlo (execBlock_singleton hup)

theorem poolModifyOutsideTail {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams} {one : Bool} {old : Value}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (ha : f.locals.get? (poolModifyOutsideLowerRet one) = some (.int (Int.ofNat (tickSqrtPrice (EVM.signed p.lower)).toNat)))
    (hb : f.locals.get? (poolModifyOutsideUpperRet one) = some (.int (Int.ofNat (tickSqrtPrice (EVM.signed p.upper)).toNat)))
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127) (hd : f.locals.get? "delta" = some old) :
    ExecBlock config f evm (poolModifyOutsideTailBlock one) (poolModifyOutsideTailResult f evm one p) := by
  have hticks := poolTicksValid_bounds ht
  have hchecked := checkedSignedAmount (f := f) (evm := evm) hc.contract
    (tickSqrtPrice_lt_160 hticks.1) (tickSqrtPrice_lt_160 hticks.2) hdlo hdhi
    (evalLocalValue ha) (evalLocalValue hb) (evalLocalValue hc.liquidityDelta)
    one (poolModifyOutsideAmountRet one) (poolModifyOutsideCastRet one)
  apply execBlock_continue hchecked
  intro f1 post hpost
  obtain ⟨rfl, hstate⟩ := checkedSignedAmountResult_normal hpost
  subst post
  apply poolModifyOutsidePack (f := checkedSignedAmountFrame f (poolModifyOutsideAmountRet one)
    (poolModifyOutsideCastRet one) (poolModifyOutsideWord one p)) hc.contract
  · exact store_get_self _ _ _
  · exact (store_get_ne2 _ _ _
      (by exact Bool.rec (by decide) (by decide) one : (poolModifyOutsideAmountRet one == "delta") = false)
      (by exact Bool.rec (by decide) (by decide) one : (poolModifyOutsideCastRet one == "delta") = false)).trans hd

theorem poolModifyOutsidePricesFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (one : Bool) : PoolModifyContext (poolModifyOutsidePricesFrame f one p) id p :=
  (hc.insert (poolModifyOutsideLowerRet one) _ (by cases one <;> decide)).insert (poolModifyOutsideUpperRet one)
    _ (by cases one <;> decide)

theorem poolModifyOutside {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams} {old : Value}
    (hc : PoolModifyContext f id p) (ht : poolTicksValid p.lower p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hd : f.locals.get? "delta" = some old) (one : Bool) :
    ExecBlock config f evm (poolModifyOutsideBlock one) (poolModifyOutsideResult f evm one p) := by
  have hpre := poolModifyOutsidePrices (evm := evm) hc ht one
  have htail := poolModifyOutsideTail (evm := evm) (one := one) (poolModifyOutsidePricesFrame_context hc one) ht
    ((store_get_ne _ _ (by cases one <;> decide : (poolModifyOutsideUpperRet one == poolModifyOutsideLowerRet one) = false)).trans
      (store_get_self _ _ _)) (store_get_self _ _ _) hdlo hdhi
    ((store_get_ne2 _ _ _ (by cases one <;> decide : (poolModifyOutsideLowerRet one == "delta") = false)
      (by cases one <;> decide : (poolModifyOutsideUpperRet one == "delta") = false)).trans hd)
  exact execBlock_append hpre htail

end Benchmarks.UniswapV4PoolManager
