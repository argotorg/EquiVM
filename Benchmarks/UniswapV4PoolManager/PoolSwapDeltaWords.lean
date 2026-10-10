import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource
import Benchmarks.UniswapV4PoolManager.SafeCast128Source
import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapCalculatedFirst (zeroForOne : Bool) (specified : UInt256) : Bool :=
  zeroForOne != decide (EVM.signed specified < 0)

def poolSwapDeltaArg (calculated : Bool) (specified remaining amount : UInt256) : UInt256 :=
  if calculated then amount else UInt256.sub specified remaining

def poolSwapDeltaWord (calculatedFirst : Bool) (specified remaining calculated : UInt256) : UInt256 :=
  balanceDeltaWord (poolSwapDeltaArg calculatedFirst specified remaining calculated)
    (poolSwapDeltaArg (!calculatedFirst) specified remaining calculated)

def poolSwapDeltaFits (calculatedFirst : Bool) (specified remaining calculated : UInt256) : Prop :=
  signedFits ⟨128, by decide⟩ (EVM.signed (poolSwapDeltaArg calculatedFirst specified remaining calculated)) ∧
    signedFits ⟨128, by decide⟩ (EVM.signed (poolSwapDeltaArg (!calculatedFirst) specified remaining calculated))
instance (cf : Bool) (specified remaining calculated : UInt256) : Decidable (poolSwapDeltaFits cf specified remaining calculated) :=
  inferInstanceAs (Decidable (_ ∧ _))

def poolSwapDeltaExpr (calculated : Bool) : Expr :=
  if calculated then .var "amountCalculated" else
    .cast (.binary .sub (.field (.var "params") "amountSpecified") (.var "amountSpecifiedRemaining"))
      (.elem (.int (.sint ⟨256, by decide⟩)))

def poolSwapDeltaName0 (cf : Bool) : Ident := if cf then "__c26" else "__c29"
def poolSwapDeltaName1 (cf : Bool) : Ident := if cf then "__c27" else "__c30"
def poolSwapDeltaName2 (cf : Bool) : Ident := if cf then "__c28" else "__c31"

def poolSwapDeltaBranch (cf : Bool) : List Stmt :=
  [.internalCall "SafeCast_toInt128" [poolSwapDeltaExpr cf] (poolSwapDeltaName0 cf),
   .internalCall "SafeCast_toInt128" [poolSwapDeltaExpr (!cf)] (poolSwapDeltaName1 cf),
   .internalCall "toBalanceDelta" [.var (poolSwapDeltaName0 cf), .var (poolSwapDeltaName1 cf)] (poolSwapDeltaName2 cf),
   .assign .localVar {base := "swapDelta"} (.var (poolSwapDeltaName2 cf))]

def poolSwapDeltaCondition : Expr := .binary .ne (.var "zeroForOne")
  (.binary .lt (.field (.var "params") "amountSpecified") (.intLit 0))

theorem poolSwapFunction_delta : poolSwapFunction.body[34]! =
    .ite poolSwapDeltaCondition (poolSwapDeltaBranch true) (poolSwapDeltaBranch false) := rfl

end Benchmarks.UniswapV4PoolManager
