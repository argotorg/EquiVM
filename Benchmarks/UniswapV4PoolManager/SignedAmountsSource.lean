import Benchmarks.UniswapV4PoolManager.SignedAmount0Source
import Benchmarks.UniswapV4PoolManager.SignedAmount1Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def signedAmountName (one : Bool) : Ident :=
  if one then "SqrtPriceMath_getAmount1Delta" else "SqrtPriceMath_getAmount0Delta"
def signedAmountFits (one : Bool) (a b : UInt256) (delta : Int) : Prop :=
  if one then signedAmount1Fits a b delta else signedAmount0Fits a b delta
instance (one : Bool) (a b : UInt256) (delta : Int) : Decidable (signedAmountFits one a b delta) :=
  inferInstanceAs (Decidable (if one then signedAmount1Fits a b delta else signedAmount0Fits a b delta))
def signedAmountWord (one : Bool) (a b : UInt256) (delta : Int) : UInt256 :=
  if one then signedAmount1Word a b delta else signedAmount0Word a b delta

theorem signedAmountCall {f : Frame} {evm : State} {a b : UInt256} {delta : Int} {ea eb ed : Expr}
    (hf : f.contract = contract) (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hea : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (heb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hed : evalExpr? config f evm ed = .ok (.int delta)) (one : Bool) (ret : Ident) :
    ExecStmt config f evm (.internalCall (signedAmountName one) [ea, eb, ed] ret)
      (if signedAmountFits one a b delta then
        .ok {f with locals := f.locals.insert ret (.int (EVM.signed (signedAmountWord one a b delta)))} evm
       else .reverted) := by
  cases one with
  | false => exact signedAmount0Call hf ha hb hdlo hdhi hea heb hed ret
  | true => exact signedAmount1Call hf hdlo hdhi hea heb hed ret

end Benchmarks.UniswapV4PoolManager
