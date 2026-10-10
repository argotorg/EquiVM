import Benchmarks.UniswapV4PoolManager.Amount1Words
import Benchmarks.UniswapV4PoolManager.SignedAmountSource
import Benchmarks.UniswapV4PoolManager.CheckedAmountSource

open Ethereum
namespace Benchmarks.UniswapV4PoolManager

abbrev signedAmount1Round := signedAmountRound
def signedAmount1Unsigned (a b : UInt256) (delta : Int) : UInt256 :=
  amount1Word a b (liquidityMagnitude delta) (signedAmount1Round delta)
def signedAmount1Fits (a b : UInt256) (delta : Int) : Prop :=
  amount1Fits a b (liquidityMagnitude delta) ∧
    (signedAmount1Unsigned a b delta).toNat < 2^255
instance (a b : UInt256) (delta : Int) : Decidable (signedAmount1Fits a b delta) :=
  inferInstanceAs (Decidable (_ ∧ _))
def signedAmount1Word (a b : UInt256) (delta : Int) : UInt256 :=
  checkedAmountReturnWord (signedAmount1Unsigned a b delta) (signedAmount1Round delta)

end Benchmarks.UniswapV4PoolManager
