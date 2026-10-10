import Benchmarks.UniswapV4PoolManager.Amount0Words
import Benchmarks.UniswapV4PoolManager.SignedAmountSource
import Benchmarks.UniswapV4PoolManager.CheckedAmountSource

open Ethereum
namespace Benchmarks.UniswapV4PoolManager

abbrev signedAmount0Round := signedAmountRound
def signedAmount0Unsigned (a b : UInt256) (delta : Int) : UInt256 :=
  amount0Word a b (liquidityMagnitude delta) (signedAmount0Round delta)
def signedAmount0Fits (a b : UInt256) (delta : Int) : Prop :=
  amount0Fits a b (liquidityMagnitude delta) (signedAmount0Round delta) ∧
    (signedAmount0Unsigned a b delta).toNat < 2^255
instance (a b : UInt256) (delta : Int) : Decidable (signedAmount0Fits a b delta) :=
  inferInstanceAs (Decidable (_ ∧ _))
def signedAmount0Word (a b : UInt256) (delta : Int) : UInt256 :=
  checkedAmountReturnWord (signedAmount0Unsigned a b delta) (signedAmount0Round delta)

end Benchmarks.UniswapV4PoolManager
