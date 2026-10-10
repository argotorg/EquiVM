import Benchmarks.UniswapV4PoolManager.WordMulModSource
import Benchmarks.UniswapV4PoolManager.WordBorrowSource
import Benchmarks.UniswapV4PoolManager.WordPow2

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def fullMathMax : UInt256 := UInt256.ofNat (2^256-1)
def fullMathQ128 : UInt256 := UInt256.ofNat (2^128)
def fullMathLow (a b : UInt256) : UInt256 := UInt256.mul a b
def fullMathMM (a b : UInt256) : UInt256 := UInt256.mulMod a b fullMathMax
def fullMathHigh (a b : UInt256) : UInt256 :=
  UInt256.sub (UInt256.sub (fullMathMM a b) (fullMathLow a b))
    (UInt256.lt (fullMathMM a b) (fullMathLow a b))
def fullMath128Fits (a b : UInt256) : Prop := (fullMathHigh a b).toNat < 2^128
instance (a b : UInt256) : Decidable (fullMath128Fits a b) := inferInstanceAs (Decidable (_ < _))
def fullMath128Remainder (a b : UInt256) : UInt256 := UInt256.mulMod a b fullMathQ128
def fullMath128ReducedLow (a b : UInt256) : UInt256 :=
  UInt256.sub (fullMathLow a b) (fullMath128Remainder a b)
def fullMath128ReducedHigh (a b : UInt256) : UInt256 :=
  UInt256.sub (fullMathHigh a b) (UInt256.gt (fullMath128Remainder a b) (fullMathLow a b))
def fullMath128Wide (a b : UInt256) : UInt256 :=
  UInt256.lor (UInt256.div (fullMath128ReducedLow a b) fullMathQ128)
    (UInt256.mul (fullMath128ReducedHigh a b) fullMathQ128)
def fullMath128Word (a b : UInt256) : UInt256 :=
  if fullMathHigh a b = ⟨0⟩ then UInt256.div (fullMathLow a b) fullMathQ128 else fullMath128Wide a b

theorem fullMathQ128_toNat : fullMathQ128.toNat = 2^128 := by decide +kernel
theorem fullMathQ128_ne : fullMathQ128 ≠ ⟨0⟩ := by decide +kernel
theorem fullMathMax_ne : fullMathMax ≠ ⟨0⟩ := by decide +kernel

theorem fullMath128_div (x : UInt256) :
    UInt256.div x fullMathQ128 = UInt256.shiftRight x (UInt256.ofNat 128) :=
  wordDivPow2 x (by decide)

theorem fullMath128_mul (x : UInt256) :
    UInt256.mul x fullMathQ128 = UInt256.shiftLeft x (UInt256.ofNat 128) :=
  wordMulPow2 x (by decide)

end Benchmarks.UniswapV4PoolManager
