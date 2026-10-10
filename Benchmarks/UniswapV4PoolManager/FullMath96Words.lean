import Benchmarks.UniswapV4PoolManager.FullMathGeneralWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def fullMathQ96 : UInt256 := UInt256.ofNat (2^96)
theorem fullMathQ96_toNat : fullMathQ96.toNat = 2^96 := by decide +kernel
theorem fullMathQ96_ne : fullMathQ96 ≠ ⟨0⟩ := by decide +kernel
theorem fullMath96_twos : fullMathTwos fullMathQ96 = fullMathQ96 := by decide +kernel
theorem fullMath96_odd : fullMathOdd fullMathQ96 = ⟨1⟩ := by decide +kernel
theorem fullMath96_twosInverse : fullMathTwosInverse fullMathQ96 = UInt256.ofNat (2^160) := by
  decide +kernel

theorem fullMath96Word_eq (a b : UInt256) : fullMathWord a b fullMathQ96 =
    if fullMathHigh a b = ⟨0⟩ then UInt256.shiftRight (fullMathLow a b) (UInt256.ofNat 96)
    else UInt256.lor (UInt256.shiftRight (fullMathReducedLow a b fullMathQ96) (UInt256.ofNat 96))
      (UInt256.shiftLeft (fullMathReducedHigh a b fullMathQ96) (UInt256.ofNat 160)) := by
  unfold fullMathWord
  rw [fullMath96_odd, fullMathInverse_one]
  rw [wordMulOne, fullMathWide, fullMath96_twos, fullMath96_twosInverse]
  simp only [fullMathQ96, wordDivPow2 _ (by decide : 96 < 256),
    wordMulPow2 _ (by decide : 160 < 256)]

end Benchmarks.UniswapV4PoolManager
