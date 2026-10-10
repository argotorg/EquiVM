import Benchmarks.UniswapV4PoolManager.FullMathGeneralWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def fullMathPPM : UInt256 := ⟨1000000⟩
theorem fullMathPPM_twos : fullMathTwos fullMathPPM = UInt256.ofNat (2^6) := by decide +kernel
theorem fullMathPPM_odd : fullMathOdd fullMathPPM = ⟨15625⟩ := by decide +kernel
theorem fullMathPPM_twosInverse : fullMathTwosInverse fullMathPPM = UInt256.ofNat (2^250) := by decide +kernel
theorem fullMathPPM_inverse : fullMathInverse ⟨15625⟩ =
    UInt256.ofNat 100666863372781004712562448662913058577844446188675931002367476554463484993849 := by
  native_decide

theorem fullMathPPM_wide (a b : UInt256) : fullMathWide a b fullMathPPM =
    UInt256.lor (UInt256.shiftRight (fullMathReducedLow a b fullMathPPM) (UInt256.ofNat 6))
      (UInt256.shiftLeft (fullMathReducedHigh a b fullMathPPM) (UInt256.ofNat 250)) := by
  rw [fullMathWide, fullMathPPM_twos, fullMathPPM_twosInverse,
    wordDivPow2 _ (by decide : 6 < 256), wordMulPow2 _ (by decide : 250 < 256)]

end Benchmarks.UniswapV4PoolManager
