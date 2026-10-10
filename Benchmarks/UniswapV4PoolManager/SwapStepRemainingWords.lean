import Benchmarks.UniswapV4PoolManager.SwapStepFeeWords
import Benchmarks.UniswapV4PoolManager.WordSubAdd

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapStepRemainingWord (remaining : UInt256) : UInt256 := UInt256.sub ⟨0⟩ remaining

def swapStepRemainingFeeWord (remaining amount : UInt256) : UInt256 :=
  UInt256.sub (swapStepRemainingWord remaining) amount

theorem swapStepRemainingFeeWord_eq (remaining amount : UInt256) :
    swapStepRemainingFeeWord remaining amount = UInt256.sub ⟨0⟩ (remaining+amount) :=
  wordSubSub ⟨0⟩ remaining amount

abbrev swapStepAvailableFits (remaining fee : UInt256) : Prop :=
  fullMathFits (swapStepRemainingWord remaining) (swapStepFeeComplement fee) fullMathPPM

def swapStepAvailableWord (remaining fee : UInt256) : UInt256 :=
  fullMathWord (swapStepRemainingWord remaining) (swapStepFeeComplement fee) fullMathPPM

end Benchmarks.UniswapV4PoolManager
