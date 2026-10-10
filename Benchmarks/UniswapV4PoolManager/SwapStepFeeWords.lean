import Benchmarks.UniswapV4PoolManager.FullMathPPMWords
import Benchmarks.UniswapV4PoolManager.FullMathRoundWords

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

def swapStepFeeComplement (fee : UInt256) : UInt256 := UInt256.sub fullMathPPM fee
abbrev swapStepFeeFits (amount fee : UInt256) : Prop :=
  fullMathRoundFits amount fee (swapStepFeeComplement fee)
instance (amount fee : UInt256) : Decidable (swapStepFeeFits amount fee) :=
  inferInstanceAs (Decidable (fullMathRoundFits _ _ _))
def swapStepFeeWord (amount fee : UInt256) : UInt256 :=
  fullMathRoundWord amount fee (swapStepFeeComplement fee)

def swapStepTargetFeeFits (amount fee : UInt256) : Prop :=
  fee = fullMathPPM ∨ swapStepFeeFits amount fee
instance (amount fee : UInt256) : Decidable (swapStepTargetFeeFits amount fee) :=
  inferInstanceAs (Decidable (_ ∨ _))
def swapStepTargetFeeWord (amount fee : UInt256) : UInt256 :=
  if fee = fullMathPPM then amount else swapStepFeeWord amount fee

end Benchmarks.UniswapV4PoolManager
