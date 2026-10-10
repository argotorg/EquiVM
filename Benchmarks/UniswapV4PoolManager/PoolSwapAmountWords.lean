import Benchmarks.UniswapV4PoolManager.PoolSwapStepWords
import Benchmarks.UniswapV4PoolManager.WordSignedSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapInputAmountFits (s : PoolSwapStepWords) (calculated : UInt256) : Prop :=
  (s.amountIn+s.feeAmount).toNat < 2^255 ∧ s.amountOut.toNat < 2^255 ∧
    int256Fits (EVM.signed calculated+EVM.signed s.amountOut)
instance (s : PoolSwapStepWords) (calculated : UInt256) : Decidable (poolSwapInputAmountFits s calculated) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def poolSwapOutputAmountFits (s : PoolSwapStepWords) (calculated : UInt256) : Prop :=
  s.amountOut.toNat < 2^255 ∧ s.amountIn.toNat+s.feeAmount.toNat < UInt256.size ∧
    (s.amountIn+s.feeAmount).toNat < 2^255 ∧ int256Fits (EVM.signed calculated-EVM.signed (s.amountIn+s.feeAmount))
instance (s : PoolSwapStepWords) (calculated : UInt256) : Decidable (poolSwapOutputAmountFits s calculated) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def poolSwapRemainingAfter (s : PoolSwapStepWords) (specified remaining : UInt256) : UInt256 :=
  if 0 < EVM.signed specified then UInt256.sub remaining s.amountOut else remaining+(s.amountIn+s.feeAmount)

def poolSwapCalculatedAfter (s : PoolSwapStepWords) (specified calculated : UInt256) : UInt256 :=
  if 0 < EVM.signed specified then UInt256.sub calculated (s.amountIn+s.feeAmount) else calculated+s.amountOut

def poolSwapInputAmountFrame (f : Frame) (s : PoolSwapStepWords) (remaining calculated : UInt256) : Frame :=
  let f1 := valueLocal f "__c18" (.int (EVM.signed (s.amountIn+s.feeAmount)))
  let f2 := valueLocal f1 "amountSpecifiedRemaining" (.int (EVM.signed (remaining+(s.amountIn+s.feeAmount))))
  let f3 := valueLocal f2 "__c19" (.int (EVM.signed s.amountOut))
  valueLocal f3 "amountCalculated" (.int (EVM.signed (calculated+s.amountOut)))

def poolSwapOutputAmountFrame (f : Frame) (s : PoolSwapStepWords) (remaining calculated : UInt256) : Frame :=
  let f1 := valueLocal f "__c16" (.int (EVM.signed s.amountOut))
  let f2 := valueLocal f1 "amountSpecifiedRemaining" (.int (EVM.signed (UInt256.sub remaining s.amountOut)))
  let f3 := valueLocal f2 "__c17" (.int (EVM.signed (s.amountIn+s.feeAmount)))
  valueLocal f3 "amountCalculated" (.int (EVM.signed (UInt256.sub calculated (s.amountIn+s.feeAmount))))

end Benchmarks.UniswapV4PoolManager
