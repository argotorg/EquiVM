import Benchmarks.UniswapV4PoolManager.SwapStepWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem swapStepDirection_test (price target : UInt256) :
    UInt256.isZero (UInt256.lt price target) = if swapStepDirection price target then ⟨1⟩ else ⟨0⟩ := by
  by_cases hle : target.toNat ≤ price.toNat
  · rw [ult_zero hle]
    simp only [swapStepDirection, decide_eq_true hle, if_true]
    rfl
  · rw [ult_one (Nat.lt_of_not_ge hle)]
    simp only [swapStepDirection, decide_eq_false hle, Bool.false_eq_true, if_false]
    rfl

theorem swapStepExactInput_test (remaining : UInt256) :
    UInt256.eq (⟨0⟩ : UInt256) (UInt256.slt remaining ⟨0⟩) =
      if swapStepExactInput remaining then ⟨0⟩ else ⟨1⟩ := by
  rw [slt_signed]
  change UInt256.eq ⟨0⟩ (UInt256.fromBool (decide (EVM.signed remaining < 0))) = _
  by_cases hn : EVM.signed remaining < 0
  · simp only [swapStepExactInput, decide_eq_true hn, if_true]
    rfl
  · simp only [swapStepExactInput, decide_eq_false hn, Bool.false_eq_true, if_false]
    rfl

theorem swapTargetDirection_test (zeroForOne : Bool) :
    UInt256.land (UInt256.isZero (if zeroForOne then (⟨0⟩ : UInt256) else ⟨1⟩)) ⟨1⟩ =
      if zeroForOne then ⟨1⟩ else ⟨0⟩ := by
  cases zeroForOne <;> decide +kernel

end Benchmarks.UniswapV4PoolManager
