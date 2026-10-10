import Benchmarks.UniswapV4PoolManager.BalanceDeltaAddTrace
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- Reuse the complete add-delta trace with counters measured from its own entry. -/
theorem balanceDeltaAddCostTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw a b j0 j1 j2 x4 x5 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨6046⟩ (j0 :: j1 :: j2 :: a :: x4 :: x5 :: b :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (balanceDeltaCombineWord false a b))] ∧ ∃ k' C', C ≤ C' ∧
        RD (deployedRuntime v) I g s0 ⟨6084⟩
          (EVM.wordOfInt (balanceDeltaCombineAmount false true a b) ::
            EVM.wordOfInt (balanceDeltaCombineAmount false false a b) :: x4 :: x5 :: b :: R)
          mem aw rdata post.accountMap k' C')
      (balanceDeltaCombineResult f evm false a b) := by
  by_cases hf : balanceDeltaCombineFits false a b
  · rw [balanceDeltaCombineResult, if_pos hf]
    refine ⟨rfl, rfl, RD_retainCost ?_ h⟩
    intro budget start hin
    have hr := balanceDeltaAddTrace f v hstack hin
    rw [balanceDeltaCombineResult, if_pos hf] at hr
    exact hr.2.2
  · have hr := balanceDeltaAddTrace f v hstack h
    rw [balanceDeltaCombineResult, if_neg hf] at hr ⊢
    exact hr

end Benchmarks.UniswapV4PoolManager
