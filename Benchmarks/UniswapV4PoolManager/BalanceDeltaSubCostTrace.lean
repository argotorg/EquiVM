import Benchmarks.UniswapV4PoolManager.BalanceDeltaSubTrace
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem balanceDeltaSubCostTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨17855⟩ (a :: b :: ret :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values => post = evm ∧
      values = some [.int (EVM.signed (balanceDeltaCombineWord true a b))] ∧ ∃ k' C', C ≤ C' ∧
        RD (deployedRuntime v) I g s0 ret (balanceDeltaCombineWord true a b :: R)
          mem aw rdata post.accountMap k' C')
      (balanceDeltaCombineResult f evm true a b) := by
  by_cases hf : balanceDeltaCombineFits true a b
  · rw [balanceDeltaCombineResult, if_pos hf]
    refine ⟨rfl, rfl, RD_retainCost ?_ h⟩
    intro budget start hin
    have hr := balanceDeltaSubTrace f v hstack hret hin
    rw [balanceDeltaCombineResult, if_pos hf] at hr
    exact hr.2.2
  · have hr := balanceDeltaSubTrace f v hstack hret h
    rw [balanceDeltaCombineResult, if_neg hf] at hr ⊢
    exact hr

end Benchmarks.UniswapV4PoolManager
