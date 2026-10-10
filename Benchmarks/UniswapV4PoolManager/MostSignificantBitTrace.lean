import Benchmarks.UniswapV4PoolManager.MostSignificantBit
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_066

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem mostSignificantBitTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret x : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23515⟩ (x :: ret :: R) mem aw rdata σ k C) :
    (x = ⟨0⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (x ≠ ⟨0⟩ ∧ RD (deployedRuntime v) I g s0 ret (mostSignificantBit x :: R)
      mem aw rdata σ (k + 54) (C + 172)) := by
  by_cases hz : x = ⟨0⟩
  · have rd1 := poolManagerBlocks.poolManager_block_23515_taken (by simp; omega)
      (by rw [hz]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨hz, emptyRevert v (by change R.length + 1 + 1 + 2 ≤ 1024; omega) rd1⟩
  · have rd1 := poolManagerBlocks.poolManager_block_23515_fallthrough (by simp; omega)
      (isZero_eq_zero_of_ne hz) h
    have rd2 := poolManagerBlocks.poolManager_block_23522 hstack hret rd1
    change RD (deployedRuntime v) I g s0 ret (mostSignificantBit x :: R)
      mem aw rdata σ (k + 5 + 49) (C + 20 + 152) at rd2
    exact .inr ⟨hz, by simpa only [Nat.add_assoc] using rd2⟩

end Benchmarks.UniswapV4PoolManager
