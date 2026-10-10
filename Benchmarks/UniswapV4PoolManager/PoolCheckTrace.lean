import Benchmarks.UniswapV4PoolManager.Slot0Source
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolCheckTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret slot : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+3 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13686⟩ (slot :: ret :: R) mem aw rdata σ k C) :
    (slot0SqrtPriceWord (solcSlotWordAt slot σ I) = ⟨0⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (slot0SqrtPriceWord (solcSlotWordAt slot σ I) ≠ ⟨0⟩ ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C') := by
  have he : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (solcSlotWordAt slot σ I) = slot0SqrtPriceWord (solcSlotWordAt slot σ I) :=
    u256_land_comm _ _
  by_cases hz : slot0SqrtPriceWord (solcSlotWordAt slot σ I) = ⟨0⟩
  · obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_13686_taken (by simp; omega)
      (by change UInt256.isZero (UInt256.land _ (solcSlotWordAt slot σ I)) ≠ ⟨0⟩; rw [he, hz]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨hz, poolManagerBlocks.poolManager_block_13716 (by change R.length+3 ≤ 1024; exact hstack) rd1⟩
  · obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_13686_fallthrough (by simp; omega)
      (by change UInt256.isZero (UInt256.land _ (solcSlotWordAt slot σ I)) = ⟨0⟩; rw [he]; exact isZero_eq_zero_of_ne hz) h
    have rd2 := poolManagerBlocks.poolManager_block_13715 (by simp; omega) hret rd1
    exact .inr ⟨hz, _, _, rd2⟩

end Benchmarks.UniswapV4PoolManager
