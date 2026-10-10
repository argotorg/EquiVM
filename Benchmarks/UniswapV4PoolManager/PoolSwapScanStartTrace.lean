import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_054
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.PoolStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapScanStartMemory (mem : ByteArray) (step price : UInt256) : ByteArray :=
  price.toByteArray.write 0 mem step.toNat 32

def poolSwapScanStartAW (aw step state params : UInt256) : UInt256 :=
  M (M (M (M aw state ⟨32⟩) step ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩) (params+UInt256.ofNat 32) ⟨32⟩

theorem poolSwapScanStartTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id price tick spacing step state fee x0 x1 params x3 x4 x6 x7 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (lte : Bool) (hstack : R.length+23 ≤ 1024)
    (hp : UInt256.land (memLoad state mem) solcAddrMask = price)
    (ht : UInt256.signextend (UInt256.ofNat 2)
      (memLoad (state+UInt256.ofNat 32) (poolSwapScanStartMemory mem step price)) = tick)
    (hs : UInt256.signextend (UInt256.ofNat 2)
      (memLoad (params+UInt256.ofNat 32) (poolSwapScanStartMemory mem step price)) = spacing)
    (h : RD (deployedRuntime v) I g s0 ⟨19169⟩
      ([x0, x1, params, x3, x4, fee, x6, x7, if lte then ⟨0⟩ else ⟨1⟩, step, poolSlot id, state] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19221⟩
      ([tick, spacing, ⟨0⟩, spacing, tick, spacing, poolSlot id, step, state, fee, if lte then ⟨0⟩ else ⟨1⟩,
        x0, x1, params, x3, x4, fee, x6, x7, if lte then ⟨0⟩ else ⟨1⟩, step, poolSlot id, state] ++ R)
      (poolSwapScanStartMemory mem step price) (poolSwapScanStartAW aw step state params) rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_19169 hstack h
  change UInt256.land (memLoad state mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = price at hp
  dsimp only [poolSwapScanStartMemory] at ht hs
  simp only [poolManagerBlocks.poolManager_block_19169_stack,
    poolManagerBlocks.poolManager_block_19169_memory, hp, ht, hs] at rd
  exact ⟨_, _, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
