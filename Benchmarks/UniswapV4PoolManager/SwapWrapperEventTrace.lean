import Benchmarks.UniswapV4PoolManager.SwapWrapperEventMemory
import Benchmarks.UniswapV4PoolManager.SwapWrapperEventStatic
import Benchmarks.UniswapV4PoolManager.MemoryAccessCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapWrapperEventTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {mem rdata : ByteArray} {free aw state delta fee id params x0 x1 x8 x9 x10 x11 x12 x13 hookPtr : UInt256}
    {r : PoolSwapResultWords} {R : List UInt256} {k C : Nat} (v : PoolManagerImmutables)
    (hstack : R.length+20 ≤ 1024) (hperm : I.perm = true)
    (hr : WordStructView mem state (poolSwapResultWordList r)) (hp : r.price.toNat < 2^160)
    (hl : r.liquidity.toNat < 2^128) (ht : int24Canonical r.tick) (he : fee.toNat < 2^24)
    (hf : free.toNat+192 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨1766⟩
      ([x0, x1, fee, UInt256.ofNat 16777215, id, state, params, delta, x8, x9, x10,
        x11, x12, x13, hookPtr, UInt256.ofNat 32]++R) mem aw rdata σ k C) :
    ∃ aw' k' C', C ≤ C' ∧ C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨1930⟩
      ([memLoad hookPtr (swapWrapperEventMemory mem free delta fee r),
        UInt256.ofNat 1461501637330902918203684832716283019655932542975,
        x12, params, delta, x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32]++R)
      (swapWrapperEventMemory mem free delta fee r) aw' rdata σ k' C' := by
  have hm := swapWrapperEventMemory_compiled (delta := delta) hr hp hl ht he hf hfree
  have rd := poolManagerBlocks.poolManager_block_1766 hstack hperm h
  have hs : poolManagerBlocks.poolManager_block_1766_stack (mem := mem) (x2 := fee)
      (x3 := UInt256.ofNat 16777215) (x5 := state) (x6 := params) (x7 := delta)
      (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13)
      (x14 := hookPtr) (x15 := UInt256.ofNat 32) (R := R) =
      [memLoad hookPtr (swapWrapperEventMemory mem free delta fee r),
        UInt256.ofNat 1461501637330902918203684832716283019655932542975,
        x12, params, delta, x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32]++R := by
    change memLoad hookPtr (poolManagerBlocks.poolManager_block_1766_memory (mem := mem) (x2 := fee)
      (x3 := UInt256.ofNat 16777215) (x5 := state) (x7 := delta) (x15 := UInt256.ofNat 32)) :: _ = _
    rw [hm]
    rfl
  rw [hs, hm] at rd
  have hc := memoryAccessCost_covers aw
    [(state, ⟨32⟩), (state+UInt256.ofNat 64, ⟨32⟩), (state+UInt256.ofNat 32, ⟨32⟩),
      (UInt256.ofNat 64, ⟨32⟩), (memLoad (UInt256.ofNat 64) mem, ⟨32⟩),
      (memLoad (UInt256.ofNat 64) mem+UInt256.ofNat 32, ⟨32⟩),
      (memLoad (UInt256.ofNat 64) mem+UInt256.ofNat 64, ⟨32⟩),
      (memLoad (UInt256.ofNat 64) mem+UInt256.ofNat 96, ⟨32⟩),
      (memLoad (UInt256.ofNat 64) mem+UInt256.ofNat 128, ⟨32⟩),
      (memLoad (UInt256.ofNat 64) mem+UInt256.ofNat 160, ⟨32⟩),
      (memLoad (UInt256.ofNat 64) mem, UInt256.ofNat 192), (hookPtr, ⟨32⟩)]
  dsimp only [memoryAccessWords, memoryAccessCost] at hc
  exact ⟨_, _, _, by omega, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
