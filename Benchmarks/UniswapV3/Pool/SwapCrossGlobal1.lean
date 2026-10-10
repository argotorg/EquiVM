import Benchmarks.UniswapV3.Pool.SwapCrossGlobal0

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCrossGlobal1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (tick global0 : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3804⟩
      ([global0, tick, ⟨3851⟩, ⟨0⟩, q] ++
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3823⟩
        ([(if a.zeroForOne then feeGrowthWord true σ ee else s.feeGrowth),
          global0, tick, ⟨3851⟩, ⟨0⟩, q] ++
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  cases hz : a.zeroForOne
  · have r1 := uniswapV3Pool_block_3804_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 18 ≤ 1024; omega) (by rw [hz]; rfl) rd
    have hfee : memLoad (UInt256.ofNat 128 + p) mem = s.feeGrowth := by
      rw [u256_add_comm]
      exact SwapStateMemory.load_feeGrowth hs (by change _ < 2 ^ 256; omega)
    have r2 := uniswapV3Pool_block_3810 (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 8 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
    simp only [uniswapV3Pool_block_3810_stack, hfee] at r2
    have hp : (UInt256.ofNat 128 + p).toNat + 32 ≤ 2 ^ 200 := by
      rw [u256_add_comm, uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)]; omega
    have hm1 := hm.expand32 (UInt256.ofNat 128 + p) hp
    have hmono := expandedWords_mono (off := UInt256.ofNat 128 + p) (size := ⟨32⟩) hm.active hp
    simp only [Bool.false_eq_true, if_false]
    refine ⟨_, _, _, ?_, r2, hm1, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega
  · have r1 := uniswapV3Pool_block_3804_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 18 ≤ 1024; omega) (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    obtain ⟨k2, C2, hC2, r2⟩ := rdRoutine_return_mono r1 (fun _ _ rr ↦
      uniswapV3Pool_block_3819 (immWords := wordsOf (immStore v))
        (by change R.length + 18 + 1 ≤ 1024; omega) rr)
    change RD (deployedRuntime v) ee g s0 ⟨3823⟩
      ([feeGrowthWord true σ ee, global0, tick, ⟨3851⟩, ⟨0⟩, q] ++
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k2 C2 at r2
    simp only [if_true]
    exact ⟨aw, k2, C2, by omega, r2, hm, le_refl _⟩

end Benchmarks.UniswapV3.Pool
