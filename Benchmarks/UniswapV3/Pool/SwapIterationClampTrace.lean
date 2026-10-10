import Benchmarks.UniswapV3.Pool.SwapIterationTickMemory
import Benchmarks.UniswapV3.Pool.SwapIterationTickSource
import Benchmarks.UniswapV3.Pool.SwapIterationBitmapStoreTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationClampMem (mem : ByteArray) (p : UInt256) (tick : Int) : ByteArray :=
  if tick < -887272 then writeWord mem (p + UInt256.ofNat 32).toNat (EVM.wordOfInt (-887272))
  else if 887272 < tick then writeWord mem (p + UInt256.ofNat 32).toNat (EVM.wordOfInt 887272)
  else mem

theorem swapIterationClampX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 (if d.tickNext < -887272 then ⟨3144⟩ else ⟨3158⟩)
      (p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem p d)
    (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23)
    (hp : 96 ≤ p.toNat) (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 4 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3189⟩ (p :: R)
        (swapIterationClampMem mem p d.tickNext) aw' rdata σ k' C' ∧
      HeapMemory (swapIterationClampMem mem p d.tickNext) aw' free ∧
      SwapIterationMemory (swapIterationClampMem mem p d.tickNext) p
        {d with tickNext := swapIterationClampTick d.tickNext} ∧
      MemoryPrefix mem (swapIterationClampMem mem p d.tickNext) p.toNat ∧
      aw.toNat ≤ aw'.toNat := by
  have hpb : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hp32 : (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 32 (by omega)]; omega
  by_cases hlo : d.tickNext < -887272
  · simp only [hlo, if_true, swapIterationClampMem, swapIterationClampTick] at rd ⊢
    have rr := uniswapV3Pool_block_3144 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have hw : UInt256.lnot (UInt256.ofNat 887271) = EVM.wordOfInt (-887272) := by decide +kernel
    simp only [uniswapV3Pool_block_3144_memory, hw] at rr
    obtain ⟨hm', hd', hpre⟩ := swapIterationTickWriteMemory d (-887272) hm hd hp hpb
    have hm1 := hm'.expand32 (p + UInt256.ofNat 32) hp32
    refine ⟨_, _, _, ?_, rr, hm1, hd', hpre, expandedWords_mono hm.active hp32⟩
    dsimp only [memExpansionCost, M, expandedWords]
    omega
  · simp only [hlo, if_false, swapIterationClampMem, swapIterationClampTick] at rd ⊢
    have hload := SwapIterationMemory.load_tick hd hpb
    have hc : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt d.tickNext) =
        EVM.wordOfInt d.tickNext := by
      rw [signextend_wordOfInt ⟨24, by decide⟩ _ d.tickNext (by decide) (by decide),
        normalizeSint_eq_self ⟨24, by decide⟩ _ ht.1 ht.2]
    have hcmp : UInt256.sgt
        (UInt256.signextend (UInt256.ofNat 2) (memLoad (p + UInt256.ofNat 32) mem))
        (UInt256.ofNat 887272) = if 887272 < d.tickNext then ⟨1⟩ else ⟨0⟩ := by
      rw [hload, hc, sgt_eq_slt_swap,
        show UInt256.ofNat 887272 = EVM.wordOfInt 887272 by decide +kernel]
      exact slt_wordOfInt _ _ (by decide) (by decide) (by omega) (by omega)
    by_cases hhi : 887272 < d.tickNext
    · simp only [if_pos hhi]
      have r1 := uniswapV3Pool_block_3158_fallthrough (immWords := wordsOf (immStore v))
        hov (by rw [hcmp, if_pos hhi]; rfl) rd
      have r2 := uniswapV3Pool_block_3180 (immWords := wordsOf (immStore v)) hov r1
      have hw : UInt256.ofNat 887272 = EVM.wordOfInt 887272 := by decide +kernel
      simp only [uniswapV3Pool_block_3180_memory, hw] at r2
      obtain ⟨hm', hd', hpre⟩ := swapIterationTickWriteMemory d 887272 hm hd hp hpb
      have hm1 := hm'.expand32 (p + UInt256.ofNat 32) hp32
      have hm2 := hm1.expand32 (p + UInt256.ofNat 32) hp32
      refine ⟨_, _, _, ?_, r2, hm2, hd', hpre, ?_⟩
      · dsimp only [memExpansionCost, M, expandedWords]
        omega
      · exact (expandedWords_mono hm.active hp32).trans (expandedWords_mono hm1.active hp32)
    · simp only [if_neg hhi]
      have rr := uniswapV3Pool_block_3158_taken (immWords := wordsOf (immStore v))
        hov (by rw [hcmp, if_neg hhi]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      refine ⟨_, _, _, ?_, rr, hm.expand32 (p + UInt256.ofNat 32) hp32,
        hd, .refl _ _, expandedWords_mono hm.active hp32⟩
      dsimp only [memExpansionCost, M, expandedWords]
      omega

end Benchmarks.UniswapV3.Pool
