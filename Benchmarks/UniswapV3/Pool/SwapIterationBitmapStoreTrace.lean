import Benchmarks.UniswapV3.Pool.SwapIterationMemory
import Benchmarks.UniswapV3.Pool.SwapIterationStartTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationBitmapStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free tickRaw hitRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (d : SwapIterationData) (tick : Int) (hit : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3109⟩ (hitRaw :: tickRaw :: p :: R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem p d)
    (ht : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hh : UInt256.isZero (UInt256.isZero hitRaw) = hit.toUInt256)
    (htb : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hp : 96 ≤ p.toNat) (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 5 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if tick < -887272 then ⟨3144⟩ else ⟨3158⟩)
        (p :: R) (swapIterationBitmapMem mem p tick hit) aw' rdata σ k' C' ∧
      HeapMemory (swapIterationBitmapMem mem p tick hit) aw' free ∧
      SwapIterationMemory (swapIterationBitmapMem mem p tick hit) p
        {d with tickNext := tick, initialized := hit} ∧
      MemoryPrefix mem (swapIterationBitmapMem mem p tick hit) p.toNat ∧
      aw.toNat ≤ aw'.toNat := by
  have hc : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick) = EVM.wordOfInt tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ tick (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ htb.1 htb.2]
  have hcmp : UInt256.slt
      (UInt256.signextend (UInt256.ofNat 2)
        (UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) tickRaw)))
      (UInt256.lnot (UInt256.ofNat 887271)) = if tick < -887272 then ⟨1⟩ else ⟨0⟩ := by
    rw [ht, hc, hc,
      show UInt256.lnot (UInt256.ofNat 887271) = EVM.wordOfInt (-887272) by decide +kernel]
    exact slt_wordOfInt _ _ (by omega) (by omega) (by decide) (by decide)
  have rout : RD (deployedRuntime v) ee g s0
      (if tick < -887272 then ⟨3144⟩ else ⟨3158⟩) (p :: R)
      (swapIterationBitmapMem mem p tick hit)
      (M (M aw (p + UInt256.ofNat 64) ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩)
      rdata σ (k + 27)
      (C + (92 + memExpansionCost aw (p + UInt256.ofNat 64) ⟨32⟩ +
        memExpansionCost (M aw (p + UInt256.ofNat 64) ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩)) := by
    by_cases hlo : tick < -887272
    · have rr := uniswapV3Pool_block_3109_fallthrough (immWords := wordsOf (immStore v))
        hov (by rw [hcmp, if_pos hlo]; rfl) rd
      simpa only [hlo, if_true, uniswapV3Pool_block_3109_fallthrough_stack,
        uniswapV3Pool_block_3109_fallthrough_memory, swapIterationBitmapMem,
        Reasoning.Theory.writeWord, ht, hc, hh] using rr
    · have rr := uniswapV3Pool_block_3109_taken (immWords := wordsOf (immStore v))
        hov (by rw [hcmp, if_neg hlo]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [hlo, if_false, uniswapV3Pool_block_3109_taken_stack,
        uniswapV3Pool_block_3109_taken_memory, swapIterationBitmapMem,
        Reasoning.Theory.writeWord, ht, hc, hh] using rr
  obtain ⟨hm', hd', hpre⟩ := swapIterationBitmapMemory d tick hit hm hd hp
    (by change _ < 2 ^ 256; omega)
  have hp32 : (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)]; omega
  have hp64 : (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)]; omega
  have hm1 := hm'.expand32 (p + UInt256.ofNat 64) hp64
  have hm2 := hm1.expand32 (p + UInt256.ofNat 32) hp32
  refine ⟨_, _, _, ?_, rout, hm2, hd', hpre, ?_⟩
  · dsimp only [memExpansionCost]
    omega
  · exact (expandedWords_mono hm.active hp64).trans (expandedWords_mono hm1.active hp32)

end Benchmarks.UniswapV3.Pool
