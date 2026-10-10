import Benchmarks.UniswapV3.Pool.SwapIterationSource
import Benchmarks.UniswapV3.Pool.SwapLoopGuardTrace
import Benchmarks.UniswapV3.Pool.WordArrayUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem SwapStateMemory.load_tick {mem : ByteArray} {p : UInt256} {s : SwapStateData}
    (hm : SwapStateMemory mem p s) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 96) mem = EVM.wordOfInt s.tick := by
  have h := WordArrayMemory.load hm 3 (by change 3 < 7; decide) hb
  simpa only [SwapStateData.words, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceMul] using h

theorem swapIterationStartBoundX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3042⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hq : SwapIterationMemory mem q (swapIterationInitial ⟨0⟩)) (hfit : s.Fits)
    (hql : 96 ≤ q.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨11307⟩
        ([a.zeroForOne.toUInt256, wordsOf (immStore v) "tickSpacing", EVM.wordOfInt s.tick,
          ⟨6⟩, ⟨3109⟩, q] ++ swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        (writeWord mem q.toNat s.price) aw' rdata σ k' C' ∧
      HeapMemory (writeWord mem q.toNat s.price) aw' free ∧
      SwapStateMemory (writeWord mem q.toNat s.price) p s ∧
      SwapIterationMemory (writeWord mem q.toNat s.price) q (swapIterationInitial s.price) ∧
      MemoryPrefix mem (writeWord mem q.toNat s.price) q.toNat ∧ aw.toNat ≤ aw'.toNat := by
  have hpb : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hp := SwapStateMemory.load_price hs hpb
  have hclean : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) s.price = s.price := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hfit.2.2.1
  have hs' : SwapStateMemory (writeWord mem q.toNat s.price) p s :=
    WordArrayMemory.write_disjoint hs q.toNat s.price (Or.inr hdisj)
  have ht := SwapStateMemory.load_tick hs' hpb
  have hmem : uniswapV3Pool_block_3042_memory (mem := mem) (x0 := q) (x1 := p) =
      writeWord mem q.toNat s.price := by
    simp only [uniswapV3Pool_block_3042_memory, amountDeltaMask160, hp, hclean,
      Reasoning.Theory.writeWord]
  have rr := uniswapV3Pool_block_3042 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 18 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_3042_stack, amountDeltaMask160, hp, hclean, hmem] at rr
  change memLoad (p + UInt256.ofNat 96) (s.price.toByteArray.write 0 mem q.toNat 32) =
    EVM.wordOfInt s.tick at ht
  rw [ht] at rr
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by omega)
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by omega)
  have hm' := HeapMemory.writeWithin hm q.toNat s.price hql
    (by have hh := hq.1; change q.toNat + 224 ≤ mem.size at hh; omega)
  have hma := ((hm'.expand32 (p + UInt256.ofNat 64) (by rw [hp64]; omega)).expand32 q
    (by omega)).expand32 (p + UInt256.ofNat 96) (by rw [hp96]; omega)
  refine ⟨_, _, _, ?_, rr, hma, hs', ?_,
    memoryPrefix_sparse_writeWord mem q.toNat q.toNat s.price (Or.inl (le_refl _)), ?_⟩
  · dsimp only [memExpansionCost, M, expandedWords]
    omega
  · have hw := WordArrayMemory.write hq 0 s.price
    simpa only [SwapIterationMemory, SwapIterationData.words, swapIterationInitial,
      Nat.mul_zero, Nat.add_zero, List.set_cons_zero] using hw
  · have h1 := expandedWords_mono (size := (⟨32⟩ : UInt256)) hm.active
      (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)
    have ha1 := activeWords_expand32 hm.active
      (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)
    have h2 := expandedWords_mono (size := (⟨32⟩ : UInt256)) ha1
      (show q.toNat + 32 ≤ 2 ^ 200 by omega)
    have ha2 := activeWords_expand32 ha1 (show q.toNat + 32 ≤ 2 ^ 200 by omega)
    have h3 := expandedWords_mono (size := (⟨32⟩ : UInt256)) ha2
      (show (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 by rw [hp96]; omega)
    exact h1.trans (h2.trans h3)

theorem swapIterationStartX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3042⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hq : SwapIterationMemory mem q (swapIterationInitial ⟨0⟩)) (hfit : s.Fits)
    (hql : 96 ≤ q.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨11307⟩
        ([a.zeroForOne.toUInt256, wordsOf (immStore v) "tickSpacing", EVM.wordOfInt s.tick,
          ⟨6⟩, ⟨3109⟩, q] ++ swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        (writeWord mem q.toNat s.price) aw' rdata σ k' C' ∧
      HeapMemory (writeWord mem q.toNat s.price) aw' free ∧
      SwapStateMemory (writeWord mem q.toNat s.price) p s ∧
      SwapIterationMemory (writeWord mem q.toNat s.price) q (swapIterationInitial s.price) ∧
      MemoryPrefix mem (writeWord mem q.toNat s.price) q.toNat := by
  obtain ⟨aw', k', C', hcost, rr, hm', hs', hq', hpre, _⟩ :=
    swapIterationStartBoundX a s rd hm hs hq hfit hql hdisj hb hov
  exact ⟨aw', k', C', hcost, rr, hm', hs', hq', hpre⟩

end Benchmarks.UniswapV3.Pool
