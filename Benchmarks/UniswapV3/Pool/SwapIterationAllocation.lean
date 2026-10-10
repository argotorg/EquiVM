import Benchmarks.UniswapV3.Pool.WordArrayMemory
import Benchmarks.UniswapV3.Pool.MemoryGasBound
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_074

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationZeroWords : List UInt256 := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]

def swapIterationAllocAw (aw p : UInt256) : UInt256 :=
  M (M (M (M (M (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩)
    (p + UInt256.ofNat 64) ⟨32⟩) (p + UInt256.ofNat 96) ⟨32⟩)
    (p + UInt256.ofNat 128) ⟨32⟩) (p + UInt256.ofNat 160) ⟨32⟩)
    (p + UInt256.ofNat 192) ⟨32⟩

theorem swapIterationAllocationMemory {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200) :
    uniswapV3Pool_block_22030_memory (mem := mem) =
      wordArrayAllocMem mem p swapIterationZeroWords := by
  have hp (n : Nat) (hn : n ≤ 224) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  simp only [uniswapV3Pool_block_22030_memory, hload, wordArrayAllocMem,
    swapIterationZeroWords, List.length_cons, List.length_nil, writeWordArray,
    Reasoning.Theory.writeWord, hp 32 (by decide), hp 64 (by decide), hp 96 (by decide),
    hp 128 (by decide), hp 160 (by decide), hp 192 (by decide), Nat.add_assoc]
  rfl

theorem swapIterationAllocAw_active {aw p : UInt256}
    (ha : ActiveWords aw) (hb : p.toNat + 224 ≤ 2 ^ 200) :
    ActiveWords (swapIterationAllocAw aw p) := by
  have hp (n : Nat) (hn : n ≤ 192) : (p + UInt256.ofNat n).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)]
    omega
  exact activeWords_expand32
    (activeWords_expand32
      (activeWords_expand32
        (activeWords_expand32
          (activeWords_expand32
            (activeWords_expand32
              (activeWords_expand32 ha (show p.toNat + 32 ≤ 2 ^ 200 by omega))
              (hp 32 (by decide)))
            (hp 64 (by decide)))
          (hp 96 (by decide)))
        (hp 128 (by decide)))
      (hp 160 (by decide)))
    (hp 192 (by decide))

theorem swapIterationAllocAw_cover {aw p : UInt256}
    (ha : ActiveWords aw) (hb : p.toNat + 224 ≤ 2 ^ 200) :
    (p + UInt256.ofNat 224).toNat ≤ (swapIterationAllocAw aw p).toNat * 32 + 32 := by
  have hp (n : Nat) (hn : n ≤ 224) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hpre : ActiveWords
      (M (M (M (M (M (M aw p ⟨32⟩) (p + ⟨32⟩) ⟨32⟩) (p + ⟨64⟩) ⟨32⟩)
        (p + ⟨96⟩) ⟨32⟩) (p + ⟨128⟩) ⟨32⟩) (p + ⟨160⟩) ⟨32⟩) := by
    have hstep (a : UInt256) (h : ActiveWords a) (n : Nat) (hn : n ≤ 192) :
        ActiveWords (M a (p + UInt256.ofNat n) ⟨32⟩) :=
      activeWords_expand32 h (by rw [hp n (by omega)]; omega)
    exact hstep _ (hstep _ (hstep _ (hstep _ (hstep _
      (activeWords_expand32 ha (show p.toNat + 32 ≤ 2 ^ 200 by omega)) 32 (by decide))
      64 (by decide)) 96 (by decide)) 128 (by decide)) 160 (by decide)
  have hc := expandedWords32_cover hpre
    (show (p + UInt256.ofNat 192).toNat + 32 ≤ 2 ^ 200 by rw [hp 192 (by decide)]; omega)
  change (p + UInt256.ofNat 192).toNat < (swapIterationAllocAw aw p).toNat * 32 at hc
  rw [hp 192 (by decide)] at hc
  rw [hp 224 (by decide)]
  omega

theorem swapIterationAllocateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨22030⟩ (ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (swapIterationAllocAw aw p) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ret (p :: R)
        (wordArrayAllocMem mem p swapIterationZeroWords) (swapIterationAllocAw aw p)
        rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p swapIterationZeroWords)
        (swapIterationAllocAw aw p) (p + ⟨224⟩) ∧
      WordArrayMemory (wordArrayAllocMem mem p swapIterationZeroWords) p swapIterationZeroWords ∧
      MemoryPrefix mem (wordArrayAllocMem mem p swapIterationZeroWords) p.toNat ∧
      (p + UInt256.ofNat 224).toNat ≤ (swapIterationAllocAw aw p).toNat * 32 + 32 := by
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have rr := uniswapV3Pool_block_22030 (immWords := wordsOf (immStore v)) hov hret rd
  simp only [uniswapV3Pool_block_22030_stack, hload, h64,
    swapIterationAllocationMemory hm hb] at rr
  refine ⟨_, _, ?_, rr, ?_, ?_, wordArrayAllocMem_prefix mem p swapIterationZeroWords,
    swapIterationAllocAw_cover hm.active hb⟩
  · simp only [swapIterationAllocAw, memExpansionCost, h64, Nat.sub_self]
    omega
  · exact wordArrayAllocMem_heap mem p _ swapIterationZeroWords hm.lower (by decide) hb
      (swapIterationAllocAw_active hm.active hb)
  · exact wordArrayAllocMem_region mem p swapIterationZeroWords hm.lower (by decide)

end Benchmarks.UniswapV3.Pool
