import Benchmarks.UniswapV3.Pool.WordArrayMemory
import Benchmarks.UniswapV3.Pool.OracleTransformSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_074

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def OracleObservation.words (last : OracleObservation) : List UInt256 :=
  [last.timestamp, EVM.wordOfInt last.tickCumulative, last.secondsPerLiquidity,
    if last.initialized then ⟨1⟩ else ⟨0⟩]

abbrev ObservationMemory (mem : ByteArray) (p : UInt256) (last : OracleObservation) : Prop :=
  WordArrayMemory mem p last.words

theorem observationZeroCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨22090⟩ (ret :: R) mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret (p :: R)
      (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) aw' (p + ⟨128⟩) ∧
      (p + ⟨128⟩).toNat ≤ aw'.toNat * 32 + 32 := by
  have rdAlloc := uniswapV3Pool_block_22090 (immWords := wordsOf (immStore v)) hov hret rd
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hp96 : (p + UInt256.ofNat 96).toNat = p.toNat + 96 :=
    uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have hfold : (UInt256.ofNat 0).toByteArray.write 0
      ((UInt256.ofNat 0).toByteArray.write 0
        ((UInt256.ofNat 0).toByteArray.write 0
          ((UInt256.ofNat 0).toByteArray.write 0
            ((p + UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)
            p.toNat 32) (p.toNat + 32) 32) (p.toNat + 64) 32) (p.toNat + 96) 32 =
      wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] := rfl
  simp only [uniswapV3Pool_block_22090_stack, uniswapV3Pool_block_22090_memory,
    hload, h64, hp32, hp64, hp96, hfold] at rdAlloc
  have ha3 := activeWords_expand32
      (activeWords_expand32
        (activeWords_expand32 hm.active (show p.toNat + 32 ≤ 2 ^ 200 by omega))
        (show (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 by rw [hp32]; omega))
      (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)
  have hlast : (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 := by rw [hp96]; omega
  have ha := activeWords_expand32 ha3 hlast
  refine ⟨_, _, _, ?_, rdAlloc,
    wordArrayAllocMem_heap mem p _ _ hm.lower (by simp) hb ha, ?_⟩
  · simp only [memExpansionCost]
    omega
  · have hc := expandedWords32_cover ha3 hlast
    have hp128 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
      uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
    rw [hp96] at hc
    dsimp only [M]
    dsimp only [expandedWords] at hc
    rw [hp128]
    omega

theorem observationZeroMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨22090⟩ (ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret (p :: R)
      (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) aw' (p + ⟨128⟩) ∧
      (p + ⟨128⟩).toNat ≤ aw'.toNat * 32 + 32 := by
  exact observationZeroCursorX (v := v) rd hm.cursor hb hret hov

theorem observationZeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨22090⟩ (ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (p :: R)
      (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) aw' (p + ⟨128⟩)  := by
  obtain ⟨aw', k', C', _, hout, hheap, _⟩ := observationZeroMonoX (v := v) rd hm hb hret hov
  exact ⟨aw', k', C', hout, hheap⟩

end Benchmarks.UniswapV3.Pool
