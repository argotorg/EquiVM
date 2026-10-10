import Benchmarks.UniswapV3.Pool.SwapProtocolTrace
import Benchmarks.UniswapV3.Pool.SwapPriceChangedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool

def swapInitializedBody : List Stmt :=
  match swapCrossBody[0]! with
  | .ite _ yes _ => yes
  | _ => []

def swapObservationBody : List Stmt :=
  match swapInitializedBody[0]! with
  | .ite _ yes _ => yes
  | _ => []

theorem swapInitializedGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3672⟩ (q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem q d)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 3 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if d.initialized then ⟨3682⟩ else ⟨3893⟩)
        (q :: R) mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧
      aw.toNat ≤ aw'.toNat := by
  have hload : memLoad (UInt256.ofNat 64 + q) mem = d.initialized.toUInt256 := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hd 2 (by change 2 < 7; decide)
      (by change q.toNat + 224 < 2 ^ 256; omega)
  have hbq : (UInt256.ofNat 64 + q).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat q 64 (by change _ < 2 ^ 256; omega)]
    omega
  have hm1 := hm.expand32 (UInt256.ofNat 64 + q) hbq
  have hmono := expandedWords_mono (off := UInt256.ofNat 64 + q) (size := ⟨32⟩) hm.active hbq
  cases hi : d.initialized
  · have rr := uniswapV3Pool_block_3672_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hload, hi]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [Bool.false_eq_true, if_false]
    refine ⟨_, _, _, ?_, rr, hm1, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega
  · have rr := uniswapV3Pool_block_3672_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hload, hi]; rfl) rd
    simp only [if_true]
    refine ⟨_, _, _, ?_, rr, hm1, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega

theorem swapObservationGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q p exactWord cache free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3682⟩ ([q, p, exactWord, cache] ++ R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hb : cache.toNat + 192 ≤ 2 ^ 200) (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if c.computedLatestObservation then ⟨3775⟩ else ⟨3691⟩)
        ([q, p, exactWord, cache] ++ R) mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧
      aw.toNat ≤ aw'.toNat := by
  have hload : memLoad (UInt256.ofNat 160 + cache) mem = c.computedLatestObservation.toUInt256 := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hc 5 (by change 5 < 6; decide)
      (by change cache.toNat + 192 < 2 ^ 256; omega)
  have hbc : (UInt256.ofNat 160 + cache).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat cache 160 (by change _ < 2 ^ 256; omega)]
    omega
  have hm1 := hm.expand32 (UInt256.ofNat 160 + cache) hbc
  have hmono := expandedWords_mono (off := UInt256.ofNat 160 + cache) (size := ⟨32⟩) hm.active hbc
  cases ho : c.computedLatestObservation
  · have rr := uniswapV3Pool_block_3682_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hload, ho]; rfl) rd
    simp only [Bool.false_eq_true, if_false]
    refine ⟨_, _, _, ?_, rr, hm1, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega
  · have rr := uniswapV3Pool_block_3682_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hload, ho]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [if_true]
    refine ⟨_, _, _, ?_, rr, hm1, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
