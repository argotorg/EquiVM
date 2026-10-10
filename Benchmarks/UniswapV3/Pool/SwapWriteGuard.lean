import Benchmarks.UniswapV3.Pool.SwapWriteSource
import Benchmarks.UniswapV3.Pool.SwapIterationStartTrace
import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.SafeCast128Trace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapWriteGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cache snap exactWord free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData) (initial : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3999⟩
      ([p, exactWord, cache, snap] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (hfit : s.Fits) (hbp : p.toNat + 224 ≤ 2 ^ 200)
    (hbs : snap.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0
        (if s.tick = slot0TickValue initial.accountMap initial.executionEnv then ⟨4218⟩ else ⟨4021⟩)
        ([p, exactWord, cache, snap] ++ R) mem aw' rdata σ k' C' ∧
      HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have ht : memLoad (UInt256.ofNat 96 + p) mem = EVM.wordOfInt s.tick := by
    rw [u256_add_comm]
    exact SwapStateMemory.load_tick hs (by change _ < 2 ^ 256; omega)
  have hsload : memLoad (UInt256.ofNat 32 + snap) mem =
      EVM.wordOfInt (slot0TickValue initial.accountMap initial.executionEnv) := by
    rw [u256_add_comm]
    exact Slot0Memory.load_tick hsnap (by change _ < 2 ^ 256; omega)
  have hclean : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt s.tick) =
      EVM.wordOfInt s.tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ s.tick (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hfit.2.2.2.1.1 hfit.2.2.2.1.2]
  have hstart := slot0TickWord_idem initial.accountMap initial.executionEnv
  have hb1 : (UInt256.ofNat 32 + snap).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat snap 32 (by change _ < 2 ^ 256; omega)]
    omega
  have hb2 : (UInt256.ofNat 96 + p).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)]
    omega
  have hm1 := hm.expand32 (UInt256.ofNat 32 + snap) hb1
  have hm2 := hm1.expand32 (UInt256.ofNat 96 + p) hb2
  have hmono1 := expandedWords_mono (off := UInt256.ofNat 32 + snap) (size := ⟨32⟩)
    hm.active hb1
  have hmono2 := expandedWords_mono (off := UInt256.ofNat 96 + p) (size := ⟨32⟩)
    hm1.active hb2
  by_cases he : s.tick = slot0TickValue initial.accountMap initial.executionEnv
  · have rr := uniswapV3Pool_block_3999_taken (immWords := wordsOf (immStore v)) hov
      (by rw [ht, hsload, hclean, hstart, he, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [he, if_true]
    refine ⟨_, _, _, ?_, rr, hm2, hmono1.trans hmono2⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega
  · have hw : EVM.wordOfInt s.tick ≠
        EVM.wordOfInt (slot0TickValue initial.accountMap initial.executionEnv) := by
      have hst := slot0TickValue_bounds initial.accountMap initial.executionEnv
      intro hh
      exact he ((wordOfInt_eq_iff_signed _ _ (by have := hfit.2.2.2.1; omega)
        (by have := hfit.2.2.2.1; omega) (by omega) (by omega)).mp hh)
    have hcmp := uInt256_eq_zero_of_ne (fun h ↦ hw (uInt256_eq_one_eq h))
    have rr := uniswapV3Pool_block_3999_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [ht, hsload, hclean, hstart]; exact hcmp) rd
    simp only [he, if_false]
    refine ⟨_, _, _, ?_, rr, hm2, hmono1.trans hmono2⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
