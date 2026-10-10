import Benchmarks.UniswapV3.Pool.SwapWriteSource
import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapWriteLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cache snap exactWord free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (initial : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4021⟩
      ([p, exactWord, cache, snap] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (hbc : cache.toNat + 192 ≤ 2 ^ 200) (hbs : snap.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨14801⟩
        (oracleWriteEntryWords (swapWriteArgs c initial) ++
          [⟨4077⟩, ⟨0⟩, ⟨0⟩, p, exactWord, cache, snap] ++ R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hcb : cache.toNat + 32 * c.words.length < UInt256.size := by
    change cache.toNat + 192 < 2 ^ 256; omega
  have hsb : snap.toNat + 32 * (slot0StructWords initial.accountMap
      initial.executionEnv).length < UInt256.size := by
    change snap.toNat + 224 < 2 ^ 256; omega
  have htime : memLoad (UInt256.ofNat 64 + cache) mem = c.blockTimestamp := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hc 2 (by change 2 < 6; decide) hcb
  have hliq : memLoad (UInt256.ofNat 32 + cache) mem = c.liquidityStart := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hc 1 (by change 1 < 6; decide) hcb
  have htick : memLoad (UInt256.ofNat 32 + snap) mem =
      EVM.wordOfInt (slot0TickValue initial.accountMap initial.executionEnv) := by
    rw [u256_add_comm]
    exact Slot0Memory.load_tick hs hsb
  have hindex : memLoad (UInt256.ofNat 64 + snap) mem =
      slot0FieldWord 23 2 initial.accountMap initial.executionEnv := by
    rw [u256_add_comm]
    exact Slot0Memory.load_index hs hsb
  have hcard : memLoad (UInt256.ofNat 96 + snap) mem =
      slot0FieldWord 25 2 initial.accountMap initial.executionEnv := by
    rw [u256_add_comm]
    exact Slot0Memory.load_cardinality hs hsb
  have hnext : memLoad (UInt256.ofNat 128 + snap) mem =
      slot0FieldWord 27 2 initial.accountMap initial.executionEnv := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hs 4 (by change 4 < 7; decide) hsb
  have hbsc (i : Nat) (hi : i ≤ 128) :
      (UInt256.ofNat i + snap).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat snap i (by change _ < 2 ^ 256; omega)]
    omega
  have hbcc (i : Nat) (hi : i ≤ 64) :
      (UInt256.ofNat i + cache).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat cache i (by change _ < 2 ^ 256; omega)]
    omega
  have hm1 := hm.expand32 (UInt256.ofNat 64 + snap) (hbsc 64 (by decide))
  have hm2 := hm1.expand32 (UInt256.ofNat 64 + cache) (hbcc 64 (by decide))
  have hm3 := hm2.expand32 (UInt256.ofNat 32 + snap) (hbsc 32 (by decide))
  have hm4 := hm3.expand32 (UInt256.ofNat 32 + cache) (hbcc 32 (by decide))
  have hm5 := hm4.expand32 (UInt256.ofNat 96 + snap) (hbsc 96 (by decide))
  have hm6 := hm5.expand32 (UInt256.ofNat 128 + snap) (hbsc 128 (by decide))
  have hm12 := expandedWords_mono (off := UInt256.ofNat 64 + snap) (size := ⟨32⟩)
    hm.active (hbsc 64 (by decide))
  have hm23 := expandedWords_mono (off := UInt256.ofNat 64 + cache) (size := ⟨32⟩)
    hm1.active (hbcc 64 (by decide))
  have hm34 := expandedWords_mono (off := UInt256.ofNat 32 + snap) (size := ⟨32⟩)
    hm2.active (hbsc 32 (by decide))
  have hm45 := expandedWords_mono (off := UInt256.ofNat 32 + cache) (size := ⟨32⟩)
    hm3.active (hbcc 32 (by decide))
  have hm56 := expandedWords_mono (off := UInt256.ofNat 96 + snap) (size := ⟨32⟩)
    hm4.active (hbsc 96 (by decide))
  have hm67 := expandedWords_mono (off := UInt256.ofNat 128 + snap) (size := ⟨32⟩)
    hm5.active (hbsc 128 (by decide))
  have rr := uniswapV3Pool_block_4021 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
  simp only [uniswapV3Pool_block_4021_stack, htime, hliq, htick, hindex, hcard, hnext] at rr
  have hpc : UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 14801) =
      (⟨14801⟩ : UInt256) := by native_decide
  rw [hpc] at rr
  dsimp only [oracleWriteEntryWords, swapWriteArgs]
  refine ⟨_, _, _, ?_, rr, hm6,
    hm12.trans (hm23.trans (hm34.trans (hm45.trans (hm56.trans hm67))))⟩
  dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
