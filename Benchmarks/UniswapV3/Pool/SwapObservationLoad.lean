import Benchmarks.UniswapV3.Pool.SwapCrossFlags
import Benchmarks.UniswapV3.Pool.Slot0Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapObservationLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q p exactWord cache snap free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (initial : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3691⟩ ([q, p, exactWord, cache, snap] ++ R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (hbc : cache.toNat + 192 ≤ 2 ^ 200) (hbs : snap.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 15 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨13193⟩
        ([slot0FieldWord 25 2 initial.accountMap initial.executionEnv, c.liquidityStart,
          slot0FieldWord 23 2 initial.accountMap initial.executionEnv,
          EVM.wordOfInt (slot0TickValue initial.accountMap initial.executionEnv),
          ⟨0⟩, c.blockTimestamp, ⟨8⟩, ⟨3741⟩, q, p, exactWord, cache, snap] ++ R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hsb : snap.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hcb : cache.toNat + 32 * c.words.length < UInt256.size := by
    change cache.toNat + 192 < 2 ^ 256; omega
  have ht : memLoad (UInt256.ofNat 32 + snap) mem =
      EVM.wordOfInt (slot0TickValue initial.accountMap initial.executionEnv) := by
    rw [u256_add_comm]; exact Slot0Memory.load_tick hs hsb
  have hi : memLoad (UInt256.ofNat 64 + snap) mem =
      slot0FieldWord 23 2 initial.accountMap initial.executionEnv := by
    rw [u256_add_comm]; exact Slot0Memory.load_index hs hsb
  have hcard : memLoad (UInt256.ofNat 96 + snap) mem =
      slot0FieldWord 25 2 initial.accountMap initial.executionEnv := by
    rw [u256_add_comm]; exact Slot0Memory.load_cardinality hs hsb
  have hliq : memLoad (UInt256.ofNat 32 + cache) mem = c.liquidityStart := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hc 1 (by change 1 < 6; decide) hcb
  have htime : memLoad (UInt256.ofNat 64 + cache) mem = c.blockTimestamp := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hc 2 (by change 2 < 6; decide) hcb
  have hb1 : (UInt256.ofNat 64 + cache).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat cache 64 (by change _ < 2 ^ 256; omega)]; omega
  have hb2 : (UInt256.ofNat 32 + snap).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat snap 32 (by change _ < 2 ^ 256; omega)]; omega
  have hb3 : (UInt256.ofNat 64 + snap).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat snap 64 (by change _ < 2 ^ 256; omega)]; omega
  have hb4 : (UInt256.ofNat 32 + cache).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat cache 32 (by change _ < 2 ^ 256; omega)]; omega
  have hb5 : (UInt256.ofNat 96 + snap).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat snap 96 (by change _ < 2 ^ 256; omega)]; omega
  have hm1 := hm.expand32 (UInt256.ofNat 64 + cache) hb1
  have hm2 := hm1.expand32 (UInt256.ofNat 32 + snap) hb2
  have hm3 := hm2.expand32 (UInt256.ofNat 64 + snap) hb3
  have hm4 := hm3.expand32 (UInt256.ofNat 32 + cache) hb4
  have hm5 := hm4.expand32 (UInt256.ofNat 96 + snap) hb5
  have hmono1 := expandedWords_mono (off := UInt256.ofNat 64 + cache) (size := ⟨32⟩) hm.active hb1
  have hmono2 := expandedWords_mono (off := UInt256.ofNat 32 + snap) (size := ⟨32⟩) hm1.active hb2
  have hmono3 := expandedWords_mono (off := UInt256.ofNat 64 + snap) (size := ⟨32⟩) hm2.active hb3
  have hmono4 := expandedWords_mono (off := UInt256.ofNat 32 + cache) (size := ⟨32⟩) hm3.active hb4
  have hmono5 := expandedWords_mono (off := UInt256.ofNat 96 + snap) (size := ⟨32⟩) hm4.active hb5
  have rr := uniswapV3Pool_block_3691 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
  have hpc : UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 13193) = ⟨13193⟩ := by
    decide +kernel
  simp only [hpc, uniswapV3Pool_block_3691_stack, ht, hi, hcard, hliq, htime] at rr
  refine ⟨_, _, _, ?_, rr, hm5,
    hmono1.trans (hmono2.trans (hmono3.trans (hmono4.trans hmono5)))⟩
  dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
