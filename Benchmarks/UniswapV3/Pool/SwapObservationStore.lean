import Benchmarks.UniswapV3.Pool.SwapObservationMemory
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapObservationStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q p exactWord cache free tickRaw secondsRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData) (tick : Int) (seconds : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3741⟩
      ([secondsRaw, tickRaw, q, p, exactWord, cache] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (htick : UInt256.signextend (UInt256.ofNat 6) tickRaw = EVM.wordOfInt tick)
    (hseconds : UInt256.land secondsRaw (UInt256.ofNat (2 ^ 160 - 1)) = seconds)
    (ht : -(2 ^ 55 : Int) ≤ tick ∧ tick < 2 ^ 55)
    (hcl : 96 ≤ cache.toNat) (hcachep : cache.toNat + 192 ≤ p.toNat)
    (hpq : p.toNat + 224 ≤ q.toNat) (hb : cache.toNat + 192 ≤ 2 ^ 200)
    (hov : R.length + 9 ≤ 1024) :
    let m := swapObservationStoreMem mem cache tick seconds
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3775⟩ ([q, p, exactWord, cache] ++ R)
        m aw' rdata σ k' C' ∧ HeapMemory m aw' free ∧
      SwapCacheMemory m cache (swapObservationCache c tick seconds) ∧ SwapStateMemory m p s ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m cache.toNat ∧ aw.toNat ≤ aw'.toNat := by
  dsimp only
  have hclean : UInt256.signextend (UInt256.ofNat 6) (EVM.wordOfInt tick) =
      EVM.wordOfInt tick := by
    rw [signextend_wordOfInt ⟨56, by decide⟩ _ tick (by decide) (by decide),
      normalizeSint_eq_self ⟨56, by decide⟩ _ ht.1 ht.2]
  have hseconds' : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) secondsRaw = seconds := by
    rw [u256_land_comm]; exact hseconds
  have h128 := uadd_word_ofNat_toNat cache 128
    (show cache.toNat + 128 < UInt256.size by change _ < 2 ^ 256; omega)
  have h96 := uadd_word_ofNat_toNat cache 96
    (show cache.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have h160 := uadd_word_ofNat_toNat cache 160
    (show cache.toNat + 160 < UInt256.size by change _ < 2 ^ 256; omega)
  have hb128 : (cache + UInt256.ofNat 128).toNat + 32 ≤ 2 ^ 200 := by rw [h128]; omega
  have hb96 : (cache + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 := by rw [h96]; omega
  have hb160 : (cache + UInt256.ofNat 160).toNat + 32 ≤ 2 ^ 200 := by rw [h160]; omega
  obtain ⟨hm0, hc0, hs0, hd0, hpre⟩ :=
    swapObservationStoreMemory c s d tick seconds hm hc hs hd hcl hcachep hpq
  have hm1 := hm0.expand32 (cache + UInt256.ofNat 128) hb128
  have hm2 := hm1.expand32 (cache + UInt256.ofNat 96) hb96
  have hm3 := hm2.expand32 (cache + UInt256.ofNat 160) hb160
  have hmono1 := expandedWords_mono (off := cache + UInt256.ofNat 128) (size := ⟨32⟩)
    hm.active hb128
  have hmono2 := expandedWords_mono (off := cache + UInt256.ofNat 96) (size := ⟨32⟩)
    hm1.active hb96
  have hmono3 := expandedWords_mono (off := cache + UInt256.ofNat 160) (size := ⟨32⟩)
    hm2.active hb160
  have rr := uniswapV3Pool_block_3741 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_3741_stack, uniswapV3Pool_block_3741_memory,
    amountDeltaMask160, hseconds', htick, hclean, h128, h96, h160] at rr
  refine ⟨_, _, _, ?_, rr, hm3, hc0, hs0, hd0, hpre,
    hmono1.trans (hmono2.trans hmono3)⟩
  dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
