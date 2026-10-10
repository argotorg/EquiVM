import Benchmarks.UniswapV3.Pool.SwapProtocolUpdateTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapProtocolX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q cache exactWord free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3504⟩ ([q, p, exactWord, cache] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (hf : c.feeProtocol.toNat < 256) (hp : 96 ≤ p.toNat)
    (hcache : cache.toNat + 192 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3574⟩ ([q, p, exactWord, cache] ++ R)
        mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' free ∧
      SwapStateMemory mem' p (swapProtocolState c s d) ∧
      SwapIterationMemory mem' q (swapProtocolData c d) ∧
      MemoryPrefix mem mem' p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  have hload := SwapCacheMemory.load_feeProtocol hc (by change _ < 2 ^ 256; omega)
  have hclean : UInt256.land (UInt256.ofNat 255) c.feeProtocol = c.feeProtocol := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 8) _ _ (by decide) hf
  have hbc : cache.toNat + 32 ≤ 2 ^ 200 := by omega
  have hcache0 : UInt256.ofNat 0 + cache = cache := u256_zero_add cache
  have hm0 := hm.expand32 cache hbc
  have hmono0 := expandedWords_mono (off := cache) (size := ⟨32⟩) hm.active hbc
  by_cases hz : c.feeProtocol = ⟨0⟩
  · have he : swapProtocolEnabled c = false := by
      simp only [swapProtocolEnabled, hz, u256_zero_toNat, lt_self_iff_false, decide_false]
    have r1 := uniswapV3Pool_block_3504_taken (immWords := wordsOf (immStore v))
      (by change R.length + 6 ≤ 1024; omega)
      (by rw [hload, hclean, hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨mem, _, k + 8, C + (29 + memExpansionCost aw cache ⟨32⟩), ?_, r1, hm0,
      ?_, ?_, MemoryPrefix.refl _ _, hmono0⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [swapProtocolState, he, Bool.false_eq_true, if_false] using hs
    · simpa only [swapProtocolData, he, Bool.false_eq_true, if_false] using hd
  · have hpos : 0 < c.feeProtocol.toNat :=
      Nat.pos_of_ne_zero (fun h ↦ hz (u256_inj h))
    have he : swapProtocolEnabled c = true := decide_eq_true hpos
    have r1 := uniswapV3Pool_block_3504_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 6 ≤ 1024; omega)
      (by rw [hload, hclean]; exact isZero_eq_zero_of_ne hz) rd
    have hfee : memLoad (UInt256.ofNat 192 + q) mem = d.feeAmount := by
      rw [u256_add_comm]
      exact SwapIterationMemory.load_fee hd (by change _ < 2 ^ 256; omega)
    have r2 := uniswapV3Pool_block_3515_taken (immWords := wordsOf (immStore v))
      (by change R.length + 9 ≤ 1024; omega)
      (by rw [hcache0, hload, hclean]; exact hz)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_3515_taken_stack, hcache0, hload, hclean, hfee] at r2
    have hbf : (UInt256.ofNat 192 + q).toNat + 32 ≤ 2 ^ 200 := by
      rw [u256_add_comm, uadd_word_ofNat_toNat q 192 (by change _ < 2 ^ 256; omega)]
      omega
    have hm1 := hm0.expand32 cache hbc
    have hm2 := hm1.expand32 (UInt256.ofNat 192 + q) hbf
    have hmono1 := expandedWords_mono (off := cache) (size := ⟨32⟩) hm0.active hbc
    have hmono2 := expandedWords_mono (off := UInt256.ofNat 192 + q) (size := ⟨32⟩)
      hm1.active hbf
    obtain ⟨a3, k3, C3, hC3, r3, hm3, hs3, hd3, hp3, hmono3⟩ :=
      swapProtocolUpdateX (v := v) c s d r2 hm2 hs hd hp hdisj hb
        (by change R.length + 2 + 8 ≤ 1024; omega)
    refine ⟨_, a3, k3, C3, ?_, r3, hm3, ?_, ?_, hp3,
      hmono0.trans (hmono1.trans (hmono2.trans hmono3))⟩
    · dsimp only [memExpansionCost, M, expandedWords] at hC3 ⊢
      omega
    · simpa only [swapProtocolState, he, if_true] using hs3
    · simpa only [swapProtocolData, he, if_true] using hd3

end Benchmarks.UniswapV3.Pool
