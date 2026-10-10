import Benchmarks.UniswapV3.Pool.SwapSlotWords
import Benchmarks.UniswapV3.Pool.SwapWriteGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapWriteStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cache snap exactWord free index cardinality : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4077⟩
      ([cardinality, index, ⟨0⟩, ⟨0⟩, p, exactWord, cache, snap] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hfit : s.Fits) (hperm : ee.perm = true) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 15 ≤ 1024) :
    ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨4268⟩ ([p, exactWord, cache, snap] ++ R) mem aw' rdata
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (swapSlotFieldsWord (solcSlotWordAt ⟨0⟩ σ ee) s.price (EVM.wordOfInt s.tick)
            index cardinality)) k' C' ∧ HeapMemory mem aw' free := by
  have ht : memLoad (p + UInt256.ofNat 96) mem = EVM.wordOfInt s.tick :=
    SwapStateMemory.load_tick hs (by change _ < 2 ^ 256; omega)
  have hp : memLoad (p + UInt256.ofNat 64) mem = s.price :=
    SwapStateMemory.load_price hs (by change _ < 2 ^ 256; omega)
  have hclean : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt s.tick) =
      EVM.wordOfInt s.tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ s.tick (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hfit.2.2.2.1.1 hfit.2.2.2.1.2]
  have hb64 : (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)]; omega
  have hb96 : (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)]; omega
  have hm1 := hm.expand32 (p + UInt256.ofNat 64) hb64
  have hm2 := hm1.expand32 (p + UInt256.ofNat 96) hb96
  obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_4077
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 12 ≤ 1024; omega) rd
  simp only [uniswapV3Pool_block_4077_stack, ht, hp, hclean] at r1
  obtain ⟨k2, C2, r2⟩ := uniswapV3Pool_block_4166
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 8 ≤ 1024; omega) hperm
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
  refine ⟨_, k2, C2, ?_, hm2⟩
  simpa only [uniswapV3Pool_block_4166_stack, swapSlotFieldsWord_reorder,
    swapSlotPriceWord_evm, swapSlotTickWord_evm, slot0ObservationWord_evm, solcSlotWordAt] using r2

theorem swapPriceStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4218⟩ (p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hperm : ee.perm = true) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨4268⟩ (p :: R) mem aw' rdata
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩
          (swapSlotFieldWord (solcSlotWordAt ⟨0⟩ σ ee) s.price false)) k' C' ∧
      HeapMemory mem aw' free := by
  have hp : memLoad (p + UInt256.ofNat 64) mem = s.price :=
    SwapStateMemory.load_price hs (by change _ < 2 ^ 256; omega)
  have hb64 : (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)]; omega
  obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_4218
    (immWords := wordsOf (immStore v)) hov hperm rd
  refine ⟨_, k1, C1, ?_, hm.expand32 (p + UInt256.ofNat 64) hb64⟩
  simpa only [hp, swapSlotPriceWord_evm, solcSlotWordAt] using r1

end Benchmarks.UniswapV3.Pool
