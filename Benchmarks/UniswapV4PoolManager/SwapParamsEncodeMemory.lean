import Benchmarks.UniswapV4PoolManager.SwapParams
import Benchmarks.UniswapV4PoolManager.MemorySlice
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapParamsEncodeMemory {mem : ByteArray} {ptr dest : UInt256} {p : SwapParamsWords}
    (hv : MemorySlice mem ptr.toNat (wordBytes (swapParamsWordList p)))
    (hl : p.priceLimit.toNat < 2^160) (hb : ptr.toNat+96 ≤ dest.toNat+228)
    (hp : ptr.toNat+96 < UInt256.size) (hf : dest.toNat+324 < UInt256.size) :
    poolManagerBlocks.poolManager_block_15382_memory (mem := mem) (x0 := ptr) (x5 := dest) =
      wordSequenceMemory mem (dest.toNat+228) (swapParamsWordList p) := by
  have h228 := uadd_word_ofNat_toNat dest 228 (by omega : dest.toNat+228 < UInt256.size)
  have h260 := uadd_word_ofNat_toNat dest 260 (by omega : dest.toNat+260 < UInt256.size)
  have h292 := uadd_word_ofNat_toNat dest 292 (by omega : dest.toNat+292 < UInt256.size)
  have h0 : UInt256.isZero (UInt256.isZero (memLoad ptr mem)) = UInt256.fromBool p.zeroForOne := by
    rw [hv.word_load (i := 0) (word := UInt256.fromBool p.zeroForOne) rfl (by omega)]
    cases p.zeroForOne <;> rfl
  let m0 := writeWord mem (dest+UInt256.ofNat 228).toNat (UInt256.fromBool p.zeroForOne)
  have hv0 : MemorySlice m0 ptr.toNat (wordBytes (swapParamsWordList p)) :=
    hv.writeWord _ _ (.inl (by
      simp only [wordBytes_size, swapParamsWordList, List.length_cons, List.length_nil]; rw [h228]; omega))
  have h1 : memLoad (ptr+UInt256.ofNat 32) m0 = p.amountSpecified :=
    hv0.word_load (i := 1) (word := p.amountSpecified) rfl (by rw [uadd_word_ofNat_toNat ptr 32 (by omega)])
  let m1 := writeWord m0 (dest+UInt256.ofNat 260).toNat p.amountSpecified
  have hv1 : MemorySlice m1 ptr.toNat (wordBytes (swapParamsWordList p)) :=
    hv0.writeWord _ _ (.inl (by
      simp only [wordBytes_size, swapParamsWordList, List.length_cons, List.length_nil]; rw [h260]; omega))
  have h2 : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (memLoad (UInt256.ofNat 64+ptr) m1) = p.priceLimit := by
    rw [u256_add_comm, hv1.word_load (i := 2) (word := p.priceLimit) rfl (by
      rw [uadd_word_ofNat_toNat ptr 64 (by omega)]), u256_land_comm]
    exact solcAddrMask_clean hl
  dsimp only [m0, m1, Reasoning.Theory.writeWord] at h1 h2
  simp only [poolManagerBlocks.poolManager_block_15382_memory, h0, h1, h2]
  simp only [h228, h260, h292, swapParamsWordList, wordSequenceMemory,
    Reasoning.Theory.writeWord, Nat.add_assoc]

end Benchmarks.UniswapV4PoolManager
