import Benchmarks.UniswapV3.Pool.SwapCacheHeadTrace
import Benchmarks.UniswapV3.Pool.WordArrayUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCacheRawTailMem (mem : ByteArray) (cursor time : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord mem cursor.toNat
    (UInt256.land (UInt256.ofNat 4294967295) time))
      (UInt256.ofNat 32 + cursor).toNat ⟨0⟩)
      (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)).toNat ⟨0⟩)
      (UInt256.ofNat 32 + (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor))).toNat ⟨0⟩

def swapCacheInitWords (fee : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List UInt256 :=
  [fee, poolLiquidityWord σ I, blockTimestampWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩]

theorem swapCacheRawTailMem_eq (mem : ByteArray) (p fee : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) (hb : p.toNat + 192 < UInt256.size) :
    swapCacheRawTailMem
      (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
      (UInt256.ofNat 64 + p) (UInt256.ofNat I.header.timestamp) =
      wordArrayAllocMem mem p (swapCacheInitWords fee σ I) := by
  have h32 := uadd_word_ofNat_toNat p 32 (by omega)
  have h64 := uadd_word_ofNat_toNat p 64 (by omega)
  have h96 := uadd_word_ofNat_toNat p 96 (by omega)
  have h128 := uadd_word_ofNat_toNat p 128 (by omega)
  have h160 := uadd_word_ofNat_toNat p 160 (by omega)
  have h64w : UInt256.ofNat 64 + p = p + UInt256.ofNat 64 := u256_add_comm _ _
  have h96w : UInt256.ofNat 32 + (UInt256.ofNat 64 + p) = p + UInt256.ofNat 96 := by
    rw [← u256_add_assoc, u256_add_comm]; rfl
  have h128w : UInt256.ofNat 32 +
      (UInt256.ofNat 32 + (UInt256.ofNat 64 + p)) = p + UInt256.ofNat 128 := by
    rw [← u256_add_assoc, ← u256_add_assoc, u256_add_comm]; rfl
  have h160w : UInt256.ofNat 32 + (UInt256.ofNat 32 +
      (UInt256.ofNat 32 + (UInt256.ofNat 64 + p))) = p + UInt256.ofNat 160 := by
    rw [← u256_add_assoc, ← u256_add_assoc, ← u256_add_assoc, u256_add_comm]; rfl
  have htime : UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat I.header.timestamp) =
      blockTimestampWord I := u256_land_comm _ _
  unfold swapCacheRawTailMem
  rw [h160w, h128w, h96w, h64w]
  simp only [swapCacheHeadMem, wordArrayAllocMem, swapCacheInitWords, writeWordArray,
    List.length_cons, List.length_nil, h32, h64, h96, h128, h160, htime]

def swapStateHeadMem (mem : ByteArray) (p remaining : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem 64 (p + UInt256.ofNat 224)) p.toNat remaining)
    (UInt256.ofNat 32 + p).toNat ⟨0⟩

theorem swapInitMemory_eq {mem : ByteArray} {aw p remaining : UInt256}
    (fee : UInt256) (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 192 ≤ 2 ^ 200) :
    uniswapV3Pool_block_2822_memory
      (mem := swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
      (x0 := UInt256.ofNat I.header.timestamp) (x1 := UInt256.ofNat 64 + p)
      (x10 := remaining) =
      swapStateHeadMem (wordArrayAllocMem mem p (swapCacheInitWords fee σ I))
        (p + UInt256.ofNat 192) remaining := by
  have htail := swapCacheRawTailMem_eq mem p fee σ I (by change _ < 2 ^ 256; omega)
  have hh := wordArrayAllocMem_heap mem p aw (swapCacheInitWords fee σ I)
    hm.lower (by simp [swapCacheInitWords]) hb hm.active
  have hload : memLoad (UInt256.ofNat 64)
      (wordArrayAllocMem mem p (swapCacheInitWords fee σ I)) = p + UInt256.ofNat 192 := hh.load64
  change writeWord (writeWord (writeWord
    (swapCacheRawTailMem
      (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
      (UInt256.ofNat 64 + p) (UInt256.ofNat I.header.timestamp)) 64
    (UInt256.ofNat 224 + memLoad (UInt256.ofNat 64)
      (swapCacheRawTailMem
        (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
        (UInt256.ofNat 64 + p) (UInt256.ofNat I.header.timestamp))))
    (memLoad (UInt256.ofNat 64)
      (swapCacheRawTailMem
        (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
        (UInt256.ofNat 64 + p) (UInt256.ofNat I.header.timestamp))).toNat remaining)
    (UInt256.ofNat 32 + memLoad (UInt256.ofNat 64)
      (swapCacheRawTailMem
        (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
        (UInt256.ofNat 64 + p) (UInt256.ofNat I.header.timestamp))).toNat ⟨0⟩ = _
  rw [htail, hload, u256_add_comm (UInt256.ofNat 224)]
  rfl

end Benchmarks.UniswapV3.Pool
