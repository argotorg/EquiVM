import Benchmarks.UniswapV4PoolManager.PoolKeyEncodeMemory
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_039

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem liquidityKeyEncodeMemory {mem : ByteArray} {free keyPtr selector sender : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hs : UInt256.land sender solcAddrMask = sender)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size) :
    poolManagerBlocks.poolManager_block_14027_memory
      (mem := writeWord mem (free+UInt256.ofNat 32).toNat selector)
      (x0 := free+UInt256.ofNat 36) (x1 := sender) (x2 := keyPtr) =
      wordCallMemory mem (free.toNat+32) selector (sender :: poolKeyWordList key) := by
  have hadd : (free+UInt256.ofNat 36)+UInt256.ofNat 32 = free+UInt256.ofNat 68 := by
    rw [u256_add_assoc]; rfl
  have hm : poolManagerBlocks.poolManager_block_14027_memory
      (mem := writeWord mem (free+UInt256.ofNat 32).toNat selector)
      (x0 := free+UInt256.ofNat 36) (x1 := sender) (x2 := keyPtr) =
      writeWord (poolKeyPrefixMemory mem free keyPtr selector sender)
        ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat
        (UInt256.land (memLoad (keyPtr+UInt256.ofNat 128)
          (poolKeyPrefixMemory mem free keyPtr selector sender)) solcAddrMask) := by
    simp only [poolManagerBlocks.poolManager_block_14027_memory, poolKeyPrefixMemory,
      show UInt256.land sender (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = sender from hs,
      hadd, Reasoning.Theory.writeWord]
    rfl
  have h68 := uadd_word_ofNat_toNat free 68 (by omega : free.toNat+68 < UInt256.size)
  have h196 : ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat = free.toNat+196 := by
    rw [uadd_word_ofNat_toNat _ 128 (by rw [h68]; omega), h68]
  rw [hm, poolKeyPrefixMemory_hook hv hc hb (by omega),
    poolKeyPrefixMemory_eq hv hc hb (by omega), h196]
  simp only [wordCallMemory, poolKeyPrefixWords, poolKeyWordList, wordSequenceMemory, Nat.add_assoc]

theorem modifyLiquidityEncodeMemory {mem : ByteArray} {ptr dest : UInt256} {p : ModifyLiquidityWords}
    (hv : MemorySlice mem ptr.toNat (wordBytes (modifyLiquidityWords p)))
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hb : ptr.toNat+128 ≤ dest.toNat+192)
    (hp : ptr.toNat+128 < UInt256.size) (hf : dest.toNat+320 < UInt256.size) :
    poolManagerBlocks.poolManager_block_14152_memory (mem := mem) (x0 := ptr) (x2 := dest) =
      wordSequenceMemory mem (dest.toNat+192) (modifyLiquidityWords p) := by
  have h192 := uadd_word_ofNat_toNat dest 192 (by omega : dest.toNat+192 < UInt256.size)
  have h224 := uadd_word_ofNat_toNat dest 224 (by omega : dest.toNat+224 < UInt256.size)
  have h256 := uadd_word_ofNat_toNat dest 256 (by omega : dest.toNat+256 < UInt256.size)
  have h288 := uadd_word_ofNat_toNat dest 288 (by omega : dest.toNat+288 < UInt256.size)
  have h0 : UInt256.signextend (UInt256.ofNat 2) (memLoad ptr mem) = p.lower := by
    rw [hv.word_load (i := 0) (word := p.lower) rfl (by omega)]
    exact (signextend24_eq_iff _).mpr hl
  let m0 := writeWord mem (dest+UInt256.ofNat 192).toNat p.lower
  have hv0 : MemorySlice m0 ptr.toNat (wordBytes (modifyLiquidityWords p)) :=
    hv.writeWord _ _ (.inl (by simp only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil]; rw [h192]; omega))
  have h1 : UInt256.signextend (UInt256.ofNat 2) (memLoad (ptr+UInt256.ofNat 32) m0) = p.upper := by
    rw [hv0.word_load (i := 1) (word := p.upper) rfl (by
      rw [uadd_word_ofNat_toNat ptr 32 (by omega)])]
    exact (signextend24_eq_iff _).mpr hu
  let m1 := writeWord m0 (dest+UInt256.ofNat 224).toNat p.upper
  have hv1 : MemorySlice m1 ptr.toNat (wordBytes (modifyLiquidityWords p)) :=
    hv0.writeWord _ _ (.inl (by simp only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil]; rw [h224]; omega))
  have h2 : memLoad (ptr+UInt256.ofNat 64) m1 = p.delta :=
    hv1.word_load (i := 2) (word := p.delta) rfl (by rw [uadd_word_ofNat_toNat ptr 64 (by omega)])
  let m2 := writeWord m1 (dest+UInt256.ofNat 256).toNat p.delta
  have hv2 : MemorySlice m2 ptr.toNat (wordBytes (modifyLiquidityWords p)) :=
    hv1.writeWord _ _ (.inl (by simp only [wordBytes_size, modifyLiquidityWords, List.length_cons, List.length_nil]; rw [h256]; omega))
  have h3 : memLoad (UInt256.ofNat 96+ptr) m2 = p.salt := by
    rw [u256_add_comm]
    exact hv2.word_load (i := 3) (word := p.salt) rfl (by rw [uadd_word_ofNat_toNat ptr 96 (by omega)])
  dsimp only [m0, m1, m2, Reasoning.Theory.writeWord] at h1 h2 h3
  simp only [poolManagerBlocks.poolManager_block_14152_memory, h0, h1, h2, h3]
  simp only [h192, h224, h256, h288, modifyLiquidityWords, wordSequenceMemory,
    Reasoning.Theory.writeWord, Nat.add_assoc]

end Benchmarks.UniswapV4PoolManager
