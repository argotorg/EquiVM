import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams
import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def modifyLiquidityEventMemory (mem : ByteArray) (free : UInt256) (p : ModifyLiquidityWords) : ByteArray :=
  wordSequenceMemory mem free.toNat (modifyLiquidityWords p)

theorem modifyLiquidityEventMemory_compiled {mem : ByteArray} {free paramsPtr : UInt256}
    {p : ModifyLiquidityWords}
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hpb : paramsPtr.toNat+128 ≤ free.toNat) (hf : free.toNat+128 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) :
    poolManagerBlocks.poolManager_block_6084_memory (mem := mem) (x2 := paramsPtr) (x11 := ⟨64⟩) =
      modifyLiquidityEventMemory mem free p := by
  change poolManagerBlocks.poolManager_block_6084_memory (mem := mem) (x2 := paramsPtr)
    (x11 := UInt256.ofNat 64) = modifyLiquidityEventMemory mem free p
  have hload {i : Nat} {w : UInt256} (hi : (modifyLiquidityWords p)[i]? = some w) :
      memLoad (paramsPtr+UInt256.ofNat (32*i)) mem = w := by
    have hb : i < 4 := by
      have hh := (List.getElem?_eq_some_iff.mp hi).1
      simpa only [modifyLiquidityWords, List.length_cons, List.length_nil] using hh
    exact hp.word_load hi (uadd_word_ofNat_toNat paramsPtr (32*i) (by omega))
  have hlo : memLoad paramsPtr mem = p.lower := by
    have hz : paramsPtr+UInt256.ofNat (32*0) = paramsPtr := uint256_add_zero_right paramsPtr
    simpa only [hz] using (hload (i := 0) rfl)
  have hup := hload (i := 1) rfl
  have hdelta := hload (i := 2) rfl
  have hsalt := hload (i := 3) rfl
  have hc0 : UInt256.signextend (UInt256.ofNat 2) p.lower = p.lower := (signextend24_eq_iff _).mpr hl
  have hc1 : UInt256.signextend (UInt256.ofNat 2) p.upper = p.upper := (signextend24_eq_iff _).mpr hu
  have h32 := uadd_word_ofNat_toNat free 32 (by omega)
  have h64 := uadd_word_ofNat_toNat free 64 (by omega)
  have h96 := uadd_word_ofNat_toNat free 96 (by omega)
  simp only [poolManagerBlocks.poolManager_block_6084_memory, hlo, hup, hdelta, hsalt, hc0, hc1,
    hfree, modifyLiquidityEventMemory, modifyLiquidityWords, wordSequenceMemory,
    Reasoning.Theory.writeWord, h32, h64, h96, Nat.add_assoc]

theorem MemorySlice.modifyLiquidityEvent {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (free : UInt256) (p : ModifyLiquidityWords)
    (hb : base+data.size ≤ free.toNat) :
    MemorySlice (modifyLiquidityEventMemory mem free p) base data := h.wordSequence _ _ hb

theorem modifyLiquidityEventMemory_size (mem : ByteArray) (free : UInt256) (p : ModifyLiquidityWords) :
    (modifyLiquidityEventMemory mem free p).size = max mem.size (free.toNat+128) := by
  simp only [modifyLiquidityEventMemory, modifyLiquidityWords, wordSequenceMemory, writeWord_sparse_size]
  omega

theorem modifyLiquidityEventMemory_free (mem : ByteArray) (free : UInt256) (p : ModifyLiquidityWords)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ free.toNat) :
    memLoad (UInt256.ofNat 64) (modifyLiquidityEventMemory mem free p) = memLoad (UInt256.ofNat 64) mem := by
  have h64 : (UInt256.ofNat 64).toNat = 64 := rfl
  rw [memLoad, memLoad, h64,
    if_neg (by rw [modifyLiquidityEventMemory_size]; omega), if_neg (by omega)]
  rw [modifyLiquidityEventMemory, wordSequenceMemory_read_below _ _ _ _ hmem hlo]

end Benchmarks.UniswapV4PoolManager
