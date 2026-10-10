import Benchmarks.UniswapV3.Pool.SwapInitMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCacheRawTailMem_load {mem : ByteArray} {aw p : UInt256}
    (fee : UInt256) (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 192 ≤ 2 ^ 200) :
    memLoad (UInt256.ofNat 64)
      (swapCacheRawTailMem
        (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
        (UInt256.ofNat 64 + p) (UInt256.ofNat I.header.timestamp)) =
      p + UInt256.ofNat 192 := by
  rw [swapCacheRawTailMem_eq mem p fee σ I (by change _ < 2 ^ 256; omega)]
  exact (wordArrayAllocMem_heap mem p aw (swapCacheInitWords fee σ I)
    hm.lower (by simp [swapCacheInitWords]) hb hm.active).load64

theorem swapStateHeadMem_prefix (mem : ByteArray) (p remaining : UInt256)
    (hb : p.toNat + 32 < UInt256.size) :
    MemoryPrefix mem (swapStateHeadMem mem p remaining) p.toNat := by
  have h32 : (UInt256.ofNat 32 + p).toNat = p.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 32 hb
  exact (memoryPrefix_sparse_writeWord mem 64 p.toNat _ (Or.inr (by decide))).trans
    ((memoryPrefix_sparse_writeWord _ p.toNat p.toNat remaining (Or.inl (by omega))).trans
      (memoryPrefix_sparse_writeWord _ (UInt256.ofNat 32 + p).toNat p.toNat _
        (Or.inl (by rw [h32]; omega))))

theorem swapInitMemory_prefix (mem : ByteArray) (p fee remaining : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) (hb : p.toNat + 224 < UInt256.size) :
    MemoryPrefix mem
      (swapStateHeadMem (wordArrayAllocMem mem p (swapCacheInitWords fee σ I))
        (p + UInt256.ofNat 192) remaining) p.toNat := by
  have h192 := uadd_word_ofNat_toNat p 192 (by omega)
  exact (wordArrayAllocMem_prefix mem p _).trans
    ((swapStateHeadMem_prefix _ _ remaining (by rw [h192]; omega)).mono (by rw [h192]; omega))

theorem swapInitStack_eq {mem : ByteArray} {aw p : UInt256}
    (fee remaining price snap x2 x5 x6 x7 x8 x9 : UInt256) (R : List UInt256)
    (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 192 ≤ 2 ^ 200)
    (hp : memLoad snap
      (swapStateHeadMem (wordArrayAllocMem mem p (swapCacheInitWords fee σ I))
        (p + UInt256.ofNat 192) remaining) = price) :
    uniswapV3Pool_block_2822_stack
      (mem := swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
      (x0 := UInt256.ofNat I.header.timestamp) (x1 := UInt256.ofNat 64 + p)
      (x2 := x2) (x4 := snap) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9)
      (x10 := remaining) (R := R) =
      [UInt256.ofNat 1, UInt256.ofNat 1, price,
        (p + UInt256.ofNat 192) + UInt256.ofNat 64, p + UInt256.ofNat 192, ⟨0⟩,
        UInt256.sgt remaining (UInt256.ofNat 0), x2, snap, x5, x6, x7, x8, x9, remaining] ++ R := by
  let tail := swapCacheRawTailMem
    (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
    (UInt256.ofNat 64 + p) (UInt256.ofNat I.header.timestamp)
  have hload : memLoad (UInt256.ofNat 64) tail = p + UInt256.ofNat 192 :=
    swapCacheRawTailMem_load fee σ I hm hb
  have hmem := swapInitMemory_eq (remaining := remaining) fee σ I hm hb
  have hzero : UInt256.ofNat 0 + snap = snap := u256_zero_add snap
  change [UInt256.ofNat 1, UInt256.ofNat 1,
    memLoad (UInt256.ofNat 0 + snap)
      (uniswapV3Pool_block_2822_memory
        (mem := swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ I)
        (x0 := UInt256.ofNat I.header.timestamp) (x1 := UInt256.ofNat 64 + p)
        (x10 := remaining)),
    UInt256.ofNat 32 + (UInt256.ofNat 32 + memLoad (UInt256.ofNat 64) tail),
    memLoad (UInt256.ofNat 64) tail, ⟨0⟩, UInt256.sgt remaining (UInt256.ofNat 0),
    x2, snap, x5, x6, x7, x8, x9, remaining] ++ R = _
  rw [hmem, hzero, hp, hload]
  have h64 : UInt256.ofNat 32 + (UInt256.ofNat 32 + (p + UInt256.ofNat 192)) =
      (p + UInt256.ofNat 192) + UInt256.ofNat 64 := by
    rw [← u256_add_assoc, u256_add_comm]; rfl
  rw [h64]

end Benchmarks.UniswapV3.Pool
