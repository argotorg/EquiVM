import Benchmarks.UniswapV4PoolManager.PoolSwapAllocatedMemory
import Benchmarks.UniswapV4PoolManager.MemoryWindowSlice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapAllocatedMemory_size (mem : ByteArray) (evm : State) (id state : UInt256)
    (hl : 96 ≤ state.toNat) (hf : state.toNat+96 < UInt256.size) :
    (poolSwapAllocatedMem mem evm id state).size = max mem.size (state.toNat+96) := by
  unfold poolSwapAllocatedMem poolSwapLoadedMem
  rw [poolSwapResultInitMem_eq _ _ _ _ hf, poolSwapResultZeroMem_eq _ _ hf,
    wordSequenceMemory_size_nonempty _ _ _ (by intro hh; cases hh),
    wordSequenceMemory_size_nonempty _ _ _ (by intro hh; cases hh), writeWord_sparse_size]
  simp only [poolSwapResultWordList, List.length_cons, List.length_nil]
  omega

theorem MemorySlice.poolSwapAllocated {mem data : ByteArray} {base : Nat} {state : UInt256}
    (h : MemorySlice mem base data) (evm : State) (id : UInt256)
    (hl : 96 ≤ base) (hb : base+data.size ≤ state.toNat) (hf : state.toNat+96 < UInt256.size) :
    MemorySlice (poolSwapAllocatedMem mem evm id state) base data := by
  unfold poolSwapAllocatedMem poolSwapLoadedMem
  rw [poolSwapResultInitMem_eq _ _ _ _ hf, poolSwapResultZeroMem_eq _ _ hf]
  exact ((h.writeWord 64 _ (.inr hl)).wordSequence _ _ hb).wordSequence _ _ hb

theorem poolSwapPreludeMemory_size (mem : ByteArray) (evm : State) (id state : UInt256) (z : Bool)
    (hl : 96 ≤ state.toNat) (hf : state.toNat+352 < UInt256.size) :
    (poolSwapPreludeMem mem evm id state z).size = max mem.size (state.toNat+352) := by
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  unfold poolSwapPreludeMem poolSwapStepInitMem
  rw [wordSequenceMemory_size_nonempty _ _ _ (by intro hh; cases hh), writeWord_sparse_size,
    poolSwapAllocatedMemory_size _ _ _ _ hl (by omega), h96]
  change max (max (max mem.size (state.toNat+96)) (64+32)) (state.toNat+96+32*8) = _
  omega

theorem poolSwapPreludeMemory_free (mem : ByteArray) (evm : State) (id state : UInt256) (z : Bool)
    (hl : 96 ≤ state.toNat) (hf : state.toNat+352 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (poolSwapPreludeMem mem evm id state z) = state+UInt256.ofNat 352 := by
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  unfold poolSwapPreludeMem poolSwapStepInitMem
  rw [wordSequenceMemory_load_before _ _ _ _ (by rw [writeWord_sparse_size]; change 64+32 ≤ _; omega)
    (by change 64+32 ≤ _; rw [h96]; omega)]
  calc
    _ = state+UInt256.ofNat 96+UInt256.ofNat 256 := writeWord_sparse_load_back _ (UInt256.ofNat 64) _
    _ = state+UInt256.ofNat 352 := by rw [uadd_assoc]; rfl

theorem MemorySlice.poolSwapPrelude {mem data : ByteArray} {base : Nat} {state : UInt256}
    (h : MemorySlice mem base data) (evm : State) (id : UInt256) (z : Bool)
    (hl : 96 ≤ base) (hb : base+data.size ≤ state.toNat) (hf : state.toNat+352 < UInt256.size) :
    MemorySlice (poolSwapPreludeMem mem evm id state z) base data := by
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  exact ((h.poolSwapAllocated evm id hl hb (by omega)).writeWord 64 _ (.inr hl)).wordSequence _ _
    (by rw [h96]; omega)

structure PoolSwapReturnMemory (before after : ByteArray) (state free : UInt256) (r : PoolSwapResultWords) : Prop where
  result : WordStructView after state (poolSwapResultWordList r)
  freeLoad : memLoad (UInt256.ofNat 64) after = free
  freeChoice : free = state+UInt256.ofNat 96 ∨ free = state+UInt256.ofNat 352
  size : after.size = max before.size free.toNat
  saved : ∀ base data, MemorySlice before base data → 96 ≤ base → base+data.size ≤ state.toNat →
    MemorySlice after base data

theorem poolSwapAllocatedReturnMemory (mem : ByteArray) (evm : State) (id state : UInt256)
    (hl : 96 ≤ state.toNat) (hf : state.toNat+96 < UInt256.size) :
    PoolSwapReturnMemory mem (poolSwapAllocatedMem mem evm id state) state (state+UInt256.ofNat 96)
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id)) := by
  refine ⟨poolSwapAllocatedMemory_result _ _ _ _ hf, poolSwapAllocatedMemory_free _ _ _ _ hl hf,
    .inl rfl, ?_, ?_⟩
  · rw [uadd_word_ofNat_toNat state 96 hf]
    exact poolSwapAllocatedMemory_size _ _ _ _ hl hf
  · intro base data hs hb hh
    exact hs.poolSwapAllocated evm id hb hh hf

theorem poolSwapLoopReturnMemory {mem out : ByteArray} {evm : State} {id state : UInt256}
    {r : PoolSwapResultWords} {z : Bool} (hl : 96 ≤ state.toNat) (hf : state.toNat+352 < UInt256.size)
    (hr : WordStructView out state (poolSwapResultWordList r))
    (hw : MemoryWindowEq (poolSwapPreludeMem mem evm id state z) out 64
      (min (state+UInt256.ofNat 96).toNat state.toNat)) :
    PoolSwapReturnMemory mem out state (state+UInt256.ofNat 352) r := by
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  rw [h96, Nat.min_eq_right (by omega)] at hw
  refine ⟨hr, ?_, .inr rfl, ?_, ?_⟩
  · rw [hw.load (UInt256.ofNat 64) (by decide) hl]
    exact poolSwapPreludeMemory_free _ _ _ _ _ hl hf
  · rw [hw.size, uadd_word_ofNat_toNat state 352 hf]
    exact poolSwapPreludeMemory_size _ _ _ _ _ hl hf
  · intro base data hs hb hh
    exact hw.slice (hs.poolSwapPrelude evm id z hb hh hf) (by omega) hh

end Benchmarks.UniswapV4PoolManager
