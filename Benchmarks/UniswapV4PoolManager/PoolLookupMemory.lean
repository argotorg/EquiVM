import Benchmarks.UniswapV4PoolManager.PoolStorage
import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.WordStoreMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

/-- The public pool operations hash the id in scratch space and cache its storage slot at 128. -/
def poolLookupMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  writeWord (twoWordHashMem id ⟨6⟩ mem) 128 (poolSlot id)

theorem poolLookupMemory_size {mem : ByteArray} (id : UInt256) (hm : 160 ≤ mem.size) :
    (poolLookupMemory mem id).size = mem.size := by
  change (writeWord (writeWord (writeWord mem 0 id) 32 ⟨6⟩) 128 (poolSlot id)).size = _
  simp only [writeWord_sparse_size]
  omega

theorem poolLookupMemory_slot (mem : ByteArray) (id : UInt256) :
    memLoad (UInt256.ofNat 128) (poolLookupMemory mem id) = poolSlot id :=
  writeWord_sparse_load_back _ (UInt256.ofNat 128) _

theorem poolLookupMemory_slotView (mem : ByteArray) (id : UInt256) :
    MemorySlice (poolLookupMemory mem id) 128 (wordBytes [poolSlot id]) := by
  refine ⟨?_, ?_⟩
  · change (writeWord (twoWordHashMem id ⟨6⟩ mem) 128 (poolSlot id)).readWithPadding 128
      (wordBytes [poolSlot id]).size = _
    rw [wordBytes_size]
    change (writeWord (twoWordHashMem id ⟨6⟩ mem) 128 (poolSlot id)).readWithPadding 128 32 = _
    rw [writeWord_sparse_read_back]
    simp only [wordBytes, ByteArray.append_empty]
  · rw [wordBytes_size]
    change 128+32 ≤ (writeWord (twoWordHashMem id ⟨6⟩ mem) 128 (poolSlot id)).size
    rw [writeWord_sparse_size]
    exact le_max_right _ _

theorem poolLookupMemory_free {mem : ByteArray} (id : UInt256) (hm : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (poolLookupMemory mem id) = memLoad (UInt256.ofNat 64) mem := by
  change memLoad (UInt256.ofNat 64)
    (writeWord (writeWord (writeWord mem 0 id) 32 ⟨6⟩) 128 (poolSlot id)) = _
  rw [writeWord_sparse_load_disjoint _ 128 _ (UInt256.ofNat 64)
      (by change 96 ≤ _; simp only [writeWord_sparse_size]; omega)
      (.inl (by decide)),
    writeWord_sparse_load_disjoint _ 32 _ (UInt256.ofNat 64)
      (by change 96 ≤ _; rw [writeWord_sparse_size]; omega) (.inr (by decide)),
    writeWord_sparse_load_disjoint _ 0 _ (UInt256.ofNat 64) hm (.inr (by decide))]

theorem MemorySlice.poolLookup {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (id : UInt256) (hb : 160 ≤ base) :
    MemorySlice (poolLookupMemory mem id) base data := by
  exact ((h.writeWord 0 id (.inr (by omega))).writeWord 32 ⟨6⟩ (.inr (by omega))).writeWord
    128 (poolSlot id) (.inr hb)

theorem PoolKeyView.poolLookup {mem ptr key} (h : PoolKeyView mem ptr key)
    (id : UInt256) (hp : 160 ≤ ptr.toNat) : PoolKeyView (poolLookupMemory mem id) ptr key :=
  ⟨h.slice.poolLookup id hp, h.fits⟩

end Benchmarks.UniswapV4PoolManager
