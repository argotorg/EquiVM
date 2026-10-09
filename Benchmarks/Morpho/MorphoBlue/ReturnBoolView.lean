import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: just the length and first word needed by an optional bool decoder.
structure ReturnBoolView (mem : ByteArray) (data : UInt256) (out : ByteArray) (limit : Nat) : Prop where
  lower : 96 ≤ data.toNat
  header_bound : data.toNat + 32 ≤ limit ∧ data.toNat + 32 ≤ mem.size
  header : memLoad data mem = UInt256.ofNat out.size
  word_bound : 32 ≤ out.size → 96 ≤ (data + UInt256.ofNat 32).toNat ∧
    (data + UInt256.ofNat 32).toNat + 32 ≤ limit ∧
    (data + UInt256.ofNat 32).toNat + 32 ≤ mem.size
  word : 32 ≤ out.size → memLoad (data + UInt256.ofNat 32) mem = calldataWord out 0

theorem ReturnBoolView.preserve {before after : ByteArray} {data : UInt256} {out : ByteArray}
    {limit : Nat} (h : ReturnBoolView before data out limit)
    (hp : MemoryPrefix before after limit) : ReturnBoolView after data out limit := by
  refine ⟨h.lower, ⟨h.header_bound.1, le_trans h.header_bound.2 hp.size⟩, ?_, ?_, ?_⟩
  · rw [memoryPrefix_memLoad hp data h.lower h.header_bound.1 h.header_bound.2]
    exact h.header
  · intro hw
    exact ⟨(h.word_bound hw).1, (h.word_bound hw).2.1, le_trans (h.word_bound hw).2.2 hp.size⟩
  · intro hw
    rw [memoryPrefix_memLoad hp _ (h.word_bound hw).1 (h.word_bound hw).2.1 (h.word_bound hw).2.2]
    exact h.word hw

theorem returnBoolView_allocated {mem out : ByteArray} {ptr : UInt256}
    (hm : MorphoHeap mem ptr 0) (hn : out.size ≠ 0)
    (hfit : ptr.toNat + (out.size + 63) / 32 * 32 < 2 ^ 64) :
    ReturnBoolView (bytesAllocMem mem out ptr) ptr out (bytesAllocPtr ptr out.size).toNat := by
  have hp := bytesAllocPtr_toNat (ptr := ptr) (size := out.size) (by omega)
  have h32 := uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have hs := bytesAllocMem_properties_of_gap hm.size hm.lower (by have hg := hm.gap; omega) hn
    (by change _ < 2 ^ 256; omega)
  refine ⟨hm.lower, ?_, hs.2.2.1, ?_, hs.2.2.2⟩
  · rw [hp, hs.1]; constructor <;> omega
  · intro hw
    rw [hp, hs.1, h32]
    have hl := hm.lower
    exact ⟨by omega, by omega, by omega⟩

theorem returnBoolView_empty {mem out : ByteArray} {limit : Nat}
    (hn : out.size = 0) (hm : 128 ≤ mem.size) (hl : 128 ≤ limit)
    (hz : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0) :
    ReturnBoolView mem (UInt256.ofNat 96) out limit := by
  refine ⟨by decide, ⟨hl, hm⟩, ?_, ?_, ?_⟩
  · rw [hn]; exact hz
  · intro hw; omega
  · intro hw; omega

end Benchmarks.Morpho.MorphoBlue
