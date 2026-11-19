import Benchmarks.Midnight.MarketEncodeMemory
import Benchmarks.Midnight.MarketHeapMemory

/-! A dynamic byte buffer containing one complete ABI-encoded market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def MarketData.encodingSize (m : MarketData) : Nat := 320 + 128 * m.collaterals.length

theorem MarketData.encodingSize_eq (m : MarketData) :
    m.encodingSize = 32 * m.encodedWords.length := by
  rw [m.encodedWords_length]
  dsimp only [MarketData.encodingSize]
  omega

def marketBytesDataMemory (mem : ByteArray) (root : UInt256) (m : MarketData) : ByteArray :=
  marketEncodeMemory (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) (root.toNat + 64) m

def marketBytesMemory (mem : ByteArray) (root : UInt256) (m : MarketData) : ByteArray :=
  writeWord (writeWord (marketBytesDataMemory mem root m) root.toNat
    (UInt256.ofNat m.encodingSize)) 64 (root + UInt256.ofNat (m.encodingSize + 32))

theorem MarketStored.preserve {before after : ByteArray} {ptr arrayPtr root : UInt256}
    {m : MarketData} (h : MarketStored before ptr arrayPtr root m)
    (hp : MemoryPrefix before after root.toNat) : MarketStored after ptr arrayPtr root m := by
  refine ⟨?_, ?_, h.collaterals.preserve hp, h.lower, h.array, h.extent, h.bound⟩
  · apply h.words.preserve hp.size
    intro word hlo hhi
    exact hp.load word (h.lower.trans hlo)
      (by change word.toNat + 32 ≤ ptr.toNat + 32 * 8 at hhi; have := h.array; have := h.extent; omega)
      (hhi.trans h.words.size)
  · apply h.header.preserve hp.size
    intro word hlo hhi
    exact hp.load word (by have := h.lower; have := h.array; omega)
      (by simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] using
        hhi.trans (by simpa using h.extent)) (hhi.trans h.header.size)

theorem marketBytesDataMemory_prefix (mem : ByteArray) (root : UInt256) (m : MarketData) :
    MemoryPrefix mem (marketBytesDataMemory mem root m) root.toNat :=
  (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))).trans
    (marketEncodeMemory_prefix _ _ _ m (by omega))

theorem marketBytesMemory_prefix (mem : ByteArray) (root : UInt256) (m : MarketData) :
    MemoryPrefix mem (marketBytesMemory mem root m) root.toNat :=
  ((marketBytesDataMemory_prefix mem root m).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inr (by decide)))

theorem marketBytesDataMemory_words (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hroot : 96 ≤ root.toNat)
    (hb : root.toNat + m.encodingSize + 32 < UInt256.size) :
    MemoryWords (marketBytesDataMemory mem root m) (root.toNat + 32) m.encodedWords := by
  let start := writeWord mem (root.toNat + 32) (UInt256.ofNat 32)
  have hh : MemoryWords start (root.toNat + 32) [UInt256.ofNat 32] :=
    MemoryWords.of_writeWordArray mem (root.toNat + 32) [UInt256.ofNat 32] (by
      change root.toNat + 32 + 32 * 1 < UInt256.size
      dsimp only [MarketData.encodingSize] at hb; omega) (by simp)
  have hp := marketEncodeMemory_prefix start (root.toNat + 64) (root.toNat + 64) m le_rfl
  have hh' : MemoryWords (marketBytesDataMemory mem root m)
      (root.toNat + 32) [UInt256.ofNat 32] := by
    apply hh.preserve hp.size
    intro word hlo hhi
    exact hp.load word (by omega) (by simpa using hhi) (hhi.trans hh.size)
  apply hh'.append
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc] using
    marketEncodeMemory_words start (root.toNat + 64) m (by
      dsimp only [MarketData.encodingSize] at hb; omega)

theorem marketBytesMemory_words (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hroot : 96 ≤ root.toNat) (hb : root.toNat + m.encodingSize + 32 < UInt256.size) :
    MemoryWords (marketBytesMemory mem root m) (root.toNat + 32) m.encodedWords :=
  ((marketBytesDataMemory_words mem m hroot hb).writeWord _ (Or.inr le_rfl)).writeWord _
    (Or.inr (by omega))

theorem marketBytesMemory_free (mem : ByteArray) (root : UInt256) (m : MarketData) :
    memLoad (UInt256.ofNat 64) (marketBytesMemory mem root m) =
      root + UInt256.ofNat (m.encodingSize + 32) := memLoad_writeWord _ _ _

theorem marketBytesMemory_length (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hroot : 96 ≤ root.toNat) :
    memLoad root (marketBytesMemory mem root m) = UInt256.ofNat m.encodingSize := by
  rw [marketBytesMemory, memLoad_writeWord_preserved]
  · exact memLoad_writeWord _ _ _
  · rw [writeWord_sparse_size]; omega
  · right; change 64 + 32 ≤ root.toNat; exact hroot

end Benchmarks.Midnight
