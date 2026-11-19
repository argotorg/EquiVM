import Benchmarks.Midnight.MemoryWords

/-! Remembering an existing region of aligned memory words across a decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: snapshot arbitrary existing words without rewriting memory.
def memoryWordSnapshot (mem : ByteArray) (base count : Nat) : List UInt256 :=
  (List.range count).map (fun i ↦ memLoad (UInt256.ofNat (base + 32 * i)) mem)

theorem memoryWordSnapshot_length (mem : ByteArray) (base count : Nat) :
    (memoryWordSnapshot mem base count).length = count := by
  simp only [memoryWordSnapshot, List.length_map, List.length_range]

theorem MemoryWords.snapshot (mem : ByteArray) (base count : Nat)
    (hb : base + 32 * count < UInt256.size) (hm : base + 32 * count ≤ mem.size) :
    MemoryWords mem base (memoryWordSnapshot mem base count) := by
  refine ⟨by rwa [memoryWordSnapshot_length], by rwa [memoryWordSnapshot_length], ?_⟩
  intro i
  change memLoad (UInt256.ofNat (base + 32 * i.val)) mem =
    (memoryWordSnapshot mem base count)[i.val]
  simp only [memoryWordSnapshot, List.getElem_map, List.getElem_range]

theorem MemoryWords.snapshot_load {before after : ByteArray} {base count : Nat}
    (h : MemoryWords after base (memoryWordSnapshot before base count))
    (i : Nat) (hi : i < count) :
    memLoad (UInt256.ofNat (base + 32 * i)) after =
      memLoad (UInt256.ofNat (base + 32 * i)) before := by
  have hi' : i < (memoryWordSnapshot before base count).length := by
    rwa [memoryWordSnapshot_length]
  have he := h.load ⟨i, hi'⟩
  change memLoad (UInt256.ofNat (base + 32 * i)) after =
    (memoryWordSnapshot before base count)[i] at he
  simpa only [memoryWordSnapshot, List.getElem_map, List.getElem_range] using he

-- LIBRARY CANDIDATE: identical aligned writes preserve a word-snapshot correspondence.
theorem MemoryWords.snapshot_writeWord {before after : ByteArray} {base count : Nat}
    (h : MemoryWords after base (memoryWordSnapshot before base count))
    (hb : base + 32 * count ≤ before.size) (i : Nat) (hi : i < count) (word : UInt256) :
    MemoryWords (Reasoning.Theory.writeWord after (base + 32 * i) word) base
      (memoryWordSnapshot (Reasoning.Theory.writeWord before (base + 32 * i) word)
        base count) := by
  have hbound : base + 32 * count < UInt256.size := by
    simpa only [memoryWordSnapshot_length] using h.bound
  have hsize : base + 32 * count ≤ after.size := by
    simpa only [memoryWordSnapshot_length] using h.size
  refine ⟨by rwa [memoryWordSnapshot_length], by
    rw [memoryWordSnapshot_length, writeWord_sparse_size]; omega, ?_⟩
  intro j
  have hj : j.val < count := by simpa only [memoryWordSnapshot_length] using j.isLt
  change memLoad (UInt256.ofNat (base + 32 * j.val)) _ =
    (memoryWordSnapshot (Reasoning.Theory.writeWord before (base + 32 * i) word)
      base count)[j.val]
  simp only [memoryWordSnapshot, List.getElem_map, List.getElem_range]
  have hr : (UInt256.ofNat (base + 32 * j.val)).toNat = base + 32 * j.val :=
    UInt256.toNat_ofNat_of_lt (by omega)
  by_cases he : i = j.val
  · have hleft := memLoad_writeWord after (UInt256.ofNat (base + 32 * j.val)) word
    have hright := memLoad_writeWord before (UInt256.ofNat (base + 32 * j.val)) word
    rw [hr] at hleft hright
    simp only [he]
    exact hleft.trans hright.symm
  · have hd : (UInt256.ofNat (base + 32 * j.val)).toNat + 32 ≤ base + 32 * i ∨
        base + 32 * i + 32 ≤ (UInt256.ofNat (base + 32 * j.val)).toNat := by
      rw [hr]
      omega
    rw [memLoad_writeWord_preserved _ _ _ _ (by rw [hr]; omega) hd,
      memLoad_writeWord_preserved _ _ _ _ (by rw [hr]; omega) hd]
    exact h.snapshot_load j.val hj

end Benchmarks.Midnight
