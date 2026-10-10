import Benchmarks.UniswapV4PoolManager.MemoryGas

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a small memory footprint potential for operation-gas lower bounds.
def MemoryZero (mem : ByteArray) : Prop := ∀ i (hi : i < mem.size), mem[i] = 0

def MemoryOneWord (mem : ByteArray) : Prop :=
  ∃ start, ∀ i (hi : i < mem.size), mem[i] ≠ 0 → start ≤ i ∧ i < start+32

noncomputable def memoryFootprint (mem : ByteArray) : Nat := by
  classical
  exact if MemoryZero mem then 0 else if MemoryOneWord mem then 7 else 14

theorem memoryFootprint_le (mem : ByteArray) : memoryFootprint mem ≤ 14 := by
  classical
  unfold memoryFootprint
  split <;> (try split) <;> omega

theorem memoryFootprint_of_zero {mem : ByteArray} (h : MemoryZero mem) : memoryFootprint mem = 0 := by
  classical
  simp [memoryFootprint, h]

theorem memoryFootprint_of_oneWord {mem : ByteArray} (h : MemoryOneWord mem) : memoryFootprint mem ≤ 7 := by
  classical
  unfold memoryFootprint
  rw [if_pos h]
  split <;> omega

theorem memoryFootprint_ge_seven {mem : ByteArray} (h : ¬MemoryZero mem) : 7 ≤ memoryFootprint mem := by
  classical
  unfold memoryFootprint
  rw [if_neg h]
  split <;> omega

theorem memoryFootprint_of_separated {mem : ByteArray} {i j : Nat}
    (hi : i < mem.size) (hj : j < mem.size) (hd : i+32 ≤ j)
    (hni : mem[i] ≠ 0) (hnj : mem[j] ≠ 0) : memoryFootprint mem = 14 := by
  classical
  have hz : ¬MemoryZero mem := fun h => hni (h i hi)
  have hw : ¬MemoryOneWord mem := by
    rintro ⟨start, hs⟩
    have := hs i hi hni
    have := hs j hj hnj
    omega
  simp only [memoryFootprint, if_neg hz, if_neg hw]

theorem MemoryZero.empty : MemoryZero .empty := by
  intro i hi
  exact False.elim (by simpa using hi)

theorem MemoryZero.zeroes (n : Nat) : MemoryZero (.zeroes n) := by
  intro i hi
  change (ByteArray.zeroes n).data[i] = 0
  simp [ByteArray.zeroes]

theorem MemoryZero.append {a b : ByteArray} (ha : MemoryZero a) (hb : MemoryZero b) :
    MemoryZero (a++b) := by
  intro i hi
  by_cases hh : i < a.size
  · rw [ByteArray.getElem_append_left hh]
    exact ha i hh
  · rw [ByteArray.getElem_append_right (by omega)]
    exact hb _ _

theorem MemoryZero.extract {mem : ByteArray} (h : MemoryZero mem) (start stop : Nat) :
    MemoryZero (mem.extract start stop) := by
  intro i hi
  rw [ByteArray.getElem_extract]
  exact h _ _

theorem MemoryZero.oneWord {mem : ByteArray} (h : MemoryZero mem) : MemoryOneWord mem := by
  exact ⟨0, fun i hi hn => False.elim (hn (h i hi))⟩

theorem MemoryOneWord.of_size {mem : ByteArray} (hs : mem.size ≤ 32) : MemoryOneWord mem := by
  exact ⟨0, fun i hi _ => ⟨Nat.zero_le _, by omega⟩⟩

theorem MemoryOneWord.extract {mem : ByteArray} (h : MemoryOneWord mem) (start stop : Nat) :
    MemoryOneWord (mem.extract start stop) := by
  obtain ⟨base, hb⟩ := h
  refine ⟨base-start, ?_⟩
  intro i hi hn
  rw [ByteArray.getElem_extract] at hn
  obtain ⟨hlo, hhi⟩ := hb _ _ hn
  omega

theorem MemoryOneWord.append_zero {a b : ByteArray} (ha : MemoryOneWord a) (hb : MemoryZero b) :
    MemoryOneWord (a++b) := by
  obtain ⟨start, hs⟩ := ha
  refine ⟨start, ?_⟩
  intro i hi hn
  by_cases hh : i < a.size
  · rw [ByteArray.getElem_append_left hh] at hn
    exact hs i hh hn
  · rw [ByteArray.getElem_append_right (by omega)] at hn
    exact False.elim (hn (hb _ _))

theorem MemoryOneWord.zero_append {a b : ByteArray} (ha : MemoryZero a) (hb : MemoryOneWord b) :
    MemoryOneWord (a++b) := by
  obtain ⟨start, hs⟩ := hb
  refine ⟨a.size+start, ?_⟩
  intro i hi hn
  by_cases hh : i < a.size
  · rw [ByteArray.getElem_append_left hh] at hn
    exact False.elim (hn (ha _ _))
  · rw [ByteArray.getElem_append_right (by omega)] at hn
    obtain ⟨hlo, hhi⟩ := hs _ _ hn
    omega

theorem MemoryOneWord.copySlice_zero {src dest : ByteArray} (hd : MemoryZero dest)
    (srcOff destOff len : Nat) (hl : len ≤ 32) :
    MemoryOneWord (src.copySlice srcOff dest destOff len) := by
  have he : src.copySlice srcOff dest destOff len =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff+len) ++
        dest.extract (destOff+min len (src.size-srcOff)) dest.size := by
    apply ByteArray.ext
    simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
    rfl
  rw [he]
  apply MemoryOneWord.append_zero _ (hd.extract _ _)
  apply MemoryOneWord.zero_append (hd.extract _ _)
  apply MemoryOneWord.of_size
  rw [ByteArray.size_extract]
  omega

theorem MemoryZero.readWithPadding {mem : ByteArray} (h : MemoryZero mem) (off len : Nat) :
    MemoryZero (mem.readWithPadding off len) := by
  unfold ByteArray.readWithPadding
  apply MemoryZero.append _ (MemoryZero.zeroes _)
  unfold ByteArray.readWithoutPadding
  split
  · exact MemoryZero.empty
  · exact h.extract _ _

theorem MemoryOneWord.readWithPadding {mem : ByteArray} (h : MemoryOneWord mem) (off len : Nat) :
    MemoryOneWord (mem.readWithPadding off len) := by
  unfold ByteArray.readWithPadding
  apply MemoryOneWord.append_zero _ (MemoryZero.zeroes _)
  unfold ByteArray.readWithoutPadding
  split
  · exact MemoryZero.empty.oneWord
  · exact h.extract _ _

theorem memoryFootprint_readWithPadding (mem : ByteArray) (off len : Nat) :
    memoryFootprint (mem.readWithPadding off len) ≤ memoryFootprint mem := by
  classical
  by_cases hz : MemoryZero mem
  · rw [memoryFootprint_of_zero hz, memoryFootprint_of_zero (hz.readWithPadding off len)]
  · by_cases hw : MemoryOneWord mem
    · exact (memoryFootprint_of_oneWord (hw.readWithPadding off len)).trans (memoryFootprint_ge_seven hz)
    · simpa only [memoryFootprint, if_neg hz, if_neg hw] using memoryFootprint_le (mem.readWithPadding off len)

theorem memoryFootprint_write_short (src mem : ByteArray) (srcOff dest len : Nat) (hl : len ≤ 32) :
    memoryFootprint (src.write srcOff mem dest len) ≤ memoryFootprint mem+7 := by
  classical
  by_cases hz : MemoryZero mem
  · rw [memoryFootprint_of_zero hz]
    apply memoryFootprint_of_oneWord
    unfold ByteArray.write
    split
    · exact hz.oneWord
    · split
      · exact MemoryOneWord.copySlice_zero hz _ _ _ (by omega)
      · apply MemoryOneWord.copySlice_zero (hz.append (MemoryZero.zeroes _))
        omega
  · have := memoryFootprint_ge_seven hz
    have := memoryFootprint_le (src.write srcOff mem dest len)
    omega

end Benchmarks.UniswapV4PoolManager
