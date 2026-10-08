import Benchmarks.EAS.Attester.AttestCellMemory
import Benchmarks.EAS.Attester.AttestHeap

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem attestCellMemory_heap {mem : ByteArray} {free : Nat} {input : UInt256}
    (hfree : 96 ≤ free) (hfit : free + 256 < UInt256.size) :
    AttestCellAt (attestCellMemory mem free input) free (free + 256) free input := by
  refine ⟨le_refl _, by omega, free + 192, by omega, by omega, ?_⟩
  simp only [attestCellMemory, attestCellPayloadMemory, attestCellHeaderMemory,
    writeCascade, Reasoning.Theory.writeWord]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint,
      memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint,
      memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega
  · rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint,
      memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint,
      memLoad_write_disjoint, memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega
  · rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint,
      memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega
  · rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint,
      memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega
  · rw [memLoad_write_disjoint, memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega
  · rw [memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega
  · rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega
  · rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint,
      memLoad_write_disjoint, memLoad_write_same]
    all_goals simp (disch := omega) only [wordWrite_size, ulit_toNat'] <;> omega

theorem attestCellSlotMemory_heap {mem : ByteArray} {free slot : Nat} {input : UInt256}
    (hfree : 96 ≤ free) (hslot : slot + 32 ≤ free) (hfit : free + 256 < UInt256.size) :
    AttestCellAt (attestCellSlotMemory mem free slot input) free (free + 256) free input := by
  apply (attestCellMemory_heap hfree hfit).congr
  intro off hlo hhi
  unfold attestCellSlotMemory Reasoning.Theory.writeWord
  rw [memLoad_write_disjoint]
  · rw [ulit_toNat' _ (by omega), attestCellMemory_size hfree]; omega
  · rw [ulit_toNat' _ (by omega)]; exact .inr (by omega)

theorem attestCellSlotMemory_slot {mem : ByteArray} {free slot : Nat} {input : UInt256}
    (hslot : slot < UInt256.size) :
    memLoad (UInt256.ofNat slot) (attestCellSlotMemory mem free slot input) =
      UInt256.ofNat free :=
  memLoad_write_same _ _ _ _ (ulit_toNat' _ hslot)

theorem attestCellSlotMemory_preserves {mem : ByteArray} {free slot off : Nat} {input : UInt256}
    (hlo : 96 ≤ off) (hin : off + 32 ≤ mem.size) (hfit : off < UInt256.size)
    (hf : off + 32 ≤ free) (hs : off + 32 ≤ slot ∨ slot + 32 ≤ off) :
    memLoad (UInt256.ofNat off) (attestCellSlotMemory mem free slot input) =
      memLoad (UInt256.ofNat off) mem := by
  have hp := attestCellMemory_prefix mem free input
  unfold attestCellSlotMemory Reasoning.Theory.writeWord
  rw [memLoad_write_disjoint _ _ _ _ (by rw [ulit_toNat' _ hfit]; have := hp.size; omega)
    (by rw [ulit_toNat' _ hfit]; exact hs)]
  exact hp.load_preserved hlo hf hin hfit

theorem attestFillMemory_preserves {mem : ByteArray} {free slots i n off : Nat}
    {values : Nat → UInt256} (hfree : 96 ≤ free) (hslots : slots + 32 * (i + n) ≤ free)
    (hlo : 96 ≤ off) (hin : off + 32 ≤ mem.size) (hfit : off < UInt256.size)
    (hf : off + 32 ≤ free)
    (hs : off + 32 ≤ slots + 32 * i ∨ slots + 32 * (i + n) ≤ off) :
    memLoad (UInt256.ofNat off) (attestFillMemory mem free slots values i n) =
      memLoad (UInt256.ofNat off) mem := by
  induction n generalizing mem free i with
  | zero => rfl
  | succ n ih =>
      rw [attestFillMemory]
      have hsize := attestCellSlotMemory_size (mem := mem) (slot := slots + 32 * i)
        (input := values i) hfree (by omega)
      rw [ih (by omega) (by omega) (by rw [hsize]; omega) (by omega) (by omega)]
      exact attestCellSlotMemory_preserves hlo hin hfit hf (by omega)

set_option maxRecDepth 1000 in
theorem attestFillMemory_cells {mem : ByteArray} {free slots i n j : Nat} {values : Nat → UInt256}
    (hfree : 96 ≤ free) (hslots : 96 ≤ slots) (hspan : slots + 32 * (i + n) ≤ free)
    (hfit : free + 256 * n < UInt256.size) (hji : i ≤ j) (hjn : j < i + n) :
    let result := attestFillMemory mem free slots values i n
    ∃ ptr, memLoad (UInt256.ofNat (slots + 32 * j)) result = UInt256.ofNat ptr ∧
      AttestCellAt result free (free + 256 * n) ptr (values j) := by
  dsimp only
  induction n generalizing mem free i with
  | zero => omega
  | succ n ih =>
      rw [attestFillMemory]
      by_cases hij : i = j
      · subst j
        have hsize := attestCellSlotMemory_size (mem := mem) (slot := slots + 32 * i)
          (input := values i) hfree (by omega)
        have hc := attestCellSlotMemory_heap (mem := mem) (free := free)
          (slot := slots + 32 * i) (input := values i) hfree (by omega) (by omega)
        have hc' := hc.congr (mem' := attestFillMemory _ (free + 256) slots values (i + 1) n)
          (by intro off hlo hhi
              exact attestFillMemory_preserves (by omega) (by omega) (by omega)
                (by rw [hsize]; omega) (by omega) hhi (.inr (by omega)))
        refine ⟨free, ?_, hc'.mono (le_refl _) (by omega)⟩
        rw [attestFillMemory_preserves (by omega) (by omega) (by omega)
          (by rw [hsize]; omega) (by omega) (by omega) (.inl (by omega))]
        exact attestCellSlotMemory_slot (by omega)
      · obtain ⟨ptr, hp, hc⟩ := ih (mem := attestCellSlotMemory mem free (slots + 32 * i) (values
          i))
          (free := free + 256) (i := i + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        exact ⟨ptr, hp, hc.mono (by omega) (by omega)⟩

end Benchmarks.EAS.Attester
