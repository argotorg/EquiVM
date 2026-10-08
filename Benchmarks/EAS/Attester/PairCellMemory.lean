import Benchmarks.EAS.Attester.PairFillMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem pairSlotMemory_preserves {mem : ByteArray} {free slot off : Nat} {first second : UInt256}
    (hlo : 96 ≤ off) (hin : off + 32 ≤ mem.size) (hfit : off < UInt256.size)
    (hf : off + 32 ≤ free) (hs : off + 32 ≤ slot ∨ slot + 32 ≤ off) :
    memLoad (UInt256.ofNat off) (pairSlotMemory mem free slot first second) =
      memLoad (UInt256.ofNat off) mem := by
  have hp := pairStructMemory_prefix mem free first second
  change memLoad (UInt256.ofNat off)
    ((UInt256.ofNat free).toByteArray.write 0 (pairStructMemory mem free first second) slot 32) = _
  rw [memLoad_write_disjoint _ _ _ _ (by rw [ulit_toNat' _ hfit]; have := hp.size; omega)
    (by rw [ulit_toNat' _ hfit]; exact hs)]
  exact hp.load_preserved hlo hf hin hfit

theorem pairSlotMemory_first {mem : ByteArray} {free slot : Nat} {first second : UInt256}
    (hslot : slot + 32 ≤ free) (hfit : free + 32 < UInt256.size) :
    memLoad (UInt256.ofNat free) (pairSlotMemory mem free slot first second) = first := by
  have hf : free < UInt256.size := by omega
  simp only [pairSlotMemory, writeCascade, Reasoning.Theory.writeWord]
  rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_same]
  all_goals simp only [ulit_toNat' _ hf, wordWrite_size] <;> omega

theorem pairSlotMemory_second {mem : ByteArray} {free slot : Nat} {first second : UInt256}
    (hslot : slot + 32 ≤ free) (hfit : free + 32 < UInt256.size) :
    memLoad (UInt256.ofNat (free + 32)) (pairSlotMemory mem free slot first second) = second := by
  simp only [pairSlotMemory, writeCascade, Reasoning.Theory.writeWord]
  rw [memLoad_write_disjoint, memLoad_write_same]
  all_goals simp only [ulit_toNat' _ hfit, wordWrite_size] <;> omega

theorem pairFillMemory_preserves {mem : ByteArray} {free slots i n off : Nat}
    {values : Nat → UInt256 × UInt256}
    (hfree : 96 ≤ free) (hslots : slots + 32 * (i + n) ≤ free)
    (hlo : 96 ≤ off) (hin : off + 32 ≤ mem.size) (hfit : off < UInt256.size)
    (hf : off + 32 ≤ free)
    (hs : off + 32 ≤ slots + 32 * i ∨ slots + 32 * (i + n) ≤ off) :
    memLoad (UInt256.ofNat off) (pairFillMemory mem free slots values i n) =
      memLoad (UInt256.ofNat off) mem := by
  induction n generalizing mem free i with
  | zero => rfl
  | succ n ih =>
      rw [pairFillMemory]
      have hsize := pairSlotMemory_size (mem := mem) (slot := slots + 32 * i)
        (first := (values i).1) (second := (values i).2) hfree (by omega)
      rw [ih (by omega) (by omega) (by rw [hsize]; omega) (by omega) (by omega)]
      exact pairSlotMemory_preserves hlo hin hfit hf (by omega)

theorem pairFillMemory_cells {mem : ByteArray} {free slots i n j : Nat}
    {values : Nat → UInt256 × UInt256}
    (hfree : 96 ≤ free) (hslots : 96 ≤ slots) (hspan : slots + 32 * (i + n) ≤ free)
    (hfit : free + 64 * n < UInt256.size) (hji : i ≤ j) (hjn : j < i + n) :
    let result := pairFillMemory mem free slots values i n
    let ptr := free + 64 * (j - i)
    memLoad (UInt256.ofNat (slots + 32 * j)) result = UInt256.ofNat ptr ∧
      memLoad (UInt256.ofNat ptr) result = (values j).1 ∧
      memLoad (UInt256.ofNat (ptr + 32)) result = (values j).2 := by
  dsimp only
  induction n generalizing mem free i with
  | zero => omega
  | succ n ih =>
      rw [pairFillMemory]
      by_cases hij : i = j
      · subst j
        simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
        have hsize := pairSlotMemory_size (mem := mem) (slot := slots + 32 * i)
          (first := (values i).1) (second := (values i).2) hfree (by omega)
        have hslot := pairFillMemory_preserves
          (mem := pairSlotMemory mem free (slots + 32 * i) (values i).1 (values i).2)
          (free := free + 64) (slots := slots) (i := i + 1) (n := n) (off := slots + 32 * i)
          (values := values) (by omega) (by omega) (by omega) (by rw [hsize]; omega)
          (by omega) (by omega) (.inl (by omega))
        have hfirst := pairFillMemory_preserves
          (mem := pairSlotMemory mem free (slots + 32 * i) (values i).1 (values i).2)
          (free := free + 64) (slots := slots) (i := i + 1) (n := n) (off := free)
          (values := values) (by omega) (by omega) hfree (by rw [hsize]; omega)
          (by omega) (by omega) (.inr (by omega))
        have hsecond := pairFillMemory_preserves
          (mem := pairSlotMemory mem free (slots + 32 * i) (values i).1 (values i).2)
          (free := free + 64) (slots := slots) (i := i + 1) (n := n) (off := free + 32)
          (values := values) (by omega) (by omega) (by omega) (by rw [hsize]; omega)
          (by omega) (by omega) (.inr (by omega))
        rw [hslot, hfirst, hsecond, pairSlotMemory_slot (by omega),
          pairSlotMemory_first (by omega) (by omega), pairSlotMemory_second (by omega) (by omega)]
        exact ⟨rfl, rfl, rfl⟩
      · have hh := ih (mem := pairSlotMemory mem free (slots + 32 * i) (values i).1 (values i).2)
          (free := free + 64) (i := i + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        simpa only [show free + 64 + 64 * (j - (i + 1)) = free + 64 * (j - i) by omega] using hh

end Benchmarks.EAS.Attester
