import Benchmarks.EAS.Attester.WordSequenceMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: allocation of fixed-width structs in a pointer array.
theorem wordSequenceMemory_size_nonempty (mem : ByteArray) (off : Nat)
    (fields : List UInt256) (hne : fields ≠ []) :
    (wordSequenceMemory mem off fields).size = max mem.size (off + 32 * fields.length) := by
  cases fields with
  | nil => contradiction
  | cons field fields =>
      rw [wordSequenceMemory, wordSequenceMemory_size fields
        (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
      simp only [List.length_cons]
      omega

theorem wordSequenceMemory_load_below {mem : ByteArray} {off read : Nat}
    (fields : List UInt256) (hin : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off)
    (hfit : read < UInt256.size) :
    memLoad (UInt256.ofNat read) (wordSequenceMemory mem off fields) =
      memLoad (UInt256.ofNat read) mem := by
  induction fields generalizing mem off with
  | nil => rfl
  | cons field fields ih =>
      rw [wordSequenceMemory, ih (by rw [writeWord_sparse_size]; omega) (by omega)]
      unfold writeWord
      rw [memLoad_write_disjoint]
      · rw [ulit_toNat' _ hfit]; omega
      · rw [ulit_toNat' _ hfit]; exact .inl hbelow

def structSlotMemory (mem : ByteArray) (free slot : Nat) (fields : List UInt256) : ByteArray :=
  writeWord (wordSequenceMemory
    (writeWord mem 64 (UInt256.ofNat (free + 32 * fields.length))) free fields)
    slot (UInt256.ofNat free)

theorem structSlotMemory_freePtr {mem : ByteArray} {free slot : Nat} {fields : List UInt256}
    (hfree : 96 ≤ free) (hslot : 96 ≤ slot) :
    memLoad (UInt256.ofNat 64) (structSlotMemory mem free slot fields) =
      UInt256.ofNat (free + 32 * fields.length) := by
  have hin : 64 + 32 ≤ (writeWord mem 64
      (UInt256.ofNat (free + 32 * fields.length))).size := by
    rw [writeWord_sparse_size]; omega
  have hp := wordSequenceMemory_prefix
    (writeWord mem 64 (UInt256.ofNat (free + 32 * fields.length))) free fields
  unfold structSlotMemory
  unfold writeWord
  rw [memLoad_write_disjoint]
  · exact (wordSequenceMemory_load_below fields hin hfree (by decide)).trans
      (memLoad_write_same _ _ _ _ rfl)
  · change 64 + 32 ≤ _
    exact le_trans hin hp.size
  · change 64 + 32 ≤ slot ∨ _
    exact .inl hslot

theorem structSlotMemory_size {mem : ByteArray} {free slot : Nat} {fields : List UInt256}
    (hfree : 96 ≤ free) (hslot : slot + 32 ≤ free + 32 * fields.length)
    (hne : fields ≠ []) :
    (structSlotMemory mem free slot fields).size =
      max mem.size (free + 32 * fields.length) := by
  rw [structSlotMemory, writeWord_sparse_size, wordSequenceMemory_size_nonempty _ _ _ hne,
    writeWord_sparse_size]
  omega

theorem structSlotMemory_prefix (mem : ByteArray) (free slot limit : Nat)
    (fields : List UInt256) (hf : limit ≤ free) (hs : limit ≤ slot) :
    MemoryPrefix mem (structSlotMemory mem free slot fields) limit :=
  (memoryPrefix_sparse_writeWord mem 64 limit _ (.inr (by decide))).trans
    (((wordSequenceMemory_prefix _ free fields).mono hf).trans
      (memoryPrefix_sparse_writeWord _ slot limit _ (.inl hs)))

def structSlotsMemory : ByteArray → Nat → Nat → List UInt256 → Nat → ByteArray
  | mem, _, _, _, 0 => mem
  | mem, free, slot, fields, n + 1 =>
      structSlotsMemory (structSlotMemory mem free slot fields)
        (free + 32 * fields.length) (slot + 32) fields n

theorem structSlotsMemory_freePtr {mem : ByteArray} {free slot : Nat} {fields : List UInt256}
    (hfree : 96 ≤ free) (hslot : 96 ≤ slot)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) (n : Nat) :
    memLoad (UInt256.ofNat 64) (structSlotsMemory mem free slot fields n) =
      UInt256.ofNat (free + 32 * fields.length * n) := by
  induction n generalizing mem free slot with
  | zero => simpa only [structSlotsMemory, Nat.mul_zero, Nat.add_zero] using hptr
  | succ n ih =>
      rw [structSlotsMemory, ih (by omega) (by omega) (structSlotMemory_freePtr hfree hslot)]
      congr 1
      simp only [Nat.mul_succ, Nat.add_assoc]
      omega

theorem structSlotsMemory_size {mem : ByteArray} {free slot : Nat} {fields : List UInt256}
    (hfree : 96 ≤ free) (hslot : slot ≤ free) (hne : fields ≠ []) (n : Nat) (hn : 0 < n) :
    (structSlotsMemory mem free slot fields n).size =
      max mem.size (free + 32 * fields.length * n) := by
  have hlen : 0 < fields.length := by cases fields <;> simp_all
  induction n generalizing mem free slot with
  | zero => omega
  | succ n ih =>
      rw [structSlotsMemory]
      cases n with
      | zero =>
          simpa only [structSlotsMemory, Nat.zero_add, Nat.mul_one] using
            structSlotMemory_size (mem := mem) (slot := slot) hfree (by omega) hne
      | succ n =>
          rw [ih (by omega) (by omega) (by omega),
            structSlotMemory_size (slot := slot) hfree (by omega) hne]
          simp only [Nat.mul_succ]
          omega

theorem structSlotsMemory_prefix (mem : ByteArray) (free slot limit : Nat)
    (fields : List UInt256) (hf : limit ≤ free) (hs : limit ≤ slot) (n : Nat) :
    MemoryPrefix mem (structSlotsMemory mem free slot fields n) limit := by
  induction n generalizing mem free slot with
  | zero => exact .refl _ _
  | succ n ih =>
      exact (structSlotMemory_prefix mem free slot limit fields hf hs).trans
        (ih _ _ _ (by omega) (by omega))

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

def structArrayMemory (mem : ByteArray) (free n : Nat) (fields : List UInt256) : ByteArray :=
  structSlotsMemory (arrayHeaderMemory mem free n) (free + 32 + 32 * n) (free + 32) fields n

theorem structArrayMemory_freePtr {mem : ByteArray} {free n : Nat} {fields : List UInt256}
    (hfree : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (structArrayMemory mem free n fields) =
      UInt256.ofNat (free + 32 + (32 + 32 * fields.length) * n) := by
  rw [structArrayMemory, structSlotsMemory_freePtr (by omega) (by omega)
    (arrayHeaderMemory_freePtr _ _ _)]
  congr 1
  ring

theorem structArrayMemory_size {mem : ByteArray} {free n : Nat} {fields : List UInt256}
    (hfree : 96 ≤ free) (hne : fields ≠ []) :
    (structArrayMemory mem free n fields).size =
      max mem.size (free + 32 + (32 + 32 * fields.length) * n) := by
  cases n with
  | zero => simpa only [structArrayMemory, structSlotsMemory, Nat.mul_zero, Nat.add_zero] using
      (arrayHeaderMemory_size (n := 0) hfree)
  | succ n =>
      rw [structArrayMemory, structSlotsMemory_size (by omega) (by omega) hne _ (by omega),
        arrayHeaderMemory_size hfree]
      simp only [Nat.add_mul]
      omega

theorem structArrayMemory_prefix (mem : ByteArray) (free n : Nat) (fields : List UInt256) :
    MemoryPrefix mem (structArrayMemory mem free n fields) free :=
  (arrayHeaderMemory_prefix mem free n).trans
    (structSlotsMemory_prefix _ _ _ free fields (by omega) (by omega) n)

theorem structArrayMemory_length {mem : ByteArray} {free n : Nat} {fields : List UInt256}
    (hfree : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (structArrayMemory mem free n fields) = UInt256.ofNat n := by
  exact ((structSlotsMemory_prefix (arrayHeaderMemory mem free n)
    (free + 32 + 32 * n) (free + 32) (free + 32) fields (by omega) (le_refl _) n).load_preserved
    hfree (le_refl _) (by rw [arrayHeaderMemory_size hfree]; omega) hfit).trans
    (arrayHeaderMemory_length hfree hfit)

end Benchmarks.EAS.Attester
