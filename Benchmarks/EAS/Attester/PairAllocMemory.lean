import Benchmarks.EAS.Attester.Memory
import Benchmarks.EAS.Attester.WordHelpers
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: transport MLOAD through preservation of an allocated prefix.
theorem MemoryPrefix.load_preserved {before after : ByteArray} {limit off : Nat}
    (h : MemoryPrefix before after limit) (hlo : 96 ≤ off) (hhi : off + 32 ≤ limit)
    (hin : off + 32 ≤ before.size) (hfit : off < UInt256.size) :
    memLoad (UInt256.ofNat off) after = memLoad (UInt256.ofNat off) before := by
  unfold memLoad
  rw [ulit_toNat' _ hfit, if_neg (by have := h.size; omega), if_neg (by omega),
      h.read off hlo hhi hin]

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

def pairStructMemory (mem : ByteArray) (free : Nat) (first second : UInt256) : ByteArray :=
  writeCascade mem [(64, UInt256.ofNat (free + 64)), (free, first), (free + 32, second)]

theorem pairStructMemory_prefix (mem : ByteArray) (free : Nat) (first second : UInt256) :
    MemoryPrefix mem (pairStructMemory mem free first second) free :=
  (memoryPrefix_sparse_writeWord mem 64 free _ (.inr (by decide))).trans
    ((memoryPrefix_sparse_writeWord _ free free first (.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ (free + 32) free second (.inl (by omega))))

/-- Allocate a two-word struct and write its pointer to an array slot. -/
def pairSlotMemory (mem : ByteArray) (free slot : Nat) (first second : UInt256) : ByteArray :=
  writeCascade mem [(64, UInt256.ofNat (free + 64)), (free, first),
    (free + 32, second), (slot, UInt256.ofNat free)]

theorem pairSlotMemory_size {mem : ByteArray} {free slot : Nat} {first second : UInt256}
    (hlo : 96 ≤ free) (hslot : slot + 32 ≤ free + 64) :
    (pairSlotMemory mem free slot first second).size = max mem.size (free + 64) := by
  simp only [pairSlotMemory, writeCascade, Reasoning.Theory.writeWord, wordWrite_size]
  omega

theorem pairSlotMemory_freePtr {mem : ByteArray} {free slot : Nat} {first second : UInt256}
    (hfree : 96 ≤ free) (hslot : 96 ≤ slot) :
    memLoad (UInt256.ofNat 64) (pairSlotMemory mem free slot first second) = UInt256.ofNat (free +
        64) := by
  simp only [pairSlotMemory, writeCascade, Reasoning.Theory.writeWord]
  rw [memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_disjoint, memLoad_write_same]
  all_goals simp only [wordWrite_size, show (UInt256.ofNat 64).toNat = 64 from rfl] <;> omega

theorem pairSlotMemory_slot {mem : ByteArray} {free slot : Nat} {first second : UInt256}
    (hslot : slot < UInt256.size) :
    memLoad (UInt256.ofNat slot) (pairSlotMemory mem free slot first second) = UInt256.ofNat free :=
        by
  exact memLoad_write_same _ _ _ _ (ulit_toNat' _ hslot)

theorem pairSlotMemory_prefix (mem : ByteArray) (free slot limit : Nat) (first second : UInt256)
    (hf : limit ≤ free) (hs : limit ≤ slot) :
    MemoryPrefix mem (pairSlotMemory mem free slot first second) limit := by
  unfold pairSlotMemory
  simp only [writeCascade_cons, writeCascade_nil]
  exact (memoryPrefix_sparse_writeWord mem 64 limit (UInt256.ofNat (free + 64)) (.inr (by
      decide))).trans
    ((memoryPrefix_sparse_writeWord _ free limit first (.inl hf)).trans
      ((memoryPrefix_sparse_writeWord _ (free + 32) limit second (.inl (by omega))).trans
        (memoryPrefix_sparse_writeWord _ slot limit (UInt256.ofNat free) (.inl hs))))

def pairSlotsMemory : ByteArray → Nat → Nat → UInt256 → Nat → ByteArray
  | mem, _, _, _, 0 => mem
  | mem, free, slot, second, n + 1 =>
      pairSlotsMemory (pairSlotMemory mem free slot ⟨0⟩ second) (free + 64) (slot + 32) second n

theorem pairSlotsMemory_freePtr {mem : ByteArray} {free slot : Nat} {second : UInt256}
    (hfree : 96 ≤ free) (hslot : 96 ≤ slot)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) (n : Nat) :
    memLoad (UInt256.ofNat 64) (pairSlotsMemory mem free slot second n) = UInt256.ofNat (free + 64 *
        n) := by
  induction n generalizing mem free slot with
  | zero => simpa only [pairSlotsMemory, Nat.mul_zero, Nat.add_zero] using hptr
  | succ n ih =>
      rw [pairSlotsMemory, ih (by omega) (by omega) (pairSlotMemory_freePtr hfree hslot)]
      congr 1; omega

theorem pairSlotsMemory_size {mem : ByteArray} {free slot : Nat} {second : UInt256}
    (hfree : 96 ≤ free) (hslot : slot + 32 ≤ free + 64) (n : Nat) (hn : 0 < n) :
    (pairSlotsMemory mem free slot second n).size = max mem.size (free + 64 * n) := by
  induction n generalizing mem free slot with
  | zero => omega
  | succ n ih =>
      rw [pairSlotsMemory]
      cases n with
      | zero => simp only [pairSlotsMemory, pairSlotMemory_size hfree hslot]
      | succ n =>
          rw [ih (by omega) (by omega) (by omega), pairSlotMemory_size hfree hslot]
          omega

theorem pairSlotsMemory_prefix (mem : ByteArray) (free slot limit : Nat) (second : UInt256)
    (hf : limit ≤ free) (hs : limit ≤ slot) (n : Nat) :
    MemoryPrefix mem (pairSlotsMemory mem free slot second n) limit := by
  induction n generalizing mem free slot with
  | zero => exact .refl _ _
  | succ n ih =>
      exact (pairSlotMemory_prefix mem free slot limit ⟨0⟩ second hf hs).trans
        (ih _ _ _ (by omega) (by omega))

def arrayHeaderMemory (mem : ByteArray) (free n : Nat) : ByteArray :=
  writeCascade mem [(free, UInt256.ofNat n), (64, UInt256.ofNat (free + 32 + 32 * n))]

theorem arrayHeaderMemory_size {mem : ByteArray} {free n : Nat} (hfree : 96 ≤ free) :
    (arrayHeaderMemory mem free n).size = max mem.size (free + 32) := by
  simp only [arrayHeaderMemory, writeCascade, Reasoning.Theory.writeWord, wordWrite_size]
  omega

theorem arrayHeaderMemory_freePtr (mem : ByteArray) (free n : Nat) :
    memLoad (UInt256.ofNat 64) (arrayHeaderMemory mem free n) = UInt256.ofNat (free + 32 + 32 * n)
        :=
  memLoad_write_same _ _ _ _ rfl

theorem arrayHeaderMemory_length {mem : ByteArray} {free n : Nat}
    (hfree : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (arrayHeaderMemory mem free n) = UInt256.ofNat n := by
  simp only [arrayHeaderMemory, writeCascade, Reasoning.Theory.writeWord]
  rw [memLoad_write_disjoint, memLoad_write_same]
  · exact ulit_toNat' _ hfit
  · rw [wordWrite_size, ulit_toNat' _ hfit]; omega
  · rw [ulit_toNat' _ hfit]; exact .inr hfree

theorem arrayHeaderMemory_prefix (mem : ByteArray) (free n : Nat) :
    MemoryPrefix mem (arrayHeaderMemory mem free n) free :=
  (memoryPrefix_sparse_writeWord mem free free (UInt256.ofNat n) (.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ 64 free _ (.inr (by decide)))

def pairArrayMemory (mem : ByteArray) (free n : Nat) (second : UInt256) : ByteArray :=
  pairSlotsMemory (arrayHeaderMemory mem free n) (free + 32 + 32 * n) (free + 32) second n

theorem pairArrayMemory_freePtr {mem : ByteArray} {free n : Nat} {second : UInt256}
    (hfree : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (pairArrayMemory mem free n second) = UInt256.ofNat (free + 32 + 96 *
        n) := by
  rw [pairArrayMemory, pairSlotsMemory_freePtr (by omega) (by omega) (arrayHeaderMemory_freePtr _ _
      _)]
  congr 1; omega

theorem pairArrayMemory_size {mem : ByteArray} {free n : Nat} {second : UInt256}
    (hfree : 96 ≤ free) :
    (pairArrayMemory mem free n second).size = max mem.size (free + 32 + 96 * n) := by
  cases n with
  | zero => simpa only [pairArrayMemory, pairSlotsMemory, Nat.mul_zero, Nat.add_zero] using
      (arrayHeaderMemory_size (n := 0) hfree)
  | succ n =>
      rw [pairArrayMemory, pairSlotsMemory_size (by omega) (by omega) _ (by omega),
        arrayHeaderMemory_size hfree]
      omega

theorem pairArrayMemory_prefix (mem : ByteArray) (free n : Nat) (second : UInt256) :
    MemoryPrefix mem (pairArrayMemory mem free n second) free :=
  (arrayHeaderMemory_prefix mem free n).trans
    (pairSlotsMemory_prefix _ _ _ free second (by omega) (by omega) n)

theorem pairArrayMemory_length {mem : ByteArray} {free n : Nat} {second : UInt256}
    (hfree : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (pairArrayMemory mem free n second) = UInt256.ofNat n := by
  have hp := pairSlotsMemory_prefix (arrayHeaderMemory mem free n)
    (free + 32 + 32 * n) (free + 32) (free + 32) second (by omega) (by omega) n
  have hb : free + 32 ≤ (arrayHeaderMemory mem free n).size := by
    rw [arrayHeaderMemory_size hfree]
    omega
  have hr := hp.read free hfree (le_refl _) hb
  have hw := readWord_of_memLoad _ _ _ hb hfit (arrayHeaderMemory_length hfree hfit)
  apply mloadWordValue_of_readWithPadding
  · rw [ulit_toNat' _ hfit]
    have := le_trans hb hp.size
    change free < (pairSlotsMemory (arrayHeaderMemory mem free n) (free + 32 + 32 * n) (free + 32)
        second n).size
    omega
  · simpa only [ulit_toNat' _ hfit] using hr.trans hw

end Benchmarks.EAS.Attester
