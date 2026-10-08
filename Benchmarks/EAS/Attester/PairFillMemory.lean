import Benchmarks.EAS.Attester.PairAllocMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

-- LIBRARY CANDIDATE: filling a pointer array with newly allocated two-word structs.
def pairFillMemory (mem : ByteArray) (free slots : Nat) (values : Nat → UInt256 × UInt256)
    (i : Nat) : Nat → ByteArray
  | 0 => mem
  | n + 1 => pairFillMemory
      (pairSlotMemory mem free (slots + 32 * i) (values i).1 (values i).2)
      (free + 64) slots values (i + 1) n

theorem pairFillMemory_freePtr {mem : ByteArray} {free slots i : Nat}
    {values : Nat → UInt256 × UInt256}
    (hfree : 96 ≤ free) (hslots : 96 ≤ slots)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) (n : Nat) :
    memLoad (UInt256.ofNat 64) (pairFillMemory mem free slots values i n) =
      UInt256.ofNat (free + 64 * n) := by
  induction n generalizing mem free i with
  | zero => simpa only [pairFillMemory, Nat.mul_zero, Nat.add_zero] using hptr
  | succ n ih =>
      rw [pairFillMemory, ih (by omega) (pairSlotMemory_freePtr hfree (by omega))]
      congr 1; omega

theorem pairFillMemory_prefix (mem : ByteArray) (free slots limit i n : Nat)
    (values : Nat → UInt256 × UInt256) (hf : limit ≤ free) (hs : limit ≤ slots) :
    MemoryPrefix mem (pairFillMemory mem free slots values i n) limit := by
  induction n generalizing mem free i with
  | zero => exact .refl _ _
  | succ n ih =>
      exact (pairSlotMemory_prefix _ _ _ _ _ _ hf (by omega)).trans
        (ih _ _ _ (by omega))

theorem pairFillMemory_size {mem : ByteArray} {free slots i n : Nat}
    {values : Nat → UInt256 × UInt256}
    (hfree : 96 ≤ free) (hslots : slots + 32 * (i + n) ≤ free) (hn : 0 < n) :
    (pairFillMemory mem free slots values i n).size = max mem.size (free + 64 * n) := by
  induction n generalizing mem free i with
  | zero => omega
  | succ n ih =>
      rw [pairFillMemory]
      cases n with
      | zero =>
          simp only [pairFillMemory,
            pairSlotMemory_size (slot := slots + 32 * i) hfree (by omega)]
      | succ n =>
          rw [ih (by omega) (by omega) (by omega),
            pairSlotMemory_size (slot := slots + 32 * i) hfree (by omega)]
          omega

theorem pairFillMemory_length {mem : ByteArray} {free base i n len : Nat}
    {values : Nat → UInt256 × UInt256}
    (hbase : 96 ≤ base) (hin : base + 32 ≤ mem.size) (hf : base + 32 ≤ free)
    (hfit : base < UInt256.size)
    (hlen : memLoad (UInt256.ofNat base) mem = UInt256.ofNat len) :
    memLoad (UInt256.ofNat base) (pairFillMemory mem free (base + 32) values i n) =
      UInt256.ofNat len :=
  ((pairFillMemory_prefix _ _ _ (base + 32) _ _ _ hf (le_refl _)).load_preserved
    hbase (le_refl _) hin hfit).trans hlen

end Benchmarks.EAS.Attester
