import Benchmarks.EAS.Attester.PairFillMemory
import Benchmarks.EAS.Attester.NestedDecodeTrace
import Benchmarks.EAS.Attester.ArrayBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def revokeDataMemory (mem cd : ByteArray) (free cdptr n : Nat) : ByteArray :=
  pairFillMemory (pairArrayMemory mem free n ⟨0⟩) (free + 32 + 96 * n) (free + 32)
    (fun j ↦ (calldataWord cd (cdptr + 32 * j), ⟨0⟩)) 0 n

theorem revokeDataMemory_freePtr {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (revokeDataMemory mem cd free cdptr n) =
      UInt256.ofNat (free + 32 + 160 * n) := by
  rw [revokeDataMemory, pairFillMemory_freePtr (by omega) (by omega)
    (pairArrayMemory_freePtr hfree)]
  congr 1; omega

theorem revokeDataMemory_size {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) (hn : 0 < n) :
    (revokeDataMemory mem cd free cdptr n).size = max mem.size (free + 32 + 160 * n) := by
  rw [revokeDataMemory, pairFillMemory_size (by omega) (by omega) hn,
    pairArrayMemory_size hfree]
  omega

theorem revokeDataMemory_prefix (mem cd : ByteArray) (free cdptr n : Nat) :
    MemoryPrefix mem (revokeDataMemory mem cd free cdptr n) free :=
  (pairArrayMemory_prefix _ _ _ _).trans
    (pairFillMemory_prefix _ _ _ _ _ _ _ (by omega) (by omega))

theorem revokeDataMemory_length {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (revokeDataMemory mem cd free cdptr n) = UInt256.ofNat n := by
  apply pairFillMemory_length hfree
    (by rw [pairArrayMemory_size hfree]; omega) (by omega) hfit
  exact pairArrayMemory_length hfree hfit

def multiRevokeRowMemory (mem cd : ByteArray) (free base i schemaPtr uidPtr n : Nat) : ByteArray :=
  pairSlotMemory (revokeDataMemory mem cd free uidPtr n) (free + 32 + 160 * n)
    (base + 32 + 32 * i) (calldataWord cd (schemaPtr + 32 * i)) (UInt256.ofNat free)

theorem multiRevokeRowMemory_freePtr {mem cd : ByteArray}
    {free base i schemaPtr uidPtr n : Nat} (hfree : 96 ≤ free) (hbase : 96 ≤ base) :
    memLoad (UInt256.ofNat 64) (multiRevokeRowMemory mem cd free base i schemaPtr uidPtr n) =
      UInt256.ofNat (free + 96 + 160 * n) := by
  rw [multiRevokeRowMemory, pairSlotMemory_freePtr (by omega) (by omega)]
  congr 1; omega

theorem multiRevokeRowMemory_size {mem cd : ByteArray}
    {free base i schemaPtr uidPtr n : Nat} (hfree : 96 ≤ free)
    (hslot : base + 64 + 32 * i ≤ free) (hn : 0 < n) :
    (multiRevokeRowMemory mem cd free base i schemaPtr uidPtr n).size =
      max mem.size (free + 96 + 160 * n) := by
  rw [multiRevokeRowMemory, pairSlotMemory_size (by omega) (by omega),
    revokeDataMemory_size hfree hn]
  omega

theorem multiRevokeRowMemory_prefix (mem cd : ByteArray)
    (free base i schemaPtr uidPtr n : Nat) (hfree : base + 32 ≤ free) :
    MemoryPrefix mem (multiRevokeRowMemory mem cd free base i schemaPtr uidPtr n) (base + 32) :=
  ((revokeDataMemory_prefix _ _ _ _ _).mono hfree).trans
    (pairSlotMemory_prefix _ _ _ _ _ _ (by omega) (by omega))

def multiRevokeRowsMemory (mem cd : ByteArray) (free base schemaPtr : Nat)
    (secondData : UInt256) (i : Nat) : Nat → ByteArray
  | 0 => mem
  | remaining + 1 =>
      multiRevokeRowsMemory
        (multiRevokeRowMemory mem cd free base i schemaPtr
          (rowData cd secondData i).toNat (rowLength cd secondData i).toNat)
        cd (free + 96 + 160 * (rowLength cd secondData i).toNat)
        base schemaPtr secondData (i + 1) remaining

def multiRevokeRowsEnd (cd : ByteArray) (free : Nat) (secondData : UInt256) (i : Nat) : Nat → Nat
  | 0 => free
  | remaining + 1 => multiRevokeRowsEnd cd
      (free + 96 + 160 * (rowLength cd secondData i).toNat) secondData (i + 1) remaining

theorem multiRevokeRowsMemory_freePtr {mem cd : ByteArray}
    {free base schemaPtr i remaining : Nat} {secondData : UInt256}
    (hfree : 96 ≤ free) (hbase : 96 ≤ base)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) :
    memLoad (UInt256.ofNat 64)
      (multiRevokeRowsMemory mem cd free base schemaPtr secondData i remaining) =
        UInt256.ofNat (multiRevokeRowsEnd cd free secondData i remaining) := by
  induction remaining generalizing mem free i with
  | zero => exact hptr
  | succ remaining ih =>
      rw [multiRevokeRowsMemory, multiRevokeRowsEnd]
      apply ih (by omega)
      exact multiRevokeRowMemory_freePtr hfree hbase

theorem multiRevokeRowsMemory_prefix (mem cd : ByteArray)
    (free base schemaPtr i remaining : Nat) (secondData : UInt256) (hfree : base + 32 ≤ free) :
    MemoryPrefix mem (multiRevokeRowsMemory mem cd free base schemaPtr secondData i remaining)
      (base + 32) := by
  induction remaining generalizing mem free i with
  | zero => exact .refl _ _
  | succ remaining ih =>
      rw [multiRevokeRowsMemory]
      exact (multiRevokeRowMemory_prefix _ _ _ _ _ _ _ _ hfree).trans
        (ih _ _ _ (by omega))

def multiRevokeBuiltMemory (cd : ByteArray) : ByteArray :=
  multiRevokeRowsMemory (pairArrayMemory solcFreePtrMem 128 (arrayCount cd 4) ⟨96⟩)
    cd (160 + 96 * arrayCount cd 4) 128 (arrayDataNat cd 4)
    (UInt256.ofNat (arrayDataNat cd 36)) 0 (arrayCount cd 4)

def multiRevokeBuiltFree (cd : ByteArray) : Nat :=
  multiRevokeRowsEnd cd (160 + 96 * arrayCount cd 4)
    (UInt256.ofNat (arrayDataNat cd 36)) 0 (arrayCount cd 4)

theorem multiRevokeBuiltMemory_freePtr (cd : ByteArray) :
    memLoad (UInt256.ofNat 64) (multiRevokeBuiltMemory cd) = UInt256.ofNat (multiRevokeBuiltFree cd)
        :=
  multiRevokeRowsMemory_freePtr (by omega) (by decide) (pairArrayMemory_freePtr (by decide))

end Benchmarks.EAS.Attester
