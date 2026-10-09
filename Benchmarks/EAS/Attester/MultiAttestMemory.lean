import Benchmarks.EAS.Attester.AttestCellMemory
import Benchmarks.EAS.Attester.StructInitTrace
import Benchmarks.EAS.Attester.NestedDecodeTrace
import Benchmarks.EAS.Attester.ArrayBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestDataMemory (mem cd : ByteArray) (free cdptr n : Nat) : ByteArray :=
  attestFillMemory (structArrayMemory mem free n attestDefaultFields) (free + 32 + 224 * n) (free +
      32)
    (fun j ↦ calldataWord cd (cdptr + 32 * j)) 0 n

theorem attestDataMemory_freePtr {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (attestDataMemory mem cd free cdptr n) =
      UInt256.ofNat (free + 32 + 480 * n) := by
  have hptr : memLoad (UInt256.ofNat 64) (structArrayMemory mem free n attestDefaultFields) =
      UInt256.ofNat (free + 32 + 224 * n) := structArrayMemory_freePtr hfree
  rw [attestDataMemory, attestFillMemory_freePtr (by omega) (by omega) hptr]
  congr 1; omega

theorem attestDataMemory_size {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) (hn : 0 < n) :
    (attestDataMemory mem cd free cdptr n).size = max mem.size (free + 32 + 480 * n) := by
  rw [attestDataMemory, attestFillMemory_size (by omega) (by omega) hn,
    structArrayMemory_size hfree (by decide : attestDefaultFields ≠ [])]
  change max (max mem.size (free + 32 + 224 * n)) (free + 32 + 224 * n + 256 * n) = _
  omega

theorem attestDataMemory_prefix (mem cd : ByteArray) (free cdptr n : Nat) :
    MemoryPrefix mem (attestDataMemory mem cd free cdptr n) free :=
  (structArrayMemory_prefix _ _ _ _).trans
    (attestFillMemory_prefix _ _ _ _ _ _ _ (by omega) (by omega))

theorem attestDataMemory_length {mem cd : ByteArray} {free cdptr n : Nat}
    (hfree : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (attestDataMemory mem cd free cdptr n) = UInt256.ofNat n := by
  apply attestFillMemory_length hfree
    (by rw [structArrayMemory_size hfree (by decide : attestDefaultFields ≠ [])]; omega) (by omega)
        hfit
  exact structArrayMemory_length hfree hfit

def multiAttestRowMemory (mem cd : ByteArray) (free base i schemaPtr uidPtr n : Nat) : ByteArray :=
  pairSlotMemory (attestDataMemory mem cd free uidPtr n) (free + 32 + 480 * n)
    (base + 32 + 32 * i) (calldataWord cd (schemaPtr + 32 * i)) (UInt256.ofNat free)

theorem multiAttestRowMemory_freePtr {mem cd : ByteArray}
    {free base i schemaPtr uidPtr n : Nat} (hfree : 96 ≤ free) (hbase : 96 ≤ base) :
    memLoad (UInt256.ofNat 64) (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n) =
      UInt256.ofNat (free + 96 + 480 * n) := by
  rw [multiAttestRowMemory, pairSlotMemory_freePtr (by omega) (by omega)]
  congr 1; omega

theorem multiAttestRowMemory_size {mem cd : ByteArray}
    {free base i schemaPtr uidPtr n : Nat} (hfree : 96 ≤ free)
    (hslot : base + 64 + 32 * i ≤ free) (hn : 0 < n) :
    (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n).size =
      max mem.size (free + 96 + 480 * n) := by
  rw [multiAttestRowMemory, pairSlotMemory_size (by omega) (by omega),
    attestDataMemory_size hfree hn]
  omega

theorem multiAttestRowMemory_prefix (mem cd : ByteArray)
    (free base i schemaPtr uidPtr n : Nat) (hfree : base + 32 ≤ free) :
    MemoryPrefix mem (multiAttestRowMemory mem cd free base i schemaPtr uidPtr n) (base + 32) :=
  ((attestDataMemory_prefix _ _ _ _ _).mono hfree).trans
    (pairSlotMemory_prefix _ _ _ _ _ _ (by omega) (by omega))

def multiAttestRowsMemory (mem cd : ByteArray) (free base schemaPtr : Nat)
    (secondData : UInt256) (i : Nat) : Nat → ByteArray
  | 0 => mem
  | remaining + 1 =>
      multiAttestRowsMemory
        (multiAttestRowMemory mem cd free base i schemaPtr
          (rowData cd secondData i).toNat (rowLength cd secondData i).toNat)
        cd (free + 96 + 480 * (rowLength cd secondData i).toNat)
        base schemaPtr secondData (i + 1) remaining

def multiAttestRowsEnd (cd : ByteArray) (free : Nat) (secondData : UInt256) (i : Nat) : Nat → Nat
  | 0 => free
  | remaining + 1 => multiAttestRowsEnd cd
      (free + 96 + 480 * (rowLength cd secondData i).toNat) secondData (i + 1) remaining

theorem multiAttestRowsMemory_freePtr {mem cd : ByteArray}
    {free base schemaPtr i remaining : Nat} {secondData : UInt256}
    (hfree : 96 ≤ free) (hbase : 96 ≤ base)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free) :
    memLoad (UInt256.ofNat 64)
      (multiAttestRowsMemory mem cd free base schemaPtr secondData i remaining) =
        UInt256.ofNat (multiAttestRowsEnd cd free secondData i remaining) := by
  induction remaining generalizing mem free i with
  | zero => exact hptr
  | succ remaining ih =>
      rw [multiAttestRowsMemory, multiAttestRowsEnd]
      apply ih (by omega)
      exact multiAttestRowMemory_freePtr hfree hbase

theorem multiAttestRowsMemory_prefix (mem cd : ByteArray)
    (free base schemaPtr i remaining : Nat) (secondData : UInt256) (hfree : base + 32 ≤ free) :
    MemoryPrefix mem (multiAttestRowsMemory mem cd free base schemaPtr secondData i remaining)
      (base + 32) := by
  induction remaining generalizing mem free i with
  | zero => exact .refl _ _
  | succ remaining ih =>
      rw [multiAttestRowsMemory]
      exact (multiAttestRowMemory_prefix _ _ _ _ _ _ _ _ hfree).trans
        (ih _ _ _ (by omega))

def multiAttestBuiltMemory (cd : ByteArray) : ByteArray :=
  multiAttestRowsMemory (pairArrayMemory solcFreePtrMem 128 (arrayCount cd 4) ⟨96⟩)
    cd (160 + 96 * arrayCount cd 4) 128 (arrayDataNat cd 4)
    (UInt256.ofNat (arrayDataNat cd 36)) 0 (arrayCount cd 4)

def multiAttestBuiltFree (cd : ByteArray) : Nat :=
  multiAttestRowsEnd cd (160 + 96 * arrayCount cd 4)
    (UInt256.ofNat (arrayDataNat cd 36)) 0 (arrayCount cd 4)

theorem multiAttestBuiltMemory_freePtr (cd : ByteArray) :
    memLoad (UInt256.ofNat 64) (multiAttestBuiltMemory cd) = UInt256.ofNat (multiAttestBuiltFree cd)
        :=
  multiAttestRowsMemory_freePtr (by omega) (by decide) (pairArrayMemory_freePtr (by decide))

end Benchmarks.EAS.Attester
