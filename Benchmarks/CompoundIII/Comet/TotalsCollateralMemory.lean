import Benchmarks.CompoundIII.Comet.TotalsCollateralData
import Benchmarks.CompoundIII.Comet.WordStructAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def collateralTotalWords (total reserved : UInt256) (i : Nat) : UInt256 :=
  if i = 0 then total else reserved

abbrev TotalsCollateralMemory (mem : ByteArray) (ptr total reserved : UInt256) : Prop :=
  WordStructMemory mem ptr 2 (collateralTotalWords total reserved)

theorem TotalsCollateralMemory.total {mem ptr total reserved}
    (h : TotalsCollateralMemory mem ptr total reserved) : memLoad ptr mem = total := by
  simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right, collateralTotalWords, if_pos rfl] using h.word 0 (by decide)

theorem TotalsCollateralMemory.reserved {mem ptr total reserved}
    (h : TotalsCollateralMemory mem ptr total reserved) :
    memLoad (ptr + UInt256.ofNat 32) mem = reserved := h.word 1 (by decide)

theorem TotalsCollateralMemory.writeTotal {mem ptr total reserved}
    (h : TotalsCollateralMemory mem ptr total reserved) (next : UInt256) :
    TotalsCollateralMemory (writeWord mem ptr.toNat next) ptr next reserved := by
  have hw := h.write 0 (by decide) next
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right] at hw
  apply hw.congr
  intro i hi
  interval_cases i <;> rfl

def totalsCollateralAllocatedMemory (mem : ByteArray) (ptr word : UInt256) : ByteArray :=
  allocatedWordStruct mem ptr 2 (collateralTotalWords (low128 word) (high128 word))

theorem totalsCollateralAllocatedMemory_correct (mem : ByteArray) (ptr word : UInt256)
    (hb : ptr.toNat + 64 < UInt256.size) :
    TotalsCollateralMemory (totalsCollateralAllocatedMemory mem ptr word) ptr
      (low128 word) (high128 word) := wordStructStore_memory (by decide) hb

theorem totalsCollateralAllocatedMemory_free {mem ptr word}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 64 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (totalsCollateralAllocatedMemory mem ptr word) =
      ptr + UInt256.ofNat 64 :=
  allocatedWordStruct_free (mem := mem) (ptr := ptr) (n := 2)
    (words := collateralTotalWords (low128 word) (high128 word)) (by decide) hlo hb

end Benchmarks.CompoundIII.Comet
