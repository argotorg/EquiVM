import Benchmarks.CompoundIII.Comet.LiquidatorPointsData
import Benchmarks.CompoundIII.Comet.WordStructAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def liquidatorPointsWords (p : LiquidatorPointsData) (i : Nat) : UInt256 :=
  match i with
  | 0 => p.absorbs
  | 1 => p.absorbed
  | 2 => p.spend
  | _ => p.reserved

abbrev LiquidatorPointsMemory (mem : ByteArray) (ptr : UInt256) (p : LiquidatorPointsData) :
    Prop := WordStructMemory mem ptr 4 (liquidatorPointsWords p)

theorem LiquidatorPointsMemory.absorbs {mem ptr p} (h : LiquidatorPointsMemory mem ptr p) :
    memLoad ptr mem = p.absorbs := by
  simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right, liquidatorPointsWords] using h.word 0 (by decide)

theorem LiquidatorPointsMemory.absorbed {mem ptr p} (h : LiquidatorPointsMemory mem ptr p) :
    memLoad (ptr + UInt256.ofNat 32) mem = p.absorbed := h.word 1 (by decide)

theorem LiquidatorPointsMemory.spend {mem ptr p} (h : LiquidatorPointsMemory mem ptr p) :
    memLoad (ptr + UInt256.ofNat 64) mem = p.spend := h.word 2 (by decide)

theorem LiquidatorPointsMemory.reserved {mem ptr p} (h : LiquidatorPointsMemory mem ptr p) :
    memLoad (ptr + UInt256.ofNat 96) mem = p.reserved := h.word 3 (by decide)

theorem LiquidatorPointsMemory.writeField {mem ptr p}
    (h : LiquidatorPointsMemory mem ptr p) (i : Fin 4) (next : UInt256) :
    LiquidatorPointsMemory (writeWord mem (ptr + UInt256.ofNat (32 * i.val)).toNat next)
      ptr (liquidatorPointsSet p i next) := by
  apply (h.write i.val i.isLt next).congr
  intro j hj
  fin_cases i <;> interval_cases j <;> rfl

def liquidatorPointsAllocatedMemory (mem : ByteArray) (ptr word : UInt256) : ByteArray :=
  allocatedWordStruct mem ptr 4 (liquidatorPointsWords (liquidatorPointsData word))

theorem liquidatorPointsAllocatedMemory_correct (mem : ByteArray) (ptr word : UInt256)
    (hb : ptr.toNat + 128 < UInt256.size) :
    LiquidatorPointsMemory (liquidatorPointsAllocatedMemory mem ptr word) ptr
      (liquidatorPointsData word) := wordStructStore_memory (by decide) hb

end Benchmarks.CompoundIII.Comet
