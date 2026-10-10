import Benchmarks.CompoundIII.Comet.UserBasicData
import Benchmarks.CompoundIII.Comet.WordStructMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def userBasicMemWord (basic : UserBasicData) (i : Nat) : UInt256 :=
  match i with
  | 0 => UInt256.signextend ⟨12⟩ basic.principal
  | 1 => basic.index
  | 2 => basic.accrued
  | 3 => basic.assets
  | _ => basic.reserved

abbrev UserBasicMemory (mem : ByteArray) (ptr : UInt256) (basic : UserBasicData) : Prop :=
  WordStructMemory mem ptr 5 (userBasicMemWord basic)

theorem UserBasicMemory.principal {mem ptr basic} (h : UserBasicMemory mem ptr basic) :
    memLoad ptr mem = UInt256.signextend ⟨12⟩ basic.principal := by
  have hw := h.word 0 (by decide)
  simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right, userBasicMemWord] using hw

theorem UserBasicMemory.index {mem ptr basic} (h : UserBasicMemory mem ptr basic) :
    memLoad (ptr + ⟨32⟩) mem = basic.index := h.word 1 (by decide)

theorem UserBasicMemory.accrued {mem ptr basic} (h : UserBasicMemory mem ptr basic) :
    memLoad (ptr + ⟨64⟩) mem = basic.accrued := h.word 2 (by decide)

theorem UserBasicMemory.assets {mem ptr basic} (h : UserBasicMemory mem ptr basic) :
    memLoad (ptr + ⟨96⟩) mem = basic.assets := h.word 3 (by decide)

theorem UserBasicMemory.reserved {mem ptr basic} (h : UserBasicMemory mem ptr basic) :
    memLoad (ptr + ⟨128⟩) mem = basic.reserved := h.word 4 (by decide)

theorem UserBasicMemory.writePrincipal {mem ptr basic} (h : UserBasicMemory mem ptr basic)
    (principal : UInt256) :
    UserBasicMemory (writeWord mem ptr.toNat (UInt256.signextend ⟨12⟩ principal)) ptr
      { basic with principal := principal } := by
  have hw := h.write 0 (by decide) (UInt256.signextend ⟨12⟩ principal)
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right] at hw
  apply hw.congr
  intro i hi
  interval_cases i <;> rfl

theorem UserBasicMemory.writeIndex {mem ptr basic} (h : UserBasicMemory mem ptr basic)
    (index : UInt256) (hb : index.toNat < 2^64) :
    UserBasicMemory (writeWord mem (ptr + ⟨32⟩).toNat index) ptr
      { basic with index := index, index_lt := hb } := by
  apply (h.write 1 (by decide) index).congr
  intro i hi
  interval_cases i <;> rfl

theorem UserBasicMemory.writeAccrued {mem ptr basic} (h : UserBasicMemory mem ptr basic)
    (accrued : UInt256) (hb : accrued.toNat < 2^64) :
    UserBasicMemory (writeWord mem (ptr + ⟨64⟩).toNat accrued) ptr
      { basic with accrued := accrued, accrued_lt := hb } := by
  apply (h.write 2 (by decide) accrued).congr
  intro i hi
  interval_cases i <;> rfl

end Benchmarks.CompoundIII.Comet
