import Benchmarks.Midnight.ScratchMemory
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.SettlementFields

variable {fork : Ethereum.Fork}

/-! Initial market allocation and mapping scratch space for the stored-market reader. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def blankMarketRaw (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  let m0 := writeWord mem ptr.toNat (memLoad ⟨800⟩ mem)
  let m1 := writeWord m0 (ptr + ⟨32⟩).toNat (memLoad ⟨800⟩ m0)
  let m2 := writeWord m1 (ptr + ⟨64⟩).toNat (memLoad ⟨800⟩ m1)
  let m3 := writeWord m2 (ptr + ⟨96⟩).toNat ⟨96⟩
  let m4 := writeWord m3 (ptr + ⟨128⟩).toNat (memLoad ⟨800⟩ m3)
  let m5 := writeWord m4 (ptr + ⟨160⟩).toNat (memLoad ⟨800⟩ m4)
  let m6 := writeWord m5 (ptr + ⟨192⟩).toNat (memLoad ⟨800⟩ m5)
  writeWord m6 (ptr + ⟨224⟩).toNat (memLoad ⟨800⟩ m6)

def toMarketAllocatedMemory : ByteArray := writeWord midnightEntryMemory 64 ⟨1088⟩

def toMarketBlankMemory : ByteArray :=
  blankMarketRaw toMarketAllocatedMemory ⟨832⟩

def toMarketInitialMemory (id : UInt256) : ByteArray :=
  twoWordHashMem id ⟨1⟩ toMarketBlankMemory

theorem toMarketBlankMemory_properties :
    toMarketBlankMemory.size = 1088 ∧
    memLoad (UInt256.ofNat 800) toMarketBlankMemory = ⟨0⟩ ∧
    memLoad (UInt256.ofNat 64) toMarketBlankMemory = ⟨1088⟩ := by native_decide

theorem toMarketInitialMemory_properties (id : UInt256) :
    (toMarketInitialMemory id).size = 1088 ∧
    memLoad (UInt256.ofNat 800) (toMarketInitialMemory id) = ⟨0⟩ ∧
    memLoad (UInt256.ofNat 64) (toMarketInitialMemory id) = ⟨1088⟩ ∧
    keccakWord ⟨0⟩ ⟨64⟩ (toMarketInitialMemory id) = solcMappingSlot ⟨1⟩ id := by
  rcases toMarketBlankMemory_properties with ⟨hs, hz, hf⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [toMarketInitialMemory, twoWordHashMem_size_of_ge_64 _ _ (by omega), hs]
  · rw [toMarketInitialMemory, memLoad_twoWordHashMem _ _ _ (by decide) (by rw [hs]; decide), hz]
  · rw [toMarketInitialMemory, memLoad_twoWordHashMem _ _ _ (by decide) (by rw [hs]; decide), hf]
  · exact twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)

set_option maxRecDepth 2000000 in
theorem toMarketInitializeMemory_shape (mem : ByteArray) (ptr id : UInt256) :
    midnightBlocks.midnight_block_751_memory (mem := mem) (x0 := ptr) (x1 := id) =
      writeWord (writeWord (blankMarketRaw mem ptr)
        (memLoad ⟨800⟩ (blankMarketRaw mem ptr)).toNat id) 32 ⟨1⟩ := rfl

set_option maxRecDepth 2000000 in
theorem toMarketInitializeStack_shape (mem : ByteArray) (ptr id : UInt256)
    (I : ExecutionEnv) (σ : AccountMap) (R : List UInt256) :
    midnightBlocks.midnight_block_751_stack (ee := I) (mem := mem) (σ := σ)
      (x0 := ptr) (x1 := id) (R := R) =
    (marketTickSpacing (solcSlotWordAt
      (keccakWord (memLoad ⟨800⟩ (midnightBlocks.midnight_block_751_memory
        (mem := mem) (x0 := ptr) (x1 := id))) ⟨64⟩
        (midnightBlocks.midnight_block_751_memory (mem := mem) (x0 := ptr) (x1 := id)) + ⟨2⟩)
      σ I) :: id :: R) := rfl

set_option maxRecDepth 2000000 in
theorem midnightToMarketInitialize {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {id : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨751⟩ (⟨832⟩ :: id :: R)
      toMarketAllocatedMemory aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨846⟩
      (marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) :: id :: R)
      (toMarketInitialMemory id) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_751_packed hstack rd
  have hm : midnightBlocks.midnight_block_751_memory (mem := toMarketAllocatedMemory)
      (x0 := ⟨832⟩) (x1 := id) = toMarketInitialMemory id := by
    rw [toMarketInitializeMemory_shape]
    change writeWord (writeWord toMarketBlankMemory
      (memLoad ⟨800⟩ toMarketBlankMemory).toNat id) 32 ⟨1⟩ = _
    have hz : memLoad ⟨800⟩ toMarketBlankMemory = ⟨0⟩ := toMarketBlankMemory_properties.2.1
    rw [hz]
    rfl
  have hz : memLoad ⟨800⟩ (toMarketInitialMemory id) = ⟨0⟩ :=
    (toMarketInitialMemory_properties id).2.1
  simp only [toMarketInitializeStack_shape, hm, hz,
    (toMarketInitialMemory_properties id).2.2.2] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

end Benchmarks.Midnight
