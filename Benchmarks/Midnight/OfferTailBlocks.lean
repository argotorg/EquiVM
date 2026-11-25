import Benchmarks.Midnight.OfferFirstBlocks

variable {fork : Ethereum.Fork}

/-! The fixed stores interleaved with the offer tail's canonical scalar readers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightOfferStoreCallbackData {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw value rel : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10687⟩ (value :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 1088 value) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨18342⟩
        ((rel + UInt256.ofNat 292) :: ⟨10709⟩ :: rel :: R)
        (writeWord mem 1088 value) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_10687 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_10687_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_10687_stack,
    midnightBlocks.midnight_block_10687_memory, hroot] at ha1 rd1
  exact ⟨_, _, _, ha1, rd1⟩

theorem midnightOfferStoreReceiver {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw value rel : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10709⟩ (value :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 1120 value) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨18342⟩
        ((rel + UInt256.ofNat 324) :: ⟨10731⟩ :: rel :: R)
        (writeWord mem 1120 value) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_10709 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_10709_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_10709_stack,
    midnightBlocks.midnight_block_10709_memory, hroot] at ha1 rd1
  exact ⟨_, _, _, ha1, rd1⟩

theorem midnightOfferStoreRatifier {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw value rel : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10731⟩ (value :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 1152 value) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨19003⟩
        ((rel + UInt256.ofNat 356) :: ⟨10753⟩ :: rel :: R)
        (writeWord mem 1152 value) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_10731 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_10731_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_10731_stack,
    midnightBlocks.midnight_block_10731_memory, hroot] at ha1 rd1
  exact ⟨_, _, _, ha1, rd1⟩

theorem midnightOfferStoreReduceOnly {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw value rel : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10753⟩ (value :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 1184 value) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨19113⟩
        ((rel + UInt256.ofNat 388) :: ⟨10775⟩ :: rel :: R)
        (writeWord mem 1184 value) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_10753 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_10753_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_10753_stack,
    midnightBlocks.midnight_block_10753_memory, hroot] at ha1 rd1
  exact ⟨_, _, _, ha1, rd1⟩

theorem midnightOfferStoreMaxUnits {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw value rel : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10775⟩ (value :: rel :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 1216 value) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨19113⟩
        ((rel + UInt256.ofNat 420) :: ⟨10795⟩ :: rel :: R)
        (writeWord mem 1216 value) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_10775 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_10775_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_10775_stack,
    midnightBlocks.midnight_block_10775_memory, hroot] at ha1 rd1
  exact ⟨_, _, _, ha1, rd1⟩

end Benchmarks.Midnight
