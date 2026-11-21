import Benchmarks.Midnight.Allocation
import Benchmarks.Midnight.MemoryFunding

/-! Memory accounting through the compiler's checked allocators. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightAllocate_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr size ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (allocationEnd ptr size) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18444⟩ (ptr :: size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 64 (allocationEnd ptr size)) aw' C' ∧
      RD midnightBytecode I g s0 ret R
        (writeWord mem 64 (allocationEnd ptr size)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18444_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18444_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18473 (by omega) hret rd1
  have ha2 := memoryFundingAt (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_18473_memory
    memory_fund ha)
  exact ⟨_, _, _, ha2, rd2⟩

theorem midnightAllocate224_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 224) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18362⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 64 (ptr + UInt256.ofNat 224)) aw' C' ∧
      RD midnightBytecode I g s0 ret R
        (writeWord mem 64 (ptr + UInt256.ofNat 224)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18362_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18362_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18385 (by omega) hret rd1
  have ha2 := memoryFundingAt (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_18385_memory
    memory_fund ha)
  exact ⟨_, _, _, ha2, rd2⟩

theorem midnightAllocate256_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 256) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18389⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 64 (ptr + UInt256.ofNat 256)) aw' C' ∧
      RD midnightBytecode I g s0 ret R
        (writeWord mem 64 (ptr + UInt256.ofNat 256)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18389_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18389_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18413 (by omega) hret rd1
  have ha2 := memoryFundingAt (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_18413_memory
    memory_fund ha)
  exact ⟨_, _, _, ha2, rd2⟩

theorem midnightAllocate128_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 128) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18417⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWord mem 64 (ptr + UInt256.ofNat 128)) aw' C' ∧
      RD midnightBytecode I g s0 ret R
        (writeWord mem 64 (ptr + UInt256.ofNat 128)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18417_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18417_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18440 (by omega) hret rd1
  have ha2 := memoryFundingAt (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_18440_memory
    memory_fund ha)
  exact ⟨_, _, _, ha2, rd2⟩

end Benchmarks.Midnight
