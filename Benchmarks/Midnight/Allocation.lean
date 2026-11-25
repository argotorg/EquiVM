import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.WordArray
import Benchmarks.Midnight.MemoryCharge

variable {fork : Ethereum.Fork}

/-! Shared allocation routines from the Midnight runtime. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def allocationEnd (ptr size : UInt256) : UInt256 :=
  ptr + UInt256.land (size + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31))

def allocationCheck (ptr next : UInt256) : UInt256 :=
  UInt256.lor (UInt256.gt next
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))
    (UInt256.lt next ptr)

theorem midnightAllocateCharge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr size ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (allocationEnd ptr size) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨18444⟩ (ptr :: size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryCharge 0 aw aw' C C' ∧ RD fork midnightBytecode I g s0 ret R
      (writeWord mem 64 (allocationEnd ptr size)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18444_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18444_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18473 (by omega) hret rd1
  have h0 := MemoryCharge.refl aw C
  have hc2 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd2 (by memory_charge h0)
  exact ⟨_, _, _, hc2, rd2⟩

theorem midnightAllocate {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr size ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (allocationEnd ptr size) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨18444⟩ (ptr :: size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret R
      (writeWord mem 64 (allocationEnd ptr size)) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', _, rd'⟩ := midnightAllocateCharge hstack hc hret rd
  exact ⟨aw', k', C', rd'⟩

theorem midnightAllocate224 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 224) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨18362⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret R
      (writeWord mem 64 (ptr + UInt256.ofNat 224)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18362_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18362_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18385 (by omega) hret rd1
  exact ⟨_, _, _, rd2⟩

theorem midnightAllocate256 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 256) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨18389⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret R
      (writeWord mem 64 (ptr + UInt256.ofNat 256)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18389_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18389_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18413 (by omega) hret rd1
  exact ⟨_, _, _, rd2⟩

theorem midnightAllocate128 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 128) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨18417⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret R
      (writeWord mem 64 (ptr + UInt256.ofNat 128)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18417_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18417_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18440 (by omega) hret rd1
  exact ⟨_, _, _, rd2⟩

set_option maxRecDepth 2000000 in
theorem midnightAllocate128Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 128) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨18417⟩ (ptr :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_18417_taken hstack hc (by jump_dest) rd
  exact midnightBlocks.midnight_block_15087 (by
    simp only [midnightBlocks.midnight_block_18417_taken_stack, List.length_cons]; omega) rd1

set_option maxRecDepth 2000000 in
theorem midnightAllocate256Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 256) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨18389⟩ (ptr :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_18389_taken hstack hc (by jump_dest) rd
  exact midnightBlocks.midnight_block_15087 (by
    simp only [midnightBlocks.midnight_block_18389_taken_stack, List.length_cons]; omega) rd1

set_option maxRecDepth 2000000 in
theorem midnightAllocateRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr size : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hc : allocationCheck ptr (allocationEnd ptr size) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨18444⟩ (ptr :: size :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_18444_taken hstack hc (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_18444_taken_stack] at rd1
  exact midnightBlocks.midnight_block_15087 (by simp only [List.length_cons]; omega) rd1

end Benchmarks.Midnight
