import Benchmarks.Midnight.SafeTransferPrepare
import Benchmarks.Midnight.BoolMemoryDecode

variable {fork : Ethereum.Fork}

/-! Shared control flow after the safe-transfer return buffer has been allocated. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def safeTransferCheckPC (isFrom : Bool) : UInt256 := if isFrom then ⟨23530⟩ else ⟨23319⟩
def safeTransferLengthPC (isFrom : Bool) : UInt256 := if isFrom then ⟨23537⟩ else ⟨23326⟩
def safeTransferDecodeReturnPC (isFrom : Bool) : UInt256 := if isFrom then ⟨23592⟩ else ⟨23381⟩

theorem safeTransferPostFailure (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 (safeTransferCheckPC isFrom)
      (ptr :: ⟨0⟩ :: R) mem aw rdata σ k C) : RDrev fork midnightBytecode g s0 := by
  cases isFrom with
  | false =>
    have rd1 := midnightBlocks.midnight_block_23319_taken hstack (by decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_3715 hstack rd1
  | true =>
    have rd1 := midnightBlocks.midnight_block_23530_taken hstack (by decide) (by jump_dest) rd
    exact midnightBlocks.midnight_block_3715 hstack rd1

theorem safeTransferPostSuccessCharge (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 (safeTransferCheckPC isFrom)
      (ptr :: ⟨1⟩ :: R) mem aw rdata σ k C) :
    ∃ k' C', MemoryCharge 0 aw aw C C' ∧ RD fork midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: R) mem aw rdata σ k' C' := by
  have h0 := MemoryCharge.refl aw C
  cases isFrom with
  | false => 
    have rd1 := midnightBlocks.midnight_block_23319_fallthrough hstack (by decide) rd
    have hc1 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd1 (by memory_charge h0)
    exact ⟨_, _, hc1, rd1⟩
  | true => 
    have rd1 := midnightBlocks.midnight_block_23530_fallthrough hstack (by decide) rd
    have hc1 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd1 (by memory_charge h0)
    exact ⟨_, _, hc1, rd1⟩

theorem safeTransferPostEmptyCharge (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr ret : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hempty : memLoad ptr mem = ⟨0⟩) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryCharge 0 aw aw' C C' ∧ RD fork midnightBytecode I g s0 ret R mem aw' rdata σ k' C' := by
  have h0 := MemoryCharge.refl aw C
  cases isFrom with
  | false =>
    have rd1 := midnightBlocks.midnight_block_23326_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hempty]; decide) rd
    simp only [midnightBlocks.midnight_block_23326_fallthrough_stack, hempty] at rd1
    have rd2 := midnightBlocks.midnight_block_23338_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) rd1
    have rd3 := midnightBlocks.midnight_block_23346 (by omega) hret rd2
    have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd3 (by memory_charge h0)
    exact ⟨_, _, _, hc3, rd3⟩
  | true =>
    have rd1 := midnightBlocks.midnight_block_23537_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hempty]; decide) rd
    simp only [midnightBlocks.midnight_block_23537_fallthrough_stack, hempty] at rd1
    have rd2 := midnightBlocks.midnight_block_23549_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) rd1
    have rd3 := midnightBlocks.midnight_block_23557 (by omega) hret rd2
    have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd3 (by memory_charge h0)
    exact ⟨_, _, _, hc3, rd3⟩

theorem safeTransferPostNonemptyCharge (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr size : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hsize : memLoad ptr mem = size) (hne : size ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryCharge 0 aw aw' C C' ∧ RD fork midnightBytecode I g s0 ⟨20432⟩
      ((ptr + UInt256.ofNat 32) :: ((ptr + size) + UInt256.ofNat 32) ::
        safeTransferDecodeReturnPC isFrom :: R) mem aw' rdata σ k' C' := by
  have h0 := MemoryCharge.refl aw C
  cases isFrom with
  | false =>
    have rd1 := midnightBlocks.midnight_block_23326_taken (by omega)
      (by rw [hsize, isZero_eq_zero_of_ne hne]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_23326_taken_stack, hsize] at rd1
    have rd2 := midnightBlocks.midnight_block_23362 (by omega) (by jump_dest) rd1
    have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd2 (by memory_charge h0)
    exact ⟨_, _, _, hc3, rd2⟩
  | true =>
    have rd1 := midnightBlocks.midnight_block_23537_taken (by omega)
      (by rw [hsize, isZero_eq_zero_of_ne hne]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_23537_taken_stack, hsize] at rd1
    have rd2 := midnightBlocks.midnight_block_23573 (by omega) (by jump_dest) rd1
    have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd2 (by memory_charge h0)
    exact ⟨_, _, _, hc3, rd2⟩

theorem safeTransferPostTrueCharge (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ret word : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hne : word ≠ ⟨0⟩) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 (safeTransferDecodeReturnPC isFrom)
      (word :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', MemoryCharge 0 aw aw C C' ∧ RD fork midnightBytecode I g s0 ret R mem aw rdata σ k' C' := by
  have h0 := MemoryCharge.refl aw C
  cases isFrom with
  | false =>
    have rd1 := midnightBlocks.midnight_block_23381
      (by simp only [List.length_cons]; omega) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_23338_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hne) rd1
    have rd3 := midnightBlocks.midnight_block_23346 (by omega) hret rd2
    have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd3 (by memory_charge h0)
    exact ⟨_, _, hc3, rd3⟩
  | true =>
    have rd1 := midnightBlocks.midnight_block_23592
      (by simp only [List.length_cons]; omega) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_23549_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hne) rd1
    have rd3 := midnightBlocks.midnight_block_23557 (by omega) hret rd2
    have hc3 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd3 (by memory_charge h0)
    exact ⟨_, _, hc3, rd3⟩

theorem safeTransferPostSuccess (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 (safeTransferCheckPC isFrom)
      (ptr :: ⟨1⟩ :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: R) mem aw rdata σ k' C' := by
  obtain ⟨k', C', _, rd'⟩ := safeTransferPostSuccessCharge isFrom hstack rd
  exact ⟨k', C', rd'⟩

theorem safeTransferPostEmpty (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr ret : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hempty : memLoad ptr mem = ⟨0⟩) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret R mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', _, rd'⟩ := safeTransferPostEmptyCharge isFrom hstack hempty hret rd
  exact ⟨aw', k', C', rd'⟩

theorem safeTransferPostNonempty (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ptr size : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hsize : memLoad ptr mem = size) (hne : size ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 (safeTransferLengthPC isFrom)
      (ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨20432⟩
      ((ptr + UInt256.ofNat 32) :: ((ptr + size) + UInt256.ofNat 32) ::
        safeTransferDecodeReturnPC isFrom :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', _, rd'⟩ := safeTransferPostNonemptyCharge isFrom hstack hsize hne rd
  exact ⟨aw', k', C', rd'⟩

theorem safeTransferPostTrue (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw ret word : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hne : word ≠ ⟨0⟩) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 (safeTransferDecodeReturnPC isFrom)
      (word :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode I g s0 ret R mem aw rdata σ k' C' := by
  obtain ⟨k', C', _, rd'⟩ := safeTransferPostTrueCharge isFrom hstack hne hret rd
  exact ⟨k', C', rd'⟩

theorem safeTransferPostFalse (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 (safeTransferDecodeReturnPC isFrom)
      (⟨0⟩ :: R) mem aw rdata σ k C) : RDrev fork midnightBytecode g s0 := by
  cases isFrom with
  | false =>
    have rd1 := midnightBlocks.midnight_block_23381
      (by simp only [List.length_cons]; omega) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_23338_taken (by omega) (by decide) (by jump_dest) rd1
    exact midnightBlocks.midnight_block_23347
      (by simp only [midnightBlocks.midnight_block_23338_taken_stack]; omega) rd2
  | true =>
    have rd1 := midnightBlocks.midnight_block_23592
      (by simp only [List.length_cons]; omega) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_23549_taken (by omega) (by decide) (by jump_dest) rd1
    exact midnightBlocks.midnight_block_23558
      (by simp only [midnightBlocks.midnight_block_23549_taken_stack]; omega) rd2

end Benchmarks.Midnight
