import Reasoning.Reach
import Benchmarks.Midnight.TickLibWrapper.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace tickLibWrapperBlocks

/-- Final stack for bytecode block summary `tickLibWrapper_block_0_taken`. -/
def tickLibWrapper_block_0_taken_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 128) :: R)

/-- Final memory for bytecode block summary `tickLibWrapper_block_0_taken`. -/
def tickLibWrapper_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem tickLibWrapper_block_0_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 18) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 18) (tickLibWrapper_block_0_taken_stack (R := R)) (tickLibWrapper_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((36) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.calldatasize (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_0_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 18) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 18) (tickLibWrapper_block_0_taken_stack (R := R)) (tickLibWrapper_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_0_fallthrough`. -/
def tickLibWrapper_block_0_fallthrough_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 128) :: R)

/-- Final memory for bytecode block summary `tickLibWrapper_block_0_fallthrough`. -/
def tickLibWrapper_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem tickLibWrapper_block_0_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 15) (tickLibWrapper_block_0_fallthrough_stack (R := R)) (tickLibWrapper_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((36) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.calldatasize (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_0_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 15) (tickLibWrapper_block_0_fallthrough_stack (R := R)) (tickLibWrapper_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem tickLibWrapper_block_15 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 15) R mem aw rdata σ k C)
    : RDrev Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `tickLibWrapper_block_18_taken`. -/
def tickLibWrapper_block_18_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 18. -/
theorem tickLibWrapper_block_18_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 11983515) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 417) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 18) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 417) (tickLibWrapper_block_18_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((37))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 11983515) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.eq (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 417) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 417)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_18_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 11983515) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 417) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 18) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 417) (tickLibWrapper_block_18_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_18_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_18_fallthrough`. -/
def tickLibWrapper_block_18_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 18. -/
theorem tickLibWrapper_block_18_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 11983515) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 18) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 35) (tickLibWrapper_block_18_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 11) (C + ((37))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 11983515) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.eq (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 417) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 35)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_18_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 11983515) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 18) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 35) (tickLibWrapper_block_18_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_18_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_35_taken`. -/
def tickLibWrapper_block_35_taken_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 35. -/
theorem tickLibWrapper_block_35_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 498317021) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 389) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 35) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 389) (tickLibWrapper_block_35_taken_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 498317021) (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 389) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 389)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_35_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 498317021) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 389) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 35) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 389) (tickLibWrapper_block_35_taken_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_35_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_35_fallthrough`. -/
def tickLibWrapper_block_35_fallthrough_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 35. -/
theorem tickLibWrapper_block_35_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 498317021) x1) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 35) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 47) (tickLibWrapper_block_35_fallthrough_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 6) (C + ((24))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 498317021) (by native_decide) (by evm_ov)
  have r4 := r3.eq (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 389) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 47)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_35_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 498317021) x1) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 35) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 47) (tickLibWrapper_block_35_fallthrough_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_35_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 47. -/
theorem tickLibWrapper_block_47_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 674862235) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 359) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 47) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 359) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 674862235) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 359) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 359)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_47_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 674862235) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 359) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 47) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 359) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_47_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 47. -/
theorem tickLibWrapper_block_47_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 674862235) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 47) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 674862235) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 359) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 58)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_47_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 674862235) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 47) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_47_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 58. -/
theorem tickLibWrapper_block_58_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1010846490) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 168) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 168) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1010846490) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 168) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 168)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_58_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1010846490) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 168) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 168) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_58_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 58. -/
theorem tickLibWrapper_block_58_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1010846490) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 69) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1010846490) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 168) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 69)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_58_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1010846490) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 69) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_58_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 69. -/
theorem tickLibWrapper_block_69_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1805907060) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 135) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 69) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 135) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1805907060) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 135) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 135)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_69_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1805907060) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 135) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 69) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 135) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_69_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 69. -/
theorem tickLibWrapper_block_69_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1805907060) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 69) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 80) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1805907060) (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 135) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 80)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_69_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1805907060) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 69) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 80) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_69_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_80_taken`. -/
def tickLibWrapper_block_80_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 80. -/
theorem tickLibWrapper_block_80_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3994256570) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 93) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 80) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 93) (tickLibWrapper_block_80_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3994256570) (by native_decide) (by evm_ov)
  have r2 := r1.eq (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 93) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 93)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_80_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3994256570) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 93) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 80) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 93) (tickLibWrapper_block_80_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_80_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_80_fallthrough`. -/
def tickLibWrapper_block_80_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 80. -/
theorem tickLibWrapper_block_80_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3994256570) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 80) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 90) (tickLibWrapper_block_80_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 3994256570) (by native_decide) (by evm_ov)
  have r2 := r1.eq (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 93) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 90)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_80_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3994256570) x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 80) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 90) (tickLibWrapper_block_80_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_80_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 90. -/
theorem tickLibWrapper_block_90 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 90) R mem aw rdata σ k C)
    : RDrev Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 93. -/
theorem tickLibWrapper_block_93_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 93) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 131)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_93_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 93) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_93_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 93. -/
theorem tickLibWrapper_block_93_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 93) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 99)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_93_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 93) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 99) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_93_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 99. -/
theorem tickLibWrapper_block_99_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 131)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_99_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_99_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 99. -/
theorem tickLibWrapper_block_99_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 111) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_99_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 99) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 111) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_99_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end tickLibWrapperBlocks
