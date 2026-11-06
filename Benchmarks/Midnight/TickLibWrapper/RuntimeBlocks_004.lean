import Reasoning.Reach
import Benchmarks.Midnight.TickLibWrapper.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace tickLibWrapperBlocks

/-- Automatically generated RD summary for bytecode block at pc 395. -/
theorem tickLibWrapper_block_395_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 395) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
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
theorem tickLibWrapper_block_395_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 395) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_395_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 395. -/
theorem tickLibWrapper_block_395_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 395) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 406) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 406)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_395_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 395) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 406) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_395_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 406. -/
theorem tickLibWrapper_block_406 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 406) R mem aw rdata σ k C)
    : RDret Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode g s0 σ (((UInt256.ofNat 6744).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6744) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  exact RD.genRet r6 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 417. -/
theorem tickLibWrapper_block_417_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 417) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 131)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_417_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 417) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_417_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 417. -/
theorem tickLibWrapper_block_417_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 417) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 423) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 423)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_417_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 417) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 423) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_417_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 423. -/
theorem tickLibWrapper_block_423_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 423) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
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
theorem tickLibWrapper_block_423_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 131) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 423) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_423_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 423. -/
theorem tickLibWrapper_block_423_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 423) R mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 434) R mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 131) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 434)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_423_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 423) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 434) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_423_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 434. -/
theorem tickLibWrapper_block_434 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 434) (x0 :: R) mem aw rdata σ k C)
    : RDret Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode g s0 σ (((UInt256.ofNat 100000000000).toByteArray.write 0 mem x0.toNat 32).readWithPadding x0.toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 100000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  exact RD.genRet r5 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 446. -/
theorem tickLibWrapper_block_446_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 456) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 446) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 456) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 456) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 456)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_446_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 456) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 446) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 456) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_446_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 446. -/
theorem tickLibWrapper_block_446_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 446) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 453) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 456) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 453)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_446_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 446) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 453) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_446_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_453`. -/
def tickLibWrapper_block_453_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 453. -/
theorem tickLibWrapper_block_453 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 453) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x2 (tickLibWrapper_block_453_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.div (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_453_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 453) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x2 (tickLibWrapper_block_453_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_453 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 456. -/
theorem tickLibWrapper_block_456 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 456) R mem aw rdata σ k C)
    : RDrev Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1313373041) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r11 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 476. -/
theorem tickLibWrapper_block_476_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 6744)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 576) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 476) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 576) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6744) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 576)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_476_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 6744)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 576) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 476) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 576) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_476_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 476. -/
theorem tickLibWrapper_block_476_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 6744)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 476) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 486) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6744) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.gt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 486)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_476_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 6744)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 476) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 486) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_476_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_486`. -/
def tickLibWrapper_block_486_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.ofNat 4987541511039073) (UInt256.sub (UInt256.ofNat 3372) x0)) :: (UInt256.ofNat 523) :: (UInt256.ofNat 570) :: (UInt256.ofNat 49999999999) :: (UInt256.ofNat 100000000000) :: (UInt256.ofNat 100000000000) :: R)

/-- Automatically generated RD summary for bytecode block at pc 486. -/
theorem tickLibWrapper_block_486 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 591) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 486) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (tickLibWrapper_block_486_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((43))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 100000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 49999999999) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 570) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 523) (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.swap5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 3372) (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 4987541511039073) (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 591) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 591)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_486_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 591) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 486) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (tickLibWrapper_block_486_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_486 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_523`. -/
def tickLibWrapper_block_523_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1000000000000000000000000000000000000) + (UInt256.shiftRight (x0 + (UInt256.ofNat 999999999999999999)) (UInt256.ofNat 1))) :: ((UInt256.ofNat 1000000000000000000) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 523. -/
theorem tickLibWrapper_block_523 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 446) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 523) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 446) (tickLibWrapper_block_523_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((42))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 999999999999999999) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.shr (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 1000000000000000000000000000000000000) (width := 15) (op := .PUSH15) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 446) (by native_decide) (by evm_ov)
  have r13 := r12.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 446)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_523_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 446) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 523) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 446) (tickLibWrapper_block_523_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_523 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_570`. -/
def tickLibWrapper_block_570_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.div (x0 + x1) x2) x3) :: R)

/-- Automatically generated RD summary for bytecode block at pc 570. -/
theorem tickLibWrapper_block_570 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 570) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x4 (tickLibWrapper_block_570_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.add (by native_decide) (by evm_ov)
  have r3 := r2.div (by native_decide) (by evm_ov)
  have r4 := r3.mul (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_570_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 570) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x4 (tickLibWrapper_block_570_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_570 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 576. -/
theorem tickLibWrapper_block_576 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 576) R mem aw rdata σ k C)
    : RDrev Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3353426433) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r8 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 591. -/
theorem tickLibWrapper_block_591_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 636) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.slt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 636) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 636)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_591_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 636) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_591_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 591. -/
theorem tickLibWrapper_block_591_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 600) (x0 :: R) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.slt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 636) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 600)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_591_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 600) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_591_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end tickLibWrapperBlocks
