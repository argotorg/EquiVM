import Reasoning.Reach
import Benchmarks.Safe.ViaIR.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR.RuntimeBlocks

set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `safeRuntime_block_4354_fallthrough`. -/
def safeRuntime_block_4354_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4354. -/
theorem safeRuntime_block_4354_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 320)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4354) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4369) (safeRuntime_block_4354_fallthrough_stack (R := R)) mem aw rdata σ (k + 10) (C + ((33))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.not (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4369)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4354_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 320)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4354) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4369) (safeRuntime_block_4354_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4354_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4369`. -/
def safeRuntime_block_4369_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4376) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4369. -/
theorem safeRuntime_block_4369 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 6952) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4369) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (safeRuntime_block_4369_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4376) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6952) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6952)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4369_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 6952) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4369) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (safeRuntime_block_4369_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4369 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4376_taken`. -/
def safeRuntime_block_4376_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4376. -/
theorem safeRuntime_block_4376_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4376) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4376_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.gt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4376_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4376) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4376_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4376_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4376_fallthrough`. -/
def safeRuntime_block_4376_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4376. -/
theorem safeRuntime_block_4376_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4376) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4394) (safeRuntime_block_4376_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.gt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4394)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4376_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4376) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4394) (safeRuntime_block_4376_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4376_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4394`. -/
def safeRuntime_block_4394_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + x0) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 4407) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4394. -/
theorem safeRuntime_block_4394 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7083) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4394) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7083) (safeRuntime_block_4394_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4407) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.calldatasize (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 7083) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7083)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4394_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7083) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4394) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7083) (safeRuntime_block_4394_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4394 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4407_taken`. -/
def safeRuntime_block_4407_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4407. -/
theorem safeRuntime_block_4407_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4407_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r6 := r5.calldataload (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4407_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4407_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4407_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4407_fallthrough`. -/
def safeRuntime_block_4407_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4407. -/
theorem safeRuntime_block_4407_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 2))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4421) (safeRuntime_block_4407_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r6 := r5.calldataload (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4421)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4407_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) (UInt256.ofNat 2))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4407) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4421) (safeRuntime_block_4407_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4407_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4421`. -/
def safeRuntime_block_4421_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4428) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4421. -/
theorem safeRuntime_block_4421 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 6974) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4421) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6974) (safeRuntime_block_4421_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4428) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 6974) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6974)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4421_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 6974) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4421) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6974) (safeRuntime_block_4421_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4421 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4428`. -/
def safeRuntime_block_4428_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4437) :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4428. -/
theorem safeRuntime_block_4428 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7018) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4428) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7018) (safeRuntime_block_4428_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4437) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7018) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7018)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4428_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7018) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4428) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7018) (safeRuntime_block_4428_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4428 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4437_taken`. -/
def safeRuntime_block_4437_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4437. -/
theorem safeRuntime_block_4437_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4437) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4437_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 292) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.gt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4437_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4437) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_4437_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4437_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4437_fallthrough`. -/
def safeRuntime_block_4437_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4437. -/
theorem safeRuntime_block_4437_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4437) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4456) (safeRuntime_block_4437_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 292) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.gt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4456)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4437_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 292).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4437) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4456) (safeRuntime_block_4437_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4437_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4456`. -/
def safeRuntime_block_4456_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + x0) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 4469) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4456. -/
theorem safeRuntime_block_4456 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7262) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4456) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7262) (safeRuntime_block_4456_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4469) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.calldatasize (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 7262) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7262)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4456_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7262) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4456) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7262) (safeRuntime_block_4456_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4456 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4469`. -/
def safeRuntime_block_4469_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 4485) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 4522) :: x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4469. -/
theorem safeRuntime_block_4469 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7497) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4469) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7497) (safeRuntime_block_4469_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4522) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 4485) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7497) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7497)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4469_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 7497) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4469) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7497) (safeRuntime_block_4469_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_4469 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4485`. -/
def safeRuntime_block_4485_stack {ee : ExecutionEnv} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (x7 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: x3 :: x8 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 100).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 196).toNat 32)) :: x6 :: (UInt256.land x4 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4485. -/
theorem safeRuntime_block_4485 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9040) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4485) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9040) (safeRuntime_block_4485_stack (ee := ee) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 5) x0) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.dup7 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r13 := r12.calldataload (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r15 := r14.calldataload (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r17 := r16.calldataload (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r19 := r18.calldataload (by native_decide) (by evm_ov)
  have r20 := r19.dup14 (by native_decide) (by evm_ov)
  have r21 := r20.dup10 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r23 := r22.calldataload (by native_decide) (by evm_ov)
  have r24 := r23.dup16 (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 9040) (by native_decide) (by evm_ov)
  have r26 := r25.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9040)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4485_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9040) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4485) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9040) (safeRuntime_block_4485_stack (ee := ee) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 5) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_4485 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4522`. -/
def safeRuntime_block_4522_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat ee.source.val) :: x0 :: x3 :: (UInt256.ofNat 4534) :: x5 :: x1 :: x2 :: x3 :: x4 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4522. -/
theorem safeRuntime_block_4522 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9258) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4522) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9258) (safeRuntime_block_4522_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 8) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap5 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4534) (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.dup8 (by native_decide) (by evm_ov)
  have r6 := r5.caller (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 9258) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9258)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4522_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 9258) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4522) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 9258) (safeRuntime_block_4522_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4522 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4534_taken`. -/
def safeRuntime_block_4534_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x0 :: x1 :: x2 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (⟨0⟩ : UInt256)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4534. -/
theorem safeRuntime_block_4534_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 5454) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4534) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 5454) (safeRuntime_block_4534_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.swap4 (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 5454) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5454)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4534_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 5454) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4534) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 5454) (safeRuntime_block_4534_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_4534_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4534_fallthrough`. -/
def safeRuntime_block_4534_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x0 :: x1 :: x2 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (⟨0⟩ : UInt256)))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4534. -/
theorem safeRuntime_block_4534_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4534) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4584) (safeRuntime_block_4534_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.swap4 (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 5454) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4584)) r13 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4534_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 33528237782592280163068556224972516439282563014722366175641814928123294921928) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4534) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4584) (safeRuntime_block_4534_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_4534_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4584_taken`. -/
def safeRuntime_block_4584_taken_stack {ee : ExecutionEnv} {g : Sat256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) + (UInt256.ofNat 2500)) :: (UInt256.div (UInt256.shiftLeft (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.ofNat 6)) (UInt256.ofNat 63)) :: ((g.subNat (C + ((3)) + 2)).toUInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4584. -/
theorem safeRuntime_block_4584_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) + (UInt256.ofNat 2500))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 5344) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4584) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 5344) (safeRuntime_block_4584_taken_stack (ee := ee) (g := g) (C := C) (R := R)) mem aw rdata σ (k + 19) (C + ((62))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.genGas (RD.normalizeCounters (k' := k + 2) (C' := C + ((3))) r2 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 63) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r6 := r5.calldataload (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 2500) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r12 := r11.calldataload (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 5344) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5344)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4584_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) + (UInt256.ofNat 2500))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 5344) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4584) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 5344) (safeRuntime_block_4584_taken_stack (ee := ee) (g := g) (C := C) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4584_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4584_fallthrough`. -/
def safeRuntime_block_4584_fallthrough_stack {ee : ExecutionEnv} {g : Sat256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) + (UInt256.ofNat 2500)) :: (UInt256.div (UInt256.shiftLeft (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) (UInt256.ofNat 6)) (UInt256.ofNat 63)) :: ((g.subNat (C + ((3)) + 2)).toUInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4584. -/
theorem safeRuntime_block_4584_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) + (UInt256.ofNat 2500))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4584) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4612) (safeRuntime_block_4584_fallthrough_stack (ee := ee) (g := g) (C := C) (R := R)) mem aw rdata σ (k + 19) (C + ((62))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.genGas (RD.normalizeCounters (k' := k + 2) (C' := C + ((3))) r2 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 63) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r6 := r5.calldataload (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 2500) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r12 := r11.calldataload (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 5344) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4612)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4584_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 132).toNat 32)) + (UInt256.ofNat 2500))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4584) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4612) (safeRuntime_block_4584_fallthrough_stack (ee := ee) (g := g) (C := C) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4584_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4612. -/
theorem safeRuntime_block_4612_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x1 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 5446) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4612) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 5446) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5446) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5446)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4612_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x1 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 5446) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 4612) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 5446) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4612_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.ViaIR.RuntimeBlocks
