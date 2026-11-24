import Reasoning.Reach
import Benchmarks.Safe.ViaIR.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR.RuntimeBlocks

set_option maxRecDepth 10000

/-- Automatically generated RD summary for bytecode block at pc 6904. -/
theorem safeRuntime_block_6904 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6904) (x0 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.Safe.ViaIR.safeBytecode g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) x0) ByteArray.empty := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 43901732083494477469716044267715912957164410118621377285867120976187919408275) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := RD.genLog1 r11 (by native_decide) hperm (by evm_ov)
  exact r12.stop (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_6952_taken`. -/
def safeRuntime_block_6952_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6952. -/
theorem safeRuntime_block_6952_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_6952_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6952_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_6952_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6952_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6952_fallthrough`. -/
def safeRuntime_block_6952_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6952. -/
theorem safeRuntime_block_6952_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6973) (safeRuntime_block_6952_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6973)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6952_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6952) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6973) (safeRuntime_block_6952_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6952_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6973`. -/
def safeRuntime_block_6973_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 6973. -/
theorem safeRuntime_block_6973 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6973) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_6973_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6973_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6973) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_6973_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6973 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6974_taken`. -/
def safeRuntime_block_6974_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6974. -/
theorem safeRuntime_block_6974_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6974) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_6974_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6974_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6974) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_6974_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6974_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6974_fallthrough`. -/
def safeRuntime_block_6974_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6974. -/
theorem safeRuntime_block_6974_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6974) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6995) (safeRuntime_block_6974_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6995)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6974_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 228).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6974) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6995) (safeRuntime_block_6974_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6974_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6995`. -/
def safeRuntime_block_6995_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 6995. -/
theorem safeRuntime_block_6995 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6995) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_6995_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6995_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6995) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_6995_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6995 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6996_taken`. -/
def safeRuntime_block_6996_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6996. -/
theorem safeRuntime_block_6996_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6996) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_6996_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6996_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6996) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_6996_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6996_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_6996_fallthrough`. -/
def safeRuntime_block_6996_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6996. -/
theorem safeRuntime_block_6996_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6996) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7017) (safeRuntime_block_6996_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7017)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_6996_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 6996) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7017) (safeRuntime_block_6996_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_6996_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7017`. -/
def safeRuntime_block_7017_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7017. -/
theorem safeRuntime_block_7017 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7017) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7017_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7017_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7017) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7017_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7017 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7018_taken`. -/
def safeRuntime_block_7018_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7018. -/
theorem safeRuntime_block_7018_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7018) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7018_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 260) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7018_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7018) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7018_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7018_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7018_fallthrough`. -/
def safeRuntime_block_7018_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7018. -/
theorem safeRuntime_block_7018_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7018) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7040) (safeRuntime_block_7018_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 260) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7040)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7018_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 260).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7018) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7040) (safeRuntime_block_7018_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7018_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7040`. -/
def safeRuntime_block_7040_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7040. -/
theorem safeRuntime_block_7040 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7040) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7040_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7040_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7040) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7040_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7040 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7041_taken`. -/
def safeRuntime_block_7041_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7041. -/
theorem safeRuntime_block_7041_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7041) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7041_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7041_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7041) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7041_taken_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7041_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7041_fallthrough`. -/
def safeRuntime_block_7041_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7041. -/
theorem safeRuntime_block_7041_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7041) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7062) (safeRuntime_block_7041_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 15) (C + ((50))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7062)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7041_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7041) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7062) (safeRuntime_block_7041_fallthrough_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7041_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7062`. -/
def safeRuntime_block_7062_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7062. -/
theorem safeRuntime_block_7062 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7062) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7062_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7062_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7062) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7062_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7062 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7063_taken`. -/
def safeRuntime_block_7063_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7063. -/
theorem safeRuntime_block_7063_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7063_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7063_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7063_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7063_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7063_fallthrough`. -/
def safeRuntime_block_7063_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7063. -/
theorem safeRuntime_block_7063_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7082) (safeRuntime_block_7063_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7082)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7063_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7082) (safeRuntime_block_7063_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7063_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7082`. -/
def safeRuntime_block_7082_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7082. -/
theorem safeRuntime_block_7082 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7082) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7082_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7082_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7082) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 x0 (safeRuntime_block_7082_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7082 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_7083_taken`. -/
def safeRuntime_block_7083_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 7083. -/
theorem safeRuntime_block_7083_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (x0 + (UInt256.ofNat 31)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7083) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7083_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 111) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 111)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_7083_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (x0 + (UInt256.ofNat 31)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeBytecode 0).contains (UInt256.ofNat 111) = true)
    (h : RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 7083) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.ViaIR.safeBytecode ee g s0 (UInt256.ofNat 111) (safeRuntime_block_7083_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_7083_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.ViaIR.RuntimeBlocks
