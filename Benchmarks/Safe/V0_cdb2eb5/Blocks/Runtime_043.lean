import Reasoning.Reach
import Benchmarks.Safe.V0_cdb2eb5.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_9763_taken`. -/
def safeRuntime_block_9763_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9763. -/
theorem safeRuntime_block_9763_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9779) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9763) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9779) (safeRuntime_block_9763_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 9779) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9779)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9763_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9779) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9763) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9779) (safeRuntime_block_9763_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9763_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9763_fallthrough`. -/
def safeRuntime_block_9763_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9763. -/
theorem safeRuntime_block_9763_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9763) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9776) (safeRuntime_block_9763_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 9779) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9776)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9763_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9763) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9776) (safeRuntime_block_9763_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9763_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9776. -/
theorem safeRuntime_block_9776 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9776) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9779`. -/
def safeRuntime_block_9779_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9779. -/
theorem safeRuntime_block_9779 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9779) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x3 (safeRuntime_block_9779_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9779_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9779) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x3 (safeRuntime_block_9779_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9779 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9786_taken`. -/
def safeRuntime_block_9786_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9786. -/
theorem safeRuntime_block_9786_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9813) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9786) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9813) (safeRuntime_block_9786_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 20) (C + ((54))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r14 := r13.dup13 (by native_decide) (by evm_ov)
  have r15 := r14.dup15 (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.slt (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 9813) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9813)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9786_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9813) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9786) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9813) (safeRuntime_block_9786_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9786_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9786_fallthrough`. -/
def safeRuntime_block_9786_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9786. -/
theorem safeRuntime_block_9786_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9786) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9810) (safeRuntime_block_9786_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 20) (C + ((54))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r14 := r13.dup13 (by native_decide) (by evm_ov)
  have r15 := r14.dup15 (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.slt (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 9813) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9810)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9786_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9786) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9810) (safeRuntime_block_9786_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9786_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9810. -/
theorem safeRuntime_block_9810 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9810) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9813`. -/
def safeRuntime_block_9813_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x11 :: (UInt256.ofNat 9822) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9813. -/
theorem safeRuntime_block_9813 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 8975) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9813) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 8975) (safeRuntime_block_9813_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9822) (by native_decide) (by evm_ov)
  have r3 := r2.dup13 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8975) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8975)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9813_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 8975) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9813) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 8975) (safeRuntime_block_9813_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9813 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9822_taken`. -/
def safeRuntime_block_9822_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 32)).toNat 32)) :: x0 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9822. -/
theorem safeRuntime_block_9822_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9855) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9822) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9855) (safeRuntime_block_9822_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (R := R)) mem aw rdata σ (k + 23) (C + ((72))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap11 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup13 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.swap10 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.dup13 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.calldataload (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.dup2 (by native_decide) (by evm_ov)
  have r20 := r19.gt (by native_decide) (by evm_ov)
  have r21 := r20.iszero (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 9855) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9855)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9822_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9855) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9822) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9855) (safeRuntime_block_9822_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9822_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9822_fallthrough`. -/
def safeRuntime_block_9822_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 32)).toNat 32)) :: x0 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9822. -/
theorem safeRuntime_block_9822_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9822) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9852) (safeRuntime_block_9822_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (R := R)) mem aw rdata σ (k + 23) (C + ((72))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap11 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup13 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.swap10 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.dup13 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.calldataload (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.dup2 (by native_decide) (by evm_ov)
  have r20 := r19.gt (by native_decide) (by evm_ov)
  have r21 := r20.iszero (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 9855) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9852)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9822_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9822) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9852) (safeRuntime_block_9822_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9822_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9852. -/
theorem safeRuntime_block_9852 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9852) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9855`. -/
def safeRuntime_block_9855_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x12 + x0) :: x13 :: (UInt256.ofNat 9867) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9855. -/
theorem safeRuntime_block_9855 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9033) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9855) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9033) (safeRuntime_block_9855_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) mem aw rdata σ (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9867) (by native_decide) (by evm_ov)
  have r3 := r2.dup15 (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup16 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 9033) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9033)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9855_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9033) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9855) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9033) (safeRuntime_block_9855_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9855 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9867`. -/
def safeRuntime_block_9867_stack {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x12 : UInt256} {x13 : UInt256} {x14 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x14 + (UInt256.ofNat 96)) :: (UInt256.ofNat 9886) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x0 :: x1 :: x12 :: x13 :: x14 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9867. -/
theorem safeRuntime_block_9867 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9497) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9867) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9497) (safeRuntime_block_9867_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (x13 := x13) (x14 := x14) (R := R)) mem aw rdata σ (k + 14) (C + ((42))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap11 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.swap9 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 9886) (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r11 := r10.dup14 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 9497) (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9497)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9867_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9497) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9867) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9497) (safeRuntime_block_9867_stack (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (x13 := x13) (x14 := x14) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9867 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9886`. -/
def safeRuntime_block_9886_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x12 + (UInt256.ofNat 224)) :: (UInt256.ofNat 9921) :: x1 :: x2 :: x3 :: (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 192)).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 160)).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 128)).toNat 32)) :: x0 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9886. -/
theorem safeRuntime_block_9886 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 8975) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9886) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 8975) (safeRuntime_block_9886_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw rdata σ (k + 27) (C + ((80))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap7 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.dup13 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.swap6 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.dup13 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.calldataload (by native_decide) (by evm_ov)
  have r14 := r13.swap5 (by native_decide) (by evm_ov)
  have r15 := r14.pop (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r17 := r16.dup13 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := r18.calldataload (by native_decide) (by evm_ov)
  have r20 := r19.swap4 (by native_decide) (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 9921) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r24 := r23.dup14 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 8975) (by native_decide) (by evm_ov)
  have r27 := r26.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8975)) r27 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9886_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 8975) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9886) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 8975) (safeRuntime_block_9886_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9886 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9921`. -/
def safeRuntime_block_9921_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x12 + (UInt256.ofNat 256)) :: (UInt256.ofNat 9936) :: x1 :: x2 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9921. -/
theorem safeRuntime_block_9921 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 8975) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9921) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 8975) (safeRuntime_block_9921_stack (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw rdata σ (k + 9) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 9936) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r6 := r5.dup14 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8975) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8975)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9921_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 8975) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9921) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 8975) (safeRuntime_block_9921_stack (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9921 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9936_taken`. -/
def safeRuntime_block_9936_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 288)).toNat 32)) :: x1 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9936. -/
theorem safeRuntime_block_9936_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9963) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9936) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9963) (safeRuntime_block_9936_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw rdata σ (k + 17) (C + ((55))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r5 := r4.dup13 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.gt (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 9963) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9963)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9936_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9963) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9936) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9963) (safeRuntime_block_9936_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9936_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9936_fallthrough`. -/
def safeRuntime_block_9936_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 288)).toNat 32)) :: x1 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9936. -/
theorem safeRuntime_block_9936_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9936) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9960) (safeRuntime_block_9936_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw rdata σ (k + 17) (C + ((55))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r5 := r4.dup13 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.gt (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 9963) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9960)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9936_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9936) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9960) (safeRuntime_block_9936_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9936_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9960. -/
theorem safeRuntime_block_9960 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9960) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9963`. -/
def safeRuntime_block_9963_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x12 + x0) :: x13 :: (UInt256.ofNat 9975) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9963. -/
theorem safeRuntime_block_9963 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9121) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9963) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9121) (safeRuntime_block_9963_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) mem aw rdata σ (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9975) (by native_decide) (by evm_ov)
  have r3 := r2.dup15 (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup16 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 9121) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9121)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9963_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9121) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9963) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9121) (safeRuntime_block_9963_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9963 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9975`. -/
def safeRuntime_block_9975_stack {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9975. -/
theorem safeRuntime_block_9975 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x15 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9975) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x15 (safeRuntime_block_9975_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw rdata σ (k + 19) (C + ((56))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.swap6 (by native_decide) (by evm_ov)
  have r7 := r6.swap9 (by native_decide) (by evm_ov)
  have r8 := r7.swap12 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.swap3 (by native_decide) (by evm_ov)
  have r11 := r10.swap6 (by native_decide) (by evm_ov)
  have r12 := r11.swap9 (by native_decide) (by evm_ov)
  have r13 := r12.swap12 (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := r14.swap4 (by native_decide) (by evm_ov)
  have r16 := r15.swap7 (by native_decide) (by evm_ov)
  have r17 := r16.swap10 (by native_decide) (by evm_ov)
  have r18 := r17.pop (by native_decide) (by evm_ov)
  have r19 := r18.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r19 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9975_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x15 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9975) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x15 (safeRuntime_block_9975_stack (x0 := x0) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9975 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks
