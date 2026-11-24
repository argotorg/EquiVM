import Reasoning.Reach
import Benchmarks.Safe.Runs1e6.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.Runs1e6.RuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 13582. -/
theorem safeRuntime_block_13582 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13582) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_13585`. -/
def safeRuntime_block_13585_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x3.toNat 32)) :: (UInt256.ofNat 13596) :: (uInt256OfByteArray (ee.calldata.readBytes x3.toNat 32)) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13585. -/
theorem safeRuntime_block_13585 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13585) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13585_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 13596) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11548) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11548)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13585_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13585) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13585_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13585 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13596`. -/
def safeRuntime_block_13596_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.ofNat 13612) :: (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 32)).toNat 32)) :: x1 :: x2 :: x0 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13596. -/
theorem safeRuntime_block_13596 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13596) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13596_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (R := R)) mem aw rdata σ (k + 11) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 13612) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 11548) (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11548)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13596_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13596) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13596_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13596 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13612`. -/
def safeRuntime_block_13612_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) :: (UInt256.ofNat 13628) :: (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) :: x1 :: x0 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13612. -/
theorem safeRuntime_block_13612 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13612) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13612_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 11) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 13628) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 11548) (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11548)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13612_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13612) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13612_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13612 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13628`. -/
def safeRuntime_block_13628_stack {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13628. -/
theorem safeRuntime_block_13628 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13628) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x6 (safeRuntime_block_13628_stack (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 11) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.swap3 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.swap3 (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13628_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13628) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x6 (safeRuntime_block_13628_stack (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13628 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13639_taken`. -/
def safeRuntime_block_13639_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13639. -/
theorem safeRuntime_block_13639_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13657) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13657) (safeRuntime_block_13639_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 12) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.dup7 (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.slt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 13657) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13657)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13639_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13657) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13657) (safeRuntime_block_13639_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13639_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13639_fallthrough`. -/
def safeRuntime_block_13639_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13639. -/
theorem safeRuntime_block_13639_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13654) (safeRuntime_block_13639_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 12) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.dup7 (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.slt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 13657) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13654)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13639_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13654) (safeRuntime_block_13639_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13639_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13654. -/
theorem safeRuntime_block_13654 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13654) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_13657`. -/
def safeRuntime_block_13657_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x3.toNat 32)) :: (UInt256.ofNat 13668) :: (uInt256OfByteArray (ee.calldata.readBytes x3.toNat 32)) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13657. -/
theorem safeRuntime_block_13657 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13657) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13657_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 13668) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11548) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11548)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13657_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13657) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13657_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13657 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13668_taken`. -/
def safeRuntime_block_13668_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) :: x1 :: (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 32)).toNat 32)) :: x0 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13668. -/
theorem safeRuntime_block_13668_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13702) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13668) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13702) (safeRuntime_block_13668_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem aw rdata σ (k + 19) (C + ((60))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.calldataload (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 13702) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13702)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13668_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13702) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13668) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13702) (safeRuntime_block_13668_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13668_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13668_fallthrough`. -/
def safeRuntime_block_13668_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) :: x1 :: (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 32)).toNat 32)) :: x0 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13668. -/
theorem safeRuntime_block_13668_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13668) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13699) (safeRuntime_block_13668_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem aw rdata σ (k + 19) (C + ((60))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.calldataload (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 13702) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13699)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13668_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 64)).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13668) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13699) (safeRuntime_block_13668_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13668_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13699. -/
theorem safeRuntime_block_13699 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13699) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_13702`. -/
def safeRuntime_block_13702_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x4 + x0) :: x5 :: (UInt256.ofNat 13714) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13702. -/
theorem safeRuntime_block_13702 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11753) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11753) (safeRuntime_block_13702_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata σ (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 13714) (by native_decide) (by evm_ov)
  have r3 := r2.dup7 (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup8 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 11753) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11753)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13702_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11753) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11753) (safeRuntime_block_13702_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13702 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13714`. -/
def safeRuntime_block_13714_stack {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13714. -/
theorem safeRuntime_block_13714 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x7 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13714) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x7 (safeRuntime_block_13714_stack (x0 := x0) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 10) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.swap3 (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.swap3 (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13714_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x7 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13714) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x7 (safeRuntime_block_13714_stack (x0 := x0) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13714 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13724_taken`. -/
def safeRuntime_block_13724_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13724. -/
theorem safeRuntime_block_13724_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13742) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13724) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13742) (safeRuntime_block_13724_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 12) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.dup7 (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.slt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 13742) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13742)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13724_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 13742) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13724) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13742) (safeRuntime_block_13724_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13724_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13724_fallthrough`. -/
def safeRuntime_block_13724_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13724. -/
theorem safeRuntime_block_13724_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13724) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13739) (safeRuntime_block_13724_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 12) (C + ((38))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.dup7 (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.slt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 13742) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13739)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13724_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 96))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13724) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13739) (safeRuntime_block_13724_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13724_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 13739. -/
theorem safeRuntime_block_13739 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13739) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.Runs1e6.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_13742`. -/
def safeRuntime_block_13742_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x3.toNat 32)) :: (UInt256.ofNat 13753) :: (uInt256OfByteArray (ee.calldata.readBytes x3.toNat 32)) :: x0 :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13742. -/
theorem safeRuntime_block_13742 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13742) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13742_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 13753) (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11548) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11548)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13742_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13742) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13742_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13742 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13753`. -/
def safeRuntime_block_13753_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.ofNat 13769) :: (uInt256OfByteArray (ee.calldata.readBytes (x4 + (UInt256.ofNat 32)).toNat 32)) :: x1 :: x2 :: x0 :: x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13753. -/
theorem safeRuntime_block_13753 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13753) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13753_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (R := R)) mem aw rdata σ (k + 11) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 13769) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 11548) (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11548)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13753_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains (UInt256.ofNat 11548) = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13753) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 11548) (safeRuntime_block_13753_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13753 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_13769`. -/
def safeRuntime_block_13769_stack {ee : ExecutionEnv} {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 64) + x4).toNat 32)) :: x0 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 13769. -/
theorem safeRuntime_block_13769 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13769) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x6 (safeRuntime_block_13769_stack (ee := ee) (x0 := x0) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 16) (C + ((48))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap6 (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.swap5 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.swap2 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.calldataload (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r16 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_13769_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.Runs1e6.safeBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 (UInt256.ofNat 13769) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.Runs1e6.safeBytecode ee g s0 x6 (safeRuntime_block_13769_stack (ee := ee) (x0 := x0) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_13769 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.Runs1e6.RuntimeBlocks
