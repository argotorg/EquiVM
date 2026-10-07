import Reasoning.Reach
import Benchmarks.Safe.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace safeRuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_9744`. -/
def safeRuntime_block_9744_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_9744`. -/
def safeRuntime_block_9744_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((memLoad (x0 + x1) mem).toByteArray.write 0 mem (x0 + x2).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9744. -/
theorem safeRuntime_block_9744 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9735) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9744) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9735) (safeRuntime_block_9744_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_9744_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x0 + x2) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((41) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x0 + x2) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 9735) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9735)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9744_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9735) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9744) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9735) (safeRuntime_block_9744_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_9744_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9744 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9759`. -/
def safeRuntime_block_9759_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `safeRuntime_block_9759`. -/
def safeRuntime_block_9759_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (x3 + x2).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9759. -/
theorem safeRuntime_block_9759 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9759) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 x4 (safeRuntime_block_9759_stack (R := R)) (safeRuntime_block_9759_memory (mem := mem) (x2 := x2) (x3 := x3)) (M aw (x3 + x2) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((24) + (memExpansionCost aw (x3 + x2) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9759_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9759) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x4 (safeRuntime_block_9759_stack (R := R)) (safeRuntime_block_9759_memory (mem := mem) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9759 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9767`. -/
def safeRuntime_block_9767_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 32)) :: (x1 + (UInt256.ofNat 32)) :: (memLoad x0 mem) :: (UInt256.ofNat 9790) :: (memLoad x0 mem) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_9767`. -/
def safeRuntime_block_9767_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9767. -/
theorem safeRuntime_block_9767 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9733) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9767) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9733) (safeRuntime_block_9767_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_9767_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((53) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 9790) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.dup7 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := r13.dup7 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 9733) (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9733)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9767_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9733) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9767) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9733) (safeRuntime_block_9767_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_9767_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9767 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9790`. -/
def safeRuntime_block_9790_stack {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + ((UInt256.land (UInt256.lnot (UInt256.ofNat 31)) ((UInt256.ofNat 31) + x0)) + x3)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9790. -/
theorem safeRuntime_block_9790 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9790) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 x4 (safeRuntime_block_9790_stack (x0 := x0) (x3 := x3) (R := R)) mem aw rdata σ (k + 17) (C + ((52))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r5 := r4.not (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.swap3 (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.swap3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.swap3 (by native_decide) (by evm_ov)
  have r14 := r13.swap2 (by native_decide) (by evm_ov)
  have r15 := r14.pop (by native_decide) (by evm_ov)
  have r16 := r15.pop (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9790_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9790) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x4 (safeRuntime_block_9790_stack (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9790 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9810`. -/
def safeRuntime_block_9810_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (x0 + (UInt256.ofNat 64)) :: (UInt256.ofNat 9836) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_9810`. -/
def safeRuntime_block_9810_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 64).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero x2)).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9810. -/
theorem safeRuntime_block_9810 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9767) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9810) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9767) (safeRuntime_block_9810_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_9810_memory (mem := mem) (x0 := x0) (x2 := x2)) (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((59) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 9836) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.dup4 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup5 (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 9767) (by native_decide) (by evm_ov)
  have r19 := r18.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9767)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9810_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9767) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9810) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9767) (safeRuntime_block_9810_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_9810_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9810 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9836`. -/
def safeRuntime_block_9836_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9836. -/
theorem safeRuntime_block_9836 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x5 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9836) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 x5 (safeRuntime_block_9836_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap5 (by native_decide) (by evm_ov)
  have r3 := r2.swap4 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9836_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x5 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9836) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x5 (safeRuntime_block_9836_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9836 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9844_taken`. -/
def safeRuntime_block_9844_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9844. -/
theorem safeRuntime_block_9844_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9861) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9844) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9861) (safeRuntime_block_9844_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((36))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 9861) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9861)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9844_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9861) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9844) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9861) (safeRuntime_block_9844_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9844_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9844_fallthrough`. -/
def safeRuntime_block_9844_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9844. -/
theorem safeRuntime_block_9844_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9844) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9858) (safeRuntime_block_9844_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((36))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 9861) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9858)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9844_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9844) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9858) (safeRuntime_block_9844_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9844_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9858. -/
theorem safeRuntime_block_9858 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9858) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9861`. -/
def safeRuntime_block_9861_stack {ee : ExecutionEnv} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x2 + (UInt256.ofNat 32)).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9861. -/
theorem safeRuntime_block_9861 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9861) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 x4 (safeRuntime_block_9861_stack (ee := ee) (x2 := x2) (R := R)) mem aw rdata σ (k + 14) (C + ((42))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.calldataload (by native_decide) (by evm_ov)
  have r6 := r5.swap3 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.calldataload (by native_decide) (by evm_ov)
  have r12 := r11.swap2 (by native_decide) (by evm_ov)
  have r13 := r12.pop (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r14 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9861_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9861) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x4 (safeRuntime_block_9861_stack (ee := ee) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9861 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9876`. -/
def safeRuntime_block_9876_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (x0 + (UInt256.ofNat 32)) :: (UInt256.ofNat 6891) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_9876`. -/
def safeRuntime_block_9876_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 9876. -/
theorem safeRuntime_block_9876 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9767) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9876) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9767) (safeRuntime_block_9876_stack (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_9876_memory (mem := mem) (x0 := x0)) (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((38) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 6891) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.dup5 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 9767) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9767)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9876_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9767) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9876) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9767) (safeRuntime_block_9876_stack (x0 := x0) (x1 := x1) (R := R)) (safeRuntime_block_9876_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9876 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9894_taken`. -/
def safeRuntime_block_9894_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9894. -/
theorem safeRuntime_block_9894_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9910) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9910) (safeRuntime_block_9894_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 9910) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9910)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9894_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9910) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9910) (safeRuntime_block_9894_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9894_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9894_fallthrough`. -/
def safeRuntime_block_9894_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9894. -/
theorem safeRuntime_block_9894_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9907) (safeRuntime_block_9894_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 9910) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9907)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9894_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9907) (safeRuntime_block_9894_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9894_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9907. -/
theorem safeRuntime_block_9907 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9907) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9910`. -/
def safeRuntime_block_9910_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 9910. -/
theorem safeRuntime_block_9910 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x3 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9910) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 x3 (safeRuntime_block_9910_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((22))) := by
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
theorem safeRuntime_block_9910_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains x3 = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9910) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 x3 (safeRuntime_block_9910_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9910 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9917_taken`. -/
def safeRuntime_block_9917_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9917. -/
theorem safeRuntime_block_9917_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9944) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9917) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9944) (safeRuntime_block_9917_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 20) (C + ((54))) := by
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
  have r19 := r18.push2 (UInt256.ofNat 9944) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9944)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9917_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9944) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9917) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9944) (safeRuntime_block_9917_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9917_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9917_fallthrough`. -/
def safeRuntime_block_9917_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9917. -/
theorem safeRuntime_block_9917_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9917) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9941) (safeRuntime_block_9917_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 20) (C + ((54))) := by
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
  have r19 := r18.push2 (UInt256.ofNat 9944) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9941)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9917_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 320))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9917) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9941) (safeRuntime_block_9917_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9917_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 9941. -/
theorem safeRuntime_block_9941 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9941) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_9944`. -/
def safeRuntime_block_9944_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x11 :: (UInt256.ofNat 9953) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9944. -/
theorem safeRuntime_block_9944 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9096) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9944) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9096) (safeRuntime_block_9944_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 9953) (by native_decide) (by evm_ov)
  have r3 := r2.dup13 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 9096) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9096)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9944_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9096) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9944) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9096) (safeRuntime_block_9944_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9944 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_9953_taken`. -/
def safeRuntime_block_9953_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 32)).toNat 32)) :: x0 :: x12 :: R)

/-- Automatically generated RD summary for bytecode block at pc 9953. -/
theorem safeRuntime_block_9953_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9986) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9953) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9986) (safeRuntime_block_9953_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (R := R)) mem aw rdata σ (k + 23) (C + ((72))) := by
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
  have r22 := r21.push2 (UInt256.ofNat 9986) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9986)) r23 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_9953_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x12 + (UInt256.ofNat 64)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 9986) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9953) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 9986) (safeRuntime_block_9953_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x12 := x12) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_9953_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end safeRuntimeBlocks
