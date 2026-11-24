import Reasoning.Reach
import Benchmarks.Safe.V0_cdb2eb5.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_11066`. -/
def safeRuntime_block_11066_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 2759) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11066. -/
theorem safeRuntime_block_11066 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11010) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11066) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11010) (safeRuntime_block_11066_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 2759) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11010) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11010)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11066_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11010) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11066) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11010) (safeRuntime_block_11066_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11066 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11073. -/
theorem safeRuntime_block_11073 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11073) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1313373041) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 33) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r11 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 11093. -/
theorem safeRuntime_block_11093_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11121) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11093) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11121) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11121) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11121)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11093_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11121) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11093) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11121) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11093_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11093. -/
theorem safeRuntime_block_11093_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 2)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11093) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11102) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11121) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11102)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11093_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.lt x0 (UInt256.ofNat 2)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11093) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11102) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11093_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11102. -/
theorem safeRuntime_block_11102 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11102) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1313373041) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 33) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r10 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_11121`. -/
def safeRuntime_block_11121_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `safeRuntime_block_11121`. -/
def safeRuntime_block_11121_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11121. -/
theorem safeRuntime_block_11121 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11121) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x2 (safeRuntime_block_11121_stack (R := R)) (safeRuntime_block_11121_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((15) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11121_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11121) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x2 (safeRuntime_block_11121_stack (R := R)) (safeRuntime_block_11121_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11121 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11125`. -/
def safeRuntime_block_11125_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  (x8 :: (x0 + (UInt256.ofNat 96)) :: (UInt256.ofNat 11200) :: (x0 + (UInt256.land (x9 + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_11125`. -/
def safeRuntime_block_11125_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (ee.calldata.write x10.toNat (x9.toByteArray.write 0 ((UInt256.ofNat 352).toByteArray.write 0 (x11.toByteArray.write 0 ((UInt256.land x12 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) (x0 + (UInt256.ofNat 64)).toNat 32) (x0 + (UInt256.ofNat 352)).toNat 32) (x0 + (UInt256.ofNat 384)).toNat x9.toNat) ((x0 + x9) + (UInt256.ofNat 384)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11125. -/
theorem safeRuntime_block_11125 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11093) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11125) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11093) (safeRuntime_block_11125_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (safeRuntime_block_11125_memory (ee := ee) (mem := mem) (x0 := x0) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12)) (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 384)) x9) ((x0 + x9) + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) rdata σ (k + 57) (C + ((169) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 384)) x9) + (3 + 3 * ((x9.toNat + 31) / 32)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 384)) x9) ((x0 + x9) + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup14 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup13 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.dup11 (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := r28.dup10 (by native_decide) (by evm_ov)
  have r30 := r29.dup12 (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r32 := r31.dup4 (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := RD.genCalldatacopy r33 (by native_decide) (by evm_ov)
  have r35 := r34.push0 (by native_decide) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r37 := r36.dup12 (by native_decide) (by evm_ov)
  have r38 := r37.dup4 (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := RD.genMstore r40 (by native_decide) (by evm_ov)
  have r42 := r41.push0 (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r44 := r43.not (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r46 := r45.dup13 (by native_decide) (by evm_ov)
  have r47 := r46.add (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.dup3 (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 11200) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r53 := r52.dup5 (by native_decide) (by evm_ov)
  have r54 := r53.add (by native_decide) (by evm_ov)
  have r55 := r54.dup13 (by native_decide) (by evm_ov)
  have r56 := r55.push2 (UInt256.ofNat 11093) (by native_decide) (by evm_ov)
  have r57 := r56.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11093)) r57 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11125_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11093) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11125) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11093) (safeRuntime_block_11125_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (safeRuntime_block_11125_memory (ee := ee) (mem := mem) (x0 := x0) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11125 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_11200`. -/
def safeRuntime_block_11200_memory {mem : ByteArray} {x2 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x6).toByteArray.write 0 (x7.toByteArray.write 0 (x8.toByteArray.write 0 (x9.toByteArray.write 0 mem (x2 + (UInt256.ofNat 128)).toNat 32) (x2 + (UInt256.ofNat 160)).toNat 32) (x2 + (UInt256.ofNat 192)).toNat 32) (x2 + (UInt256.ofNat 224)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11200. -/
theorem safeRuntime_block_11200 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11239) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11200) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11239) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) (safeRuntime_block_11200_memory (mem := mem) (x2 := x2) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9)) (M (M (M (M aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 30) (C + ((93) + (memExpansionCost aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x2 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup10 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup9 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup8 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r14 := r13.dup5 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 11239) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r19 := r18.dup5 (by native_decide) (by evm_ov)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := r20.dup9 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.sub (by native_decide) (by evm_ov)
  have r27 := r26.and (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := RD.genMstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11239)) r30 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11200_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11239) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11200) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11239) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) (safeRuntime_block_11200_memory (mem := mem) (x2 := x2) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11200 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11239`. -/
def safeRuntime_block_11239_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: (x0 + (UInt256.ofNat 384)) :: (UInt256.ofNat 11282) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_11239`. -/
def safeRuntime_block_11239_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x5 : UInt256} : ByteArray :=
  (((UInt256.sub x0 x2) + (UInt256.ofNat 384)).toByteArray.write 0 ((UInt256.land x5 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x2 + (UInt256.ofNat 256)).toNat 32) (x2 + (UInt256.ofNat 288)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11239. -/
theorem safeRuntime_block_11239 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9612) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11239) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9612) (safeRuntime_block_11239_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (safeRuntime_block_11239_memory (mem := mem) (x0 := x0) (x2 := x2) (x5 := x5)) (M (M aw (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((87) + (memExpansionCost aw (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x2 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup7 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r10 := r9.dup5 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r19 := r18.dup5 (by native_decide) (by evm_ov)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 11282) (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.dup7 (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 9612) (by native_decide) (by evm_ov)
  have r28 := r27.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9612)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11239_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 9612) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11239) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 9612) (safeRuntime_block_11239_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (safeRuntime_block_11239_memory (mem := mem) (x0 := x0) (x2 := x2) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11239 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11282`. -/
def safeRuntime_block_11282_stack {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_11282`. -/
def safeRuntime_block_11282_memory {mem : ByteArray} {x3 : UInt256} {x4 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4).toByteArray.write 0 mem (x3 + (UInt256.ofNat 320)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11282. -/
theorem safeRuntime_block_11282 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11307) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11282) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11307) (safeRuntime_block_11282_stack (x0 := x0) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_11282_memory (mem := mem) (x3 := x3) (x4 := x4)) (M aw (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((55) + (memExpansionCost aw (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11307) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r13 := r12.shl (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11307)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11282_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11307) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11282) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11307) (safeRuntime_block_11282_stack (x0 := x0) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_11282_memory (mem := mem) (x3 := x3) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11282 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11307`. -/
def safeRuntime_block_11307_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11307. -/
theorem safeRuntime_block_11307 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x14 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11307) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x14 (safeRuntime_block_11307_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 17) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap14 (by native_decide) (by evm_ov)
  have r3 := r2.swap13 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.pop (by native_decide) (by evm_ov)
  have r12 := r11.pop (by native_decide) (by evm_ov)
  have r13 := r12.pop (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.pop (by native_decide) (by evm_ov)
  have r16 := r15.pop (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11307_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x14 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11307) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x14 (safeRuntime_block_11307_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11307 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11324_taken`. -/
def safeRuntime_block_11324_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + x0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11324. -/
theorem safeRuntime_block_11324_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (x1 + x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 2759) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11324) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 2759) (safeRuntime_block_11324_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := r6.gt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2759) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2759)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11324_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (x1 + x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 2759) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11324) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 2759) (safeRuntime_block_11324_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11324_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11324_fallthrough`. -/
def safeRuntime_block_11324_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + x0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11324. -/
theorem safeRuntime_block_11324_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (x1 + x0))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11324) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11336) (safeRuntime_block_11324_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := r6.gt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2759) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11336)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11324_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (x1 + x0))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11324) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11336) (safeRuntime_block_11324_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11324_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11336`. -/
def safeRuntime_block_11336_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 2759) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11336. -/
theorem safeRuntime_block_11336 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11010) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11336) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11010) (safeRuntime_block_11336_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 2759) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11010) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11010)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11336_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11010) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11336) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11010) (safeRuntime_block_11336_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11336 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11343_taken`. -/
def safeRuntime_block_11343_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11343. -/
theorem safeRuntime_block_11343_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11369) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11343) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11369) (safeRuntime_block_11343_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11369) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11369)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11343_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11369) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11343) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11369) (safeRuntime_block_11343_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11343_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11343_fallthrough`. -/
def safeRuntime_block_11343_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11343. -/
theorem safeRuntime_block_11343_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11343) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11350) (safeRuntime_block_11343_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11369) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11350)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11343_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11343) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11350) (safeRuntime_block_11343_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11343_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11350. -/
theorem safeRuntime_block_11350 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11350) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 1313373041) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r3 := r2.shl (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r10 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_11369`. -/
def safeRuntime_block_11369_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x1 x2) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11369. -/
theorem safeRuntime_block_11369 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11369) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x3 (safeRuntime_block_11369_stack (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.div (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11369_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11369) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x3 (safeRuntime_block_11369_stack (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11369 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11374. -/
theorem safeRuntime_block_11374 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11374) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1313373041) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 50) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r11 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_11394`. -/
def safeRuntime_block_11394_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (x0 + (UInt256.ofNat 160)) :: x5 :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_11394`. -/
def safeRuntime_block_11394_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  (x4.toByteArray.write 0 ((UInt256.ofNat 128).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 128)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11394. -/
theorem safeRuntime_block_11394 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11394) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11412) (safeRuntime_block_11394_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (safeRuntime_block_11394_memory (mem := mem) (x0 := x0) (x4 := x4)) (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((45) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.dup6 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := r11.dup7 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11412)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11394_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11394) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11412) (safeRuntime_block_11394_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (safeRuntime_block_11394_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11394 hstack h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks
