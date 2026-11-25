import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_19055`. -/
def midnight_block_19055_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: (UInt256.ofNat 19066) :: x0 :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 19055. -/
theorem midnight_block_19055 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19016) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19055) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19016) (midnight_block_19055_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19066) (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19016) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19016)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19055_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19016) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19055) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19016) (midnight_block_19055_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19055 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19066`. -/
def midnight_block_19066_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: x0 :: (UInt256.ofNat 19080) :: x3 :: x1 :: x2 :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 19066. -/
theorem midnight_block_19066 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19066) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_19066_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 19080) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.swap5 (by native_decide) (by evm_ov)
  have r7 := r6.dup6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19066_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18444) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19066) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18444) (midnight_block_19066_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19066 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19080_taken`. -/
def midnight_block_19080_taken_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `midnight_block_19080_taken`. -/
def midnight_block_19080_taken_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem x3.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 19080. -/
theorem midnight_block_19080_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt ((x1 + x2) + (UInt256.ofNat 32)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19080) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_19080_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_19080_taken_memory (mem := mem) (x2 := x2) (x3 := x3)) (M aw x3 (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((41) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.gt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6350)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19080_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt ((x1 + x2) + (UInt256.ofNat 32)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19080) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_19080_taken_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_19080_taken_memory (mem := mem) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19080_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19080_fallthrough`. -/
def midnight_block_19080_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `midnight_block_19080_fallthrough`. -/
def midnight_block_19080_fallthrough_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem x3.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 19080. -/
theorem midnight_block_19080_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt ((x1 + x2) + (UInt256.ofNat 32)) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19080) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19095) (midnight_block_19080_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_19080_fallthrough_memory (mem := mem) (x2 := x2) (x3 := x3)) (M aw x3 (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((41) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.gt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19095)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19080_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt ((x1 + x2) + (UInt256.ofNat 32)) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19080) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19095) (midnight_block_19080_fallthrough_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_19080_fallthrough_memory (mem := mem) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19080_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19095`. -/
def midnight_block_19095_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Final memory for bytecode block summary `midnight_block_19095`. -/
def midnight_block_19095_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (ee.calldata.write (x0 + (UInt256.ofNat 32)).toNat mem (x2 + (UInt256.ofNat 32)).toNat x1.toNat) ((x2 + x1) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 19095. -/
theorem midnight_block_19095 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19095) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x3 (midnight_block_19095_stack (x2 := x2) (R := R)) (midnight_block_19095_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M aw (x2 + (UInt256.ofNat 32)) x1) ((x2 + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((52) + (memExpansionCost aw (x2 + (UInt256.ofNat 32)) x1) + (3 + 3 * ((x1.toNat + 31) / 32)) + (memExpansionCost (M aw (x2 + (UInt256.ofNat 32)) x1) ((x2 + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.swap4 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.dup7 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genCalldatacopy r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19095_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x3 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19095) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x3 (midnight_block_19095_stack (x2 := x2) (R := R)) (midnight_block_19095_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19095 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19113_taken`. -/
def midnight_block_19113_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 19113. -/
theorem midnight_block_19113_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_19113_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6350)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19113_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_19113_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19113_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19113_fallthrough`. -/
def midnight_block_19113_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 19113. -/
theorem midnight_block_19113_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19132) (midnight_block_19113_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((47))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19132)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19113_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19132) (midnight_block_19113_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19113_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19132`. -/
def midnight_block_19132_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 19132. -/
theorem midnight_block_19132 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19132) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_19132_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19132_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19132) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_19132_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19132 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19133_taken`. -/
def midnight_block_19133_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 19133. -/
theorem midnight_block_19133_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19161) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19133) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19161) (midnight_block_19133_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 19161) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19161)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19133_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19161) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19133) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19161) (midnight_block_19133_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19133_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19133_fallthrough`. -/
def midnight_block_19133_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 19133. -/
theorem midnight_block_19133_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19133) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19146) (midnight_block_19133_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 19161) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19146)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19133_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x1 (UInt256.ofNat 7))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19133) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19146) (midnight_block_19133_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19133_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19146`. -/
def midnight_block_19146_stack {x0 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.shiftLeft x2 (UInt256.ofNat 1)) (UInt256.ofNat 30)) :: ((UInt256.shiftRight x2 (UInt256.ofNat 4)) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 19146. -/
theorem midnight_block_19146 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19146) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_19146_stack (x0 := x0) (x2 := x2) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 30) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.swap3 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r12 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19146_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19146) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_19146_stack (x0 := x0) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19146 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 19161. -/
theorem midnight_block_19161 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19161) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
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

/-- Final stack for bytecode block summary `midnight_block_19181`. -/
def midnight_block_19181_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (memLoad (memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)) ((UInt256.ofNat 256).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) :: ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 32)) :: x0 :: x1 :: (x1 + (UInt256.ofNat 288)) :: R)

/-- Final memory for bytecode block summary `midnight_block_19181`. -/
def midnight_block_19181_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad (memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)) ((UInt256.ofNat 256).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 256).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32) (x1 + (UInt256.ofNat 256)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 19181. -/
theorem midnight_block_19181 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (midnight_block_19181_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_19181_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) rdata σ (k + 61) (C + ((180) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := RD.genMload r18 (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r22 := r21.dup4 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r28 := r27.shl (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r31 := r30.dup3 (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := RD.genMload r32 (by native_decide) (by evm_ov)
  have r34 := r33.and (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r36 := r35.dup4 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r40 := r39.dup2 (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := RD.genMload r41 (by native_decide) (by evm_ov)
  have r43 := r42.swap3 (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r46 := r45.dup5 (by native_decide) (by evm_ov)
  have r47 := r46.add (by native_decide) (by evm_ov)
  have r48 := RD.genMstore r47 (by native_decide) (by evm_ov)
  have r49 := r48.dup4 (by native_decide) (by evm_ov)
  have r50 := RD.genMload r49 (by native_decide) (by evm_ov)
  have r51 := r50.dup1 (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := RD.genMstore r52 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r55 := r54.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r56 := r55.dup5 (by native_decide) (by evm_ov)
  have r57 := r56.add (by native_decide) (by evm_ov)
  have r58 := r57.swap5 (by native_decide) (by evm_ov)
  have r59 := r58.add (by native_decide) (by evm_ov)
  have r60 := r59.swap1 (by native_decide) (by evm_ov)
  have r61 := r60.push0 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19261)) r61 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19181_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (midnight_block_19181_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_19181_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19181 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 19261. -/
theorem midnight_block_19261_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19324) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19324) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 19324) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19324)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19261_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19324) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19324) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19261_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 19261. -/
theorem midnight_block_19261_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19269) (x0 :: x1 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 19324) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19269)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19261_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19269) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19261_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19269`. -/
def midnight_block_19269_stack {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: R)

/-- Final memory for bytecode block summary `midnight_block_19269`. -/
def midnight_block_19269_memory {mem : ByteArray} {x3 : UInt256} {x4 : UInt256} : ByteArray :=
  ((UInt256.land (memLoad (x3 + (UInt256.ofNat 224)) ((UInt256.land (memLoad (x3 + (UInt256.ofNat 192)) ((memLoad (x3 + (UInt256.ofNat 160)) ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32) (x4 + (UInt256.ofNat 160)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (x3 + (UInt256.ofNat 160)) ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32) (x4 + (UInt256.ofNat 160)).toNat 32) (x4 + (UInt256.ofNat 192)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x3 + (UInt256.ofNat 192)) ((memLoad (x3 + (UInt256.ofNat 160)) ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32) (x4 + (UInt256.ofNat 160)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad (x3 + (UInt256.ofNat 160)) ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((memLoad (x3 + (UInt256.ofNat 128)) mem).toByteArray.write 0 mem (x4 + (UInt256.ofNat 128)).toNat 32) (x4 + (UInt256.ofNat 160)).toNat 32) (x4 + (UInt256.ofNat 192)).toNat 32) (x4 + (UInt256.ofNat 224)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 19269. -/
theorem midnight_block_19269 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19269) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x6 (midnight_block_19269_stack (x5 := x5) (R := R)) (midnight_block_19269_memory (mem := mem) (x3 := x3) (x4 := x4)) (M (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 45) (C + ((137) + (memExpansionCost aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.swap5 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r17 := r16.dup7 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.genMload r22 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r25 := r24.dup7 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.dup3 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r30 := r29.dup3 (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have r33 := r32.and (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r35 := r34.dup7 (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := RD.genMstore r36 (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := RD.genMload r38 (by native_decide) (by evm_ov)
  have r40 := r39.and (by native_decide) (by evm_ov)
  have r41 := r40.swap2 (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := RD.genMstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.swap1 (by native_decide) (by evm_ov)
  have r45 := r44.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r45 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19269_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19269) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x6 (midnight_block_19269_stack (x5 := x5) (R := R)) (midnight_block_19269_memory (mem := mem) (x3 := x3) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19269 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19324`. -/
def midnight_block_19324_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 1)) :: x1 :: (x2 + (UInt256.ofNat 32)) :: x3 :: x4 :: (x5 + (UInt256.ofNat 128)) :: R)

/-- Final memory for bytecode block summary `midnight_block_19324`. -/
def midnight_block_19324_memory {mem : ByteArray} {x2 : UInt256} {x5 : UInt256} : ByteArray :=
  ((UInt256.land (memLoad ((memLoad x2 mem) + (UInt256.ofNat 96)) ((memLoad ((memLoad x2 mem) + (UInt256.ofNat 64)) ((memLoad ((memLoad x2 mem) + (UInt256.ofNat 32)) ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32) (x5 + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad x2 mem) + (UInt256.ofNat 32)) ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32) (x5 + (UInt256.ofNat 32)).toNat 32) (x5 + (UInt256.ofNat 64)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((memLoad ((memLoad x2 mem) + (UInt256.ofNat 64)) ((memLoad ((memLoad x2 mem) + (UInt256.ofNat 32)) ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32) (x5 + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad ((memLoad x2 mem) + (UInt256.ofNat 32)) ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (memLoad x2 mem) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem x5.toNat 32) (x5 + (UInt256.ofNat 32)).toNat 32) (x5 + (UInt256.ofNat 64)).toNat 32) (x5 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 19324. -/
theorem midnight_block_19324 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19261) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19324) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (midnight_block_19324_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_19324_memory (mem := mem) (x2 := x2) (x5 := x5)) (M (M (M (M (M (M (M (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 55) (C + ((168) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x2 (⟨32⟩ : UInt256)) (memLoad x2 mem) (⟨32⟩ : UInt256)) x5 (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad x2 mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.swap5 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r15 := r14.dup11 (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.dup2 (by native_decide) (by evm_ov)
  have r19 := RD.genMload r18 (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.dup5 (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.dup6 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.dup7 (by native_decide) (by evm_ov)
  have r28 := r27.dup6 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r32 := r31.dup2 (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := RD.genMload r33 (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r36 := r35.dup6 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r43 := r42.dup3 (by native_decide) (by evm_ov)
  have r44 := r43.add (by native_decide) (by evm_ov)
  have r45 := RD.genMstore r44 (by native_decide) (by evm_ov)
  have r46 := r45.add (by native_decide) (by evm_ov)
  have r47 := r46.swap7 (by native_decide) (by evm_ov)
  have r48 := r47.add (by native_decide) (by evm_ov)
  have r49 := r48.swap2 (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := r50.swap2 (by native_decide) (by evm_ov)
  have r52 := r51.swap1 (by native_decide) (by evm_ov)
  have r53 := r52.swap2 (by native_decide) (by evm_ov)
  have r54 := r53.push2 (UInt256.ofNat 19261) (by native_decide) (by evm_ov)
  have r55 := r54.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19261)) r55 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19324_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19261) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19324) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19261) (midnight_block_19324_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_19324_memory (mem := mem) (x2 := x2) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19324 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 19391. -/
theorem midnight_block_19391_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19401) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19401) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19401) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19401)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19391_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19401) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19401) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19391_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 19391. -/
theorem midnight_block_19391_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19398) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19401) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19398)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19391_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19398) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19391_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_19398`. -/
def midnight_block_19398_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 19398. -/
theorem midnight_block_19398 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19398) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x2 (midnight_block_19398_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.div (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_19398_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19398) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x2 (midnight_block_19398_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_19398 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
