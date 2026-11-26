import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.EAS.Attester.Immutables
import Benchmarks.EAS.Attester.CreationBytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace attesterCreationBlocks

set_option maxRecDepth 10000

private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.EAS.Attester.attesterCreationBytecode

/-- Final stack for bytecode block summary `attesterCreation_block_0_taken`. -/
def attesterCreation_block_0_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `attesterCreation_block_0_taken`. -/
def attesterCreation_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 160).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem attesterCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (attesterCreation_block_0_taken_stack (ee := ee) (R := R)) (attesterCreation_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 0) rfl
  have r1 := r0.push1 (UInt256.ofNat 160) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMstore r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.callvalue d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.iszero d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 15) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.jumpiT d7.head hcond (Benchmarks.EAS.Attester.CreationBytecode.jumpdest_code tail (t := 15) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_0_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (attesterCreation_block_0_taken_stack (ee := ee) (R := R)) (attesterCreation_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_0_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_0_fallthrough`. -/
def attesterCreation_block_0_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `attesterCreation_block_0_fallthrough`. -/
def attesterCreation_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 160).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem attesterCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) (attesterCreation_block_0_fallthrough_stack (ee := ee) (R := R)) (attesterCreation_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 0) rfl
  have r1 := r0.push1 (UInt256.ofNat 160) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMstore r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.callvalue d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.iszero d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 15) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.jumpiNT d7.head hcond (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_0_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) (attesterCreation_block_0_fallthrough_stack (ee := ee) (R := R)) (attesterCreation_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11. -/
theorem attesterCreation_block_11 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 0) rfl).drop 8 11 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterCreation_block_15`. -/
def attesterCreation_block_15_stack {tail : ByteArray} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) :: (UInt256.ofNat 44) :: R)

/-- Final memory for bytecode block summary `attesterCreation_block_15`. -/
def attesterCreation_block_15_memory {tail : ByteArray} {mem : ByteArray} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))).toByteArray.write 0 ((Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).write (UInt256.ofNat 4057).toNat mem (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057)).toNat) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem attesterCreation_block_15 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (attesterCreation_block_15_stack (tail := tail) (mem := mem) (R := R)) (attesterCreation_block_15_memory (tail := tail) (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((61) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) + (3 + 3 * (((UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057)).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.sub (UInt256.ofNat (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).size) (UInt256.ofNat 4057))) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 15) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 64) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push2 (UInt256.ofNat 4057) d4.head (by evm_ov)
  have d5 := d4.next 3 rfl
  have r6 := r5.codesize d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.sub d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push2 (UInt256.ofNat 4057) d8.head (by evm_ov)
  have d9 := d8.next 3 rfl
  have r10 := r9.dup4 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := RD.genCodecopy r10 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.add d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 64) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.swap1 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := RD.genMstore r16 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.push1 (UInt256.ofNat 44) d17.head (by evm_ov)
  have d18 := d17.next 2 rfl
  have r19 := r18.swap2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.push1 (UInt256.ofNat 98) d19.head (by evm_ov)
  have d20 := d19.next 2 rfl
  have r21 := r20.jump d20.head (Benchmarks.EAS.Attester.CreationBytecode.jumpdest_code tail (t := 98) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r21 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_15_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (attesterCreation_block_15_stack (tail := tail) (mem := mem) (R := R)) (attesterCreation_block_15_memory (tail := tail) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_15 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 44. -/
theorem attesterCreation_block_44_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 44) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 1) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 1) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.push1 (UInt256.ofNat 160) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.shl d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.sub d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.dup2 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.and d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 82) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.jumpiT d9.head hcond (Benchmarks.EAS.Attester.CreationBytecode.jumpdest_code tail (t := 82) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_44_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_44_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 44. -/
theorem attesterCreation_block_44_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 44) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 1) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 1) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.push1 (UInt256.ofNat 160) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.shl d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.sub d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.dup2 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.and d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 82) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.jumpiNT d9.head hcond (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_44_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 44) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 58) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_44_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 58. -/
theorem attesterCreation_block_58 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 58) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 44) rfl).drop 10 58 rfl
  have r1 := r0.push1 (UInt256.ofNat 64) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push4 (UInt256.ofNat 1102841855) d2.head (by evm_ov)
  have d3 := d2.next 5 rfl
  have r4 := r3.push1 (UInt256.ofNat 225) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.shl d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup2 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 4) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.add d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 64) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := RD.genMload r10 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup1 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.swap2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.sub d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.swap1 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  exact RD.genRev r15 d15.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterCreation_block_82`. -/
def attesterCreation_block_82_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `attesterCreation_block_82`. -/
def attesterCreation_block_82_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0).toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 82. -/
theorem attesterCreation_block_82 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 144) (attesterCreation_block_82_stack (R := R)) (attesterCreation_block_82_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((36) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 82) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 1) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 1) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.push1 (UInt256.ofNat 160) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.shl d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.sub d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.and d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 128) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 144) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := r10.jump d10.head (Benchmarks.EAS.Attester.CreationBytecode.jumpdest_code tail (t := 144) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_82_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 82) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 144) (attesterCreation_block_82_stack (R := R)) (attesterCreation_block_82_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_82 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_98_taken`. -/
def attesterCreation_block_98_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 98. -/
theorem attesterCreation_block_98_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (attesterCreation_block_98_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 98) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 32) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.dup3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup5 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.sub d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.slt d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.iszero d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 115) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.jumpiT d9.head hcond (Benchmarks.EAS.Attester.CreationBytecode.jumpdest_code tail (t := 115) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_98_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (attesterCreation_block_98_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_98_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_98_fallthrough`. -/
def attesterCreation_block_98_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 98. -/
theorem attesterCreation_block_98_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 111) (attesterCreation_block_98_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 98) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 32) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.dup3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup5 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.sub d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.slt d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.iszero d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 115) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.jumpiNT d9.head hcond (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_98_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 98) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 111) (attesterCreation_block_98_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_98_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 111. -/
theorem attesterCreation_block_111 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 111) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 98) rfl).drop 10 111 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterCreation_block_115_taken`. -/
def attesterCreation_block_115_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 115. -/
theorem attesterCreation_block_115_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (attesterCreation_block_115_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((47) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 115) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup2 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 1) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.push1 (UInt256.ofNat 1) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := r5.push1 (UInt256.ofNat 160) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.shl d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.sub d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.and d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.eq d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.push1 (UInt256.ofNat 137) d12.head (by evm_ov)
  have d13 := d12.next 2 rfl
  have r14 := r13.jumpiT d13.head hcond (Benchmarks.EAS.Attester.CreationBytecode.jumpdest_code tail (t := 137) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r14 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_115_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (attesterCreation_block_115_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_115_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterCreation_block_115_fallthrough`. -/
def attesterCreation_block_115_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 115. -/
theorem attesterCreation_block_115_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 133) (attesterCreation_block_115_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((47) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 115) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup2 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 1) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.push1 (UInt256.ofNat 1) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := r5.push1 (UInt256.ofNat 160) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.shl d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.sub d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.and d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.eq d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.push1 (UInt256.ofNat 137) d12.head (by evm_ov)
  have d13 := d12.next 2 rfl
  have r14 := r13.jumpiNT d13.head hcond (by evm_ov)
  exact RD.normalizeCounters r14 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_115_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.land (memLoad x1 mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 115) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 133) (attesterCreation_block_115_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_115_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 133. -/
theorem attesterCreation_block_133 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 133) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 115) rfl).drop 14 133 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterCreation_block_137`. -/
def attesterCreation_block_137_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 137. -/
theorem attesterCreation_block_137 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.EAS.Attester.attesterCreationBytecode 0).contains x4 = true)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 x4 (attesterCreation_block_137_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((21))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 137) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap4 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap3 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pop d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.jump d6.head (j tail x4 hvalid) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterCreation_block_137_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.EAS.Attester.attesterCreationBytecode 0).contains x4 = true)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 137) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 x4 (attesterCreation_block_137_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterCreation_block_137 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 144. -/
theorem attesterCreation_block_144 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 144) R mem aw rdata σ k C)
    : RDret fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 σ (((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 ((Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail).write (UInt256.ofNat 192).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 3865).toNat) ((UInt256.ofNat 824) + (UInt256.ofNat 0)).toNat 32) ((UInt256.ofNat 1719) + (UInt256.ofNat 0)).toNat 32) ((UInt256.ofNat 1888) + (UInt256.ofNat 0)).toNat 32) ((UInt256.ofNat 2289) + (UInt256.ofNat 0)).toNat 32).readWithPadding (UInt256.ofNat 0).toNat (UInt256.ofNat 3865).toNat) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 144) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 128) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 3865) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.push2 (UInt256.ofNat 192) d4.head (by evm_ov)
  have d5 := d4.next 3 rfl
  have r6 := r5.push1 (UInt256.ofNat 0) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := RD.genCodecopy r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 0) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.dup2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup2 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.push2 (UInt256.ofNat 824) d10.head (by evm_ov)
  have d11 := d10.next 3 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push2 (UInt256.ofNat 1719) d15.head (by evm_ov)
  have d16 := d15.next 3 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := RD.genMstore r17 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.dup2 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push2 (UInt256.ofNat 1888) d20.head (by evm_ov)
  have d21 := d20.next 3 rfl
  have r22 := r21.add d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := RD.genMstore r22 d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.push2 (UInt256.ofNat 2289) d23.head (by evm_ov)
  have d24 := d23.next 3 rfl
  have r25 := r24.add d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := RD.genMstore r25 d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := r26.push2 (UInt256.ofNat 3865) d26.head (by evm_ov)
  have d27 := d26.next 3 rfl
  have r28 := r27.push1 (UInt256.ofNat 0) d27.head (by evm_ov)
  have d28 := d27.next 2 rfl
  exact RD.genRet r28 d28.head (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 191. -/
theorem attesterCreation_block_191 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 191) R mem aw rdata σ k C)
    : RDinvalid fork (Benchmarks.EAS.Attester.attesterCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.CreationBytecode.decodes_code tail (t := 144) rfl).drop 29 191 rfl
  exact RD.invalid r0 d0.head

end attesterCreationBlocks
