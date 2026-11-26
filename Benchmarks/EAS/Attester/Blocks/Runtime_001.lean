import Reasoning.Reach
import Reasoning.Immutables
import Benchmarks.EAS.Attester.Immutables
import Benchmarks.EAS.Attester.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace attesterRuntimeBlocks

open Reasoning.Immutables
set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `attesterRuntime_block_0_taken`. -/
def attesterRuntime_block_0_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_0_taken`. -/
def attesterRuntime_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem attesterRuntime_block_0_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 16) (attesterRuntime_block_0_taken_stack (ee := ee) (R := R)) (attesterRuntime_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 0) rfl
  have r1 := r0.push1 (UInt256.ofNat 128) d0.head (by evm_ov)
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
  have r7 := r6.push2 (UInt256.ofNat 16) d6.head (by evm_ov)
  have d7 := d6.next 3 rfl
  have r8 := r7.jumpiT d7.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 16) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_0_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 16) (attesterRuntime_block_0_taken_stack (ee := ee) (R := R)) (attesterRuntime_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_0_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_0_fallthrough`. -/
def attesterRuntime_block_0_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_0_fallthrough`. -/
def attesterRuntime_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem attesterRuntime_block_0_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 12) (attesterRuntime_block_0_fallthrough_stack (ee := ee) (R := R)) (attesterRuntime_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 0) rfl
  have r1 := r0.push1 (UInt256.ofNat 128) d0.head (by evm_ov)
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
  have r7 := r6.push2 (UInt256.ofNat 16) d6.head (by evm_ov)
  have d7 := d6.next 3 rfl
  have r8 := r7.jumpiNT d7.head hcond (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_0_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 12) (attesterRuntime_block_0_fallthrough_stack (ee := ee) (R := R)) (attesterRuntime_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 12. -/
theorem attesterRuntime_block_12 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 12) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 0) rfl).drop 8 12 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_16_taken`. -/
def attesterRuntime_block_16_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 16. -/
theorem attesterRuntime_block_16_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 76) (attesterRuntime_block_16_taken_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 4) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.calldatasize d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.lt d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 76) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 76) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_16_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 76) (attesterRuntime_block_16_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_16_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_16_fallthrough`. -/
def attesterRuntime_block_16_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 16. -/
theorem attesterRuntime_block_16_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 26) (attesterRuntime_block_16_fallthrough_stack (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 4) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.calldatasize d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.lt d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 76) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_16_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 16) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 26) (attesterRuntime_block_16_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_16_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_26_taken`. -/
def attesterRuntime_block_26_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem attesterRuntime_block_26_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 335406416) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 81) (attesterRuntime_block_26_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 7 26 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.calldataload d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 224) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.shr d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push4 (UInt256.ofNat 335406416) d5.head (by evm_ov)
  have d6 := d5.next 5 rfl
  have r7 := r6.eq d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 81) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiT d8.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 81) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_26_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 335406416) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 81) (attesterRuntime_block_26_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_26_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_26_fallthrough`. -/
def attesterRuntime_block_26_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem attesterRuntime_block_26_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 335406416) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 43) (attesterRuntime_block_26_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 9) (C + ((34))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 7 26 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.calldataload d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 224) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.shr d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push4 (UInt256.ofNat 335406416) d5.head (by evm_ov)
  have d6 := d5.next 5 rfl
  have r7 := r6.eq d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 81) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiNT d8.head hcond (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_26_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 335406416) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 0).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 43) (attesterRuntime_block_26_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_26_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 43. -/
theorem attesterRuntime_block_43_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1424087861) x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 102) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 16 43 rfl
  have r1 := r0.dup1 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push4 (UInt256.ofNat 1424087861) d1.head (by evm_ov)
  have d2 := d1.next 5 rfl
  have r3 := r2.eq d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 102) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiT d4.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 102) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_43_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1424087861) x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 102) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_43_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 43. -/
theorem attesterRuntime_block_43_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1424087861) x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 16 43 rfl
  have r1 := r0.dup1 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push4 (UInt256.ofNat 1424087861) d1.head (by evm_ov)
  have d2 := d1.next 5 rfl
  have r3 := r2.eq d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 102) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiNT d4.head hcond (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_43_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1424087861) x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 43) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_43_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 54. -/
theorem attesterRuntime_block_54_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1924765293) x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 143) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 21 54 rfl
  have r1 := r0.dup1 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push4 (UInt256.ofNat 1924765293) d1.head (by evm_ov)
  have d2 := d1.next 5 rfl
  have r3 := r2.eq d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 143) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiT d4.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 143) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_54_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1924765293) x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 143) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_54_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 54. -/
theorem attesterRuntime_block_54_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1924765293) x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 21 54 rfl
  have r1 := r0.dup1 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push4 (UInt256.ofNat 1924765293) d1.head (by evm_ov)
  have d2 := d1.next 5 rfl
  have r3 := r2.eq d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 143) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiNT d4.head hcond (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_54_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1924765293) x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_54_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 65. -/
theorem attesterRuntime_block_65_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3261482512) x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 176) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 26 65 rfl
  have r1 := r0.dup1 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push4 (UInt256.ofNat 3261482512) d1.head (by evm_ov)
  have d2 := d1.next 5 rfl
  have r3 := r2.eq d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 176) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiT d4.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 176) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_65_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3261482512) x0) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 176) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_65_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 65. -/
theorem attesterRuntime_block_65_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3261482512) x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 16) rfl).drop 26 65 rfl
  have r1 := r0.dup1 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push4 (UInt256.ofNat 3261482512) d1.head (by evm_ov)
  have d2 := d1.next 5 rfl
  have r3 := r2.eq d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 176) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.jumpiNT d4.head hcond (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_65_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 3261482512) x0) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 65) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 76) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_65_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 76. -/
theorem attesterRuntime_block_76 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 76) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 76) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  exact RD.genRev r3 d3.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_81`. -/
def attesterRuntime_block_81_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 95) :: (UInt256.ofNat 100) :: R)

/-- Automatically generated RD summary for bytecode block at pc 81. -/
theorem attesterRuntime_block_81 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 81) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2482) (attesterRuntime_block_81_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 81) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push2 (UInt256.ofNat 100) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.push2 (UInt256.ofNat 95) d2.head (by evm_ov)
  have d3 := d2.next 3 rfl
  have r4 := r3.calldatasize d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 4) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := r5.push2 (UInt256.ofNat 2482) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jump d6.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2482) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_81_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 81) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2482) (attesterRuntime_block_81_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_81 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 95. -/
theorem attesterRuntime_block_95 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 95) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 195) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 95) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push2 (UInt256.ofNat 195) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 195) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_95_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 95) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 195) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_95 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 100. -/
theorem attesterRuntime_block_100 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 100) R mem aw rdata σ k C)
    : RDret fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 σ ByteArray.empty := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 100) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  exact r1.stop d1.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_102`. -/
def attesterRuntime_block_102_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 116) :: (UInt256.ofNat 121) :: R)

/-- Automatically generated RD summary for bytecode block at pc 102. -/
theorem attesterRuntime_block_102 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 102) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2482) (attesterRuntime_block_102_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((23))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 102) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push2 (UInt256.ofNat 121) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.push2 (UInt256.ofNat 116) d2.head (by evm_ov)
  have d3 := d2.next 3 rfl
  have r4 := r3.calldatasize d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 4) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := r5.push2 (UInt256.ofNat 2482) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jump d6.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2482) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_102_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 102) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2482) (attesterRuntime_block_102_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_102 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 116. -/
theorem attesterRuntime_block_116 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 116) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 935) R mem aw rdata σ (k + 3) (C + ((12))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 116) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push2 (UInt256.ofNat 935) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 935) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_116_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 116) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 935) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_116 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_121`. -/
def attesterRuntime_block_121_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: x0 :: (UInt256.ofNat 134) :: R)

/-- Automatically generated RD summary for bytecode block at pc 121. -/
theorem attesterRuntime_block_121 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 121) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2595) (attesterRuntime_block_121_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 121) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push2 (UInt256.ofNat 134) d3.head (by evm_ov)
  have d4 := d3.next 3 rfl
  have r5 := r4.swap2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.swap1 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push2 (UInt256.ofNat 2595) d6.head (by evm_ov)
  have d7 := d6.next 3 rfl
  have r8 := r7.jump d7.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2595) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_121_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 121) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2595) (attesterRuntime_block_121_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_121 hstack h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
