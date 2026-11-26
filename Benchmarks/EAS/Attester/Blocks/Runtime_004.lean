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

/-- Final stack for bytecode block summary `attesterRuntime_block_575`. -/
def attesterRuntime_block_575_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 575. -/
theorem attesterRuntime_block_575 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_575_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((11))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 575) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pop d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 0) d4.head (by evm_ov)
  exact RD.normalizeCounters r5 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_575_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 575) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_575_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_575 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem attesterRuntime_block_581_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 581) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup3 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 672) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 672) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_581_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_581_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 581. -/
theorem attesterRuntime_block_581_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 581) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup3 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 672) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_581_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_581_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_590_taken`. -/
def attesterRuntime_block_590_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_590_taken`. -/
def attesterRuntime_block_590_taken_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 590. -/
theorem attesterRuntime_block_590_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (attesterRuntime_block_590_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_taken_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((55) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 581) rfl).drop 7 590 rfl
  have r1 := r0.push1 (UInt256.ofNat 64) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 64) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 64) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup7 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup7 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup5 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.lt d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push2 (UInt256.ofNat 618) d14.head (by evm_ov)
  have d15 := d14.next 3 rfl
  have r16 := r15.jumpiT d15.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 618) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r16 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_590_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (attesterRuntime_block_590_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_590_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_590_fallthrough`. -/
def attesterRuntime_block_590_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_590_fallthrough`. -/
def attesterRuntime_block_590_fallthrough_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 590. -/
theorem attesterRuntime_block_590_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) (attesterRuntime_block_590_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_fallthrough_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((55) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 581) rfl).drop 7 590 rfl
  have r1 := r0.push1 (UInt256.ofNat 64) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 64) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 64) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup7 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup7 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup5 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.lt d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push2 (UInt256.ofNat 618) d14.head (by evm_ov)
  have d15 := d14.next 3 rfl
  have r16 := r15.jumpiNT d15.head hcond (by evm_ov)
  exact RD.normalizeCounters r16 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_590_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 590) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) (attesterRuntime_block_590_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_590_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_590_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_611`. -/
def attesterRuntime_block_611_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 618) :: R)

/-- Automatically generated RD summary for bytecode block at pc 611. -/
theorem attesterRuntime_block_611 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_611_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 581) rfl).drop 23 611 rfl
  have r1 := r0.push2 (UInt256.ofNat 618) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_611_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 611) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_611_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_611 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_618_taken`. -/
def attesterRuntime_block_618_taken_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x6 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_618_taken`. -/
def attesterRuntime_block_618_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 618. -/
theorem attesterRuntime_block_618_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (attesterRuntime_block_618_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 618) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.pop d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 32) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.mul d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.calldataload d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 32) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push1 (UInt256.ofNat 0) d11.head (by evm_ov)
  have d12 := d11.next 2 rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := RD.genMstore r13 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.pop d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.dup3 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup3 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.dup2 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := RD.genMload r18 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.dup2 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.lt d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.push2 (UInt256.ofNat 653) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiT d22.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 653) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_618_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (attesterRuntime_block_618_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_618_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_618_fallthrough`. -/
def attesterRuntime_block_618_fallthrough_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x6 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_618_fallthrough`. -/
def attesterRuntime_block_618_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 618. -/
theorem attesterRuntime_block_618_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) (attesterRuntime_block_618_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 618) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.pop d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 32) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.mul d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.calldataload d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 32) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push1 (UInt256.ofNat 0) d11.head (by evm_ov)
  have d12 := d11.next 2 rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := RD.genMstore r13 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.pop d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.dup3 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup3 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.dup2 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := RD.genMload r18 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.dup2 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.lt d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.push2 (UInt256.ofNat 653) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiNT d22.head hcond (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_618_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.lt x5 (memLoad x6 ((UInt256.ofNat 0).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 618) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) (attesterRuntime_block_618_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_618_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_618_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_646`. -/
def attesterRuntime_block_646_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 653) :: R)

/-- Automatically generated RD summary for bytecode block at pc 646. -/
theorem attesterRuntime_block_646 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_646_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 618) rfl).drop 23 646 rfl
  have r1 := r0.push2 (UInt256.ofNat 653) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_646_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 646) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_646_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_646 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_653`. -/
def attesterRuntime_block_653_stack {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x3) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_653`. -/
def attesterRuntime_block_653_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 653. -/
theorem attesterRuntime_block_653 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_653_stack (x3 := x3) (R := R)) (attesterRuntime_block_653_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((50) + (memExpansionCost aw (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 653) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.swap1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup2 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.mul d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.swap2 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.swap1 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.swap2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.add d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := RD.genMstore r10 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push1 (UInt256.ofNat 1) d11.head (by evm_ov)
  have d12 := d11.next 2 rfl
  have r13 := r12.add d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push2 (UInt256.ofNat 581) d13.head (by evm_ov)
  have d14 := d13.next 3 rfl
  have r15 := r14.jump d14.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 581) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r15 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_653_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 653) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 581) (attesterRuntime_block_653_stack (x3 := x3) (R := R)) (attesterRuntime_block_653_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_653 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_672_taken`. -/
def attesterRuntime_block_672_taken_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x10 :: x11 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_672_taken`. -/
def attesterRuntime_block_672_taken_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 672. -/
theorem attesterRuntime_block_672_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (attesterRuntime_block_672_taken_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_taken_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 672) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 64) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 64) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.add d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 64) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup1 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup13 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup13 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup9 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.lt d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.push2 (UInt256.ofNat 702) d16.head (by evm_ov)
  have d17 := d16.next 3 rfl
  have r18 := r17.jumpiT d17.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 702) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r18 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_672_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (attesterRuntime_block_672_taken_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_672_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_672_fallthrough`. -/
def attesterRuntime_block_672_fallthrough_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x10 :: x11 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_672_fallthrough`. -/
def attesterRuntime_block_672_fallthrough_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 672. -/
theorem attesterRuntime_block_672_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) (attesterRuntime_block_672_fallthrough_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_fallthrough_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 672) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 64) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 64) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.add d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 64) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup1 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup13 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup13 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup9 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.lt d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.push2 (UInt256.ofNat 702) d16.head (by evm_ov)
  have d17 := d16.next 3 rfl
  have r18 := r17.jumpiNT d17.head hcond (by evm_ov)
  exact RD.normalizeCounters r18 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_672_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.lt x5 x10) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 672) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) (attesterRuntime_block_672_fallthrough_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (attesterRuntime_block_672_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_672_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_695`. -/
def attesterRuntime_block_695_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 702) :: R)

/-- Automatically generated RD summary for bytecode block at pc 695. -/
theorem attesterRuntime_block_695 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_695_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 672) rfl).drop 18 695 rfl
  have r1 := r0.push2 (UInt256.ofNat 702) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_695_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 695) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_695_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_695 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_702_taken`. -/
def attesterRuntime_block_702_taken_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x10 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_702_taken`. -/
def attesterRuntime_block_702_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 702. -/
theorem attesterRuntime_block_702_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (attesterRuntime_block_702_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 702) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.pop d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 32) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.mul d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.calldataload d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 32) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup3 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := RD.genMstore r13 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.pop d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.dup7 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup7 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.dup2 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := RD.genMload r18 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.dup2 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.lt d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.push2 (UInt256.ofNat 736) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiT d22.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 736) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_702_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (attesterRuntime_block_702_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_702_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_702_fallthrough`. -/
def attesterRuntime_block_702_fallthrough_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x10 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_702_fallthrough`. -/
def attesterRuntime_block_702_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 702. -/
theorem attesterRuntime_block_702_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) (attesterRuntime_block_702_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 702) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.pop d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 32) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.mul d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.calldataload d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 32) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup3 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := RD.genMstore r13 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.pop d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.dup7 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup7 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.dup2 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := RD.genMload r18 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.dup2 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.lt d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.push2 (UInt256.ofNat 736) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiNT d22.head hcond (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_702_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 702) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) (attesterRuntime_block_702_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_702_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_702_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_729`. -/
def attesterRuntime_block_729_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 736) :: R)

/-- Automatically generated RD summary for bytecode block at pc 729. -/
theorem attesterRuntime_block_729 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_729_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 702) rfl).drop 23 729 rfl
  have r1 := r0.push2 (UInt256.ofNat 736) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_729_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_729_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_729 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_736`. -/
def attesterRuntime_block_736_stack {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x7) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_736`. -/
def attesterRuntime_block_736_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 736. -/
theorem attesterRuntime_block_736 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (attesterRuntime_block_736_stack (x7 := x7) (R := R)) (attesterRuntime_block_736_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((62) + (memExpansionCost aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 736) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.mul d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 32) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.dup2 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.swap1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.pop d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.pop d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.pop d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.pop d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.pop d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup1 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push1 (UInt256.ofNat 1) d15.head (by evm_ov)
  have d16 := d15.next 2 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.swap1 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.pop d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.push2 (UInt256.ofNat 367) d19.head (by evm_ov)
  have d20 := d19.next 3 rfl
  have r21 := r20.jump d20.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 367) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r21 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_736_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 736) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 367) (attesterRuntime_block_736_stack (x7 := x7) (R := R)) (attesterRuntime_block_736_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_736 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_762`. -/
def attesterRuntime_block_762_stack {immWords : String → UInt256} {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: x1 :: (UInt256.ofNat 877) :: (UInt256.ofNat 1287121381) :: (UInt256.land (immWords "_eas") (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_762`. -/
def attesterRuntime_block_762_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 34700723785909278827545364893952542206761801622036869180408675228056652087296).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 762. -/
theorem attesterRuntime_block_762 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 762) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (attesterRuntime_block_762_stack (immWords := immWords) (mem := mem) (x1 := x1) (R := R)) (attesterRuntime_block_762_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((65) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 762) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 64) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pushConst (UInt256.ofNat 34700723785909278827545364893952542206761801622036869180408675228056652087296) (width := 32) (op := .PUSH32) (by decide) d4.head (by evm_ov)
  have d5 := d4.next (Nat.succ 32) rfl
  have r6 := r5.dup2 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) d7.head (by evm_ov)
  have d8 := d7.next 21 rfl
  have r9 := r8.pushConst (immWords "_eas") (width := 32) (op := .PUSH32) (by decide) d8.head (by evm_ov)
  have d9 := d8.next (Nat.succ 32) rfl
  have r10 := r9.and d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap1 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push4 (UInt256.ofNat 1287121381) d11.head (by evm_ov)
  have d12 := d11.next 5 rfl
  have r13 := r12.swap1 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push2 (UInt256.ofNat 877) d13.head (by evm_ov)
  have d14 := d13.next 3 rfl
  have r15 := r14.swap1 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.dup5 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.swap1 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.push1 (UInt256.ofNat 4) d17.head (by evm_ov)
  have d18 := d17.next 2 rfl
  have r19 := r18.add d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.push2 (UInt256.ofNat 2894) d19.head (by evm_ov)
  have d20 := d19.next 3 rfl
  have r21 := r20.jump d20.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2894) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r21 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_762_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 762) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (attesterRuntime_block_762_stack (immWords := immWords) (mem := mem) (x1 := x1) (R := R)) (attesterRuntime_block_762_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_762 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_877_taken`. -/
def attesterRuntime_block_877_taken_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x2)) :: x2 :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 877. -/
theorem attesterRuntime_block_877_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 903) (attesterRuntime_block_877_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 877) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 64) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup4 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.sub d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 0) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.dup8 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup1 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  obtain ⟨_, _, r12⟩ := r11.extcodesize d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.iszero d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup1 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.iszero d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push2 (UInt256.ofNat 903) d15.head (by evm_ov)
  have d16 := d15.next 3 rfl
  have r17 := r16.jumpiT d16.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 903) rfl rfl) (by evm_ov)
  exact ⟨_, _, r17⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_877_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 903) (attesterRuntime_block_877_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := attesterRuntime_block_877_taken hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_877_fallthrough`. -/
def attesterRuntime_block_877_fallthrough_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x2)) :: x2 :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 877. -/
theorem attesterRuntime_block_877_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 899) (attesterRuntime_block_877_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 877) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 64) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup4 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.sub d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 0) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.dup8 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup1 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  obtain ⟨_, _, r12⟩ := r11.extcodesize d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.iszero d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup1 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.iszero d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push2 (UInt256.ofNat 903) d15.head (by evm_ov)
  have d16 := d15.next 3 rfl
  have r17 := r16.jumpiNT d16.head hcond (by evm_ov)
  exact ⟨_, _, r17⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_877_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 899) (attesterRuntime_block_877_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := attesterRuntime_block_877_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
