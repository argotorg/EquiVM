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

/-- Final stack for bytecode block summary `attesterRuntime_block_2843_fallthrough`. -/
def attesterRuntime_block_2843_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x3 + x0) :: (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2843. -/
theorem attesterRuntime_block_2843_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2866) (attesterRuntime_block_2843_fallthrough_stack (ee := ee) (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2843) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup4 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.add d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup1 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.calldataload d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.swap2 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pop d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d7.head (by evm_ov)
  have d8 := d7.next (Nat.succ 8) rfl
  have r9 := r8.dup3 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.gt d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.iszero d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push2 (UInt256.ofNat 2870) d11.head (by evm_ov)
  have d12 := d11.next 3 rfl
  have r13 := r12.jumpiNT d12.head hcond (by evm_ov)
  exact RD.normalizeCounters r13 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2843_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2866) (attesterRuntime_block_2843_fallthrough_stack (ee := ee) (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2843_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2866. -/
theorem attesterRuntime_block_2866 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2866) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2843) rfl).drop 13 2866 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_2870_taken`. -/
def attesterRuntime_block_2870_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: ((UInt256.ofNat 32) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2870. -/
theorem attesterRuntime_block_2870_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2475) (attesterRuntime_block_2870_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 16) (C + ((51))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2870) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.add d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap2 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 5) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.dup2 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.swap1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.shl d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.calldatasize d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.sub d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup3 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.sgt d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.iszero d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push2 (UInt256.ofNat 2475) d14.head (by evm_ov)
  have d15 := d14.next 3 rfl
  have r16 := r15.jumpiT d15.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2475) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r16 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2870_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2475) (attesterRuntime_block_2870_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2870_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2870_fallthrough`. -/
def attesterRuntime_block_2870_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: ((UInt256.ofNat 32) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2870. -/
theorem attesterRuntime_block_2870_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2890) (attesterRuntime_block_2870_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 16) (C + ((51))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2870) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.add d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap2 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 5) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.dup2 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.swap1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.shl d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.calldatasize d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.sub d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup3 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.sgt d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.iszero d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push2 (UInt256.ofNat 2475) d14.head (by evm_ov)
  have d15 := d14.next 3 rfl
  have r16 := r15.jumpiNT d15.head hcond (by evm_ov)
  exact RD.normalizeCounters r16 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2870_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.sgt ((UInt256.ofNat 32) + x0) (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft x1 (UInt256.ofNat 5))))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2890) (attesterRuntime_block_2870_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2870_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2890. -/
theorem attesterRuntime_block_2890 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2890) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2870) rfl).drop 16 2890 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_2894`. -/
def attesterRuntime_block_2894_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (x1 + (UInt256.ofNat 32)) :: (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) :: (x0 + (UInt256.ofNat 64)) :: ((x0 + (UInt256.shiftLeft (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 5))) + (UInt256.ofNat 64)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_2894`. -/
def attesterRuntime_block_2894_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2894. -/
theorem attesterRuntime_block_2894 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_2894_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_2894_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((92) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2894) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.push1 (UInt256.ofNat 32) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.dup3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 32) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.dup4 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := RD.genMstore r7 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup1 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup5 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := RD.genMload r10 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup1 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup4 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := RD.genMstore r13 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push1 (UInt256.ofNat 64) d14.head (by evm_ov)
  have d15 := d14.next 2 rfl
  have r16 := r15.dup6 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.swap2 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.pop d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.push1 (UInt256.ofNat 64) d19.head (by evm_ov)
  have d20 := d19.next 2 rfl
  have r21 := r20.dup2 d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.push1 (UInt256.ofNat 5) d21.head (by evm_ov)
  have d22 := d21.next 2 rfl
  have r23 := r22.shl d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.dup7 d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := r24.add d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.add d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := r26.swap3 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.pop d27.head (by evm_ov)
  have d28 := d27.next 1 rfl
  have r29 := r28.push1 (UInt256.ofNat 32) d28.head (by evm_ov)
  have d29 := d28.next 2 rfl
  have r30 := r29.dup7 d29.head (by evm_ov)
  have d30 := d29.next 1 rfl
  have r31 := r30.add d30.head (by evm_ov)
  have d31 := d30.next 1 rfl
  have r32 := r31.push1 (UInt256.ofNat 0) d31.head (by evm_ov)
  exact RD.normalizeCounters r32 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2894_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2894) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_2894_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_2894_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2894 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2934. -/
theorem attesterRuntime_block_2934_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2934) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 3097) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3097) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2934_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2934_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2934. -/
theorem attesterRuntime_block_2934_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2934) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 3097) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2934_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2934_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2943`. -/
def attesterRuntime_block_2943_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) :: (x4 + (UInt256.ofNat 96)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32))) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_2943`. -/
def attesterRuntime_block_2943_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x6 : UInt256} : ByteArray :=
  ((memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2943. -/
theorem attesterRuntime_block_2943 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_2943_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_2943_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) (M (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 42) (C + ((126) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) + (UInt256.sub x4 x6)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2934) rfl).drop 7 2943 rfl
  have r1 := r0.dup7 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup6 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.sub d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) (width := 32) (op := .PUSH32) (by decide) d3.head (by evm_ov)
  have d4 := d3.next (Nat.succ 32) rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup5 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := RD.genMload r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup1 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := RD.genMload r10 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup7 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 32) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.swap1 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.dup2 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := RD.genMload r17 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.push1 (UInt256.ofNat 64) d18.head (by evm_ov)
  have d19 := d18.next 2 rfl
  have r20 := r19.dup3 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.dup9 d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.add d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.dup2 d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.swap1 d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := RD.genMstore r24 d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.dup2 d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := RD.genMload r26 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.swap1 d27.head (by evm_ov)
  have d28 := d27.next 1 rfl
  have r29 := r28.dup9 d28.head (by evm_ov)
  have d29 := d28.next 1 rfl
  have r30 := r29.add d29.head (by evm_ov)
  have d30 := d29.next 1 rfl
  have r31 := r30.dup2 d30.head (by evm_ov)
  have d31 := d30.next 1 rfl
  have r32 := r31.swap1 d31.head (by evm_ov)
  have d32 := d31.next 1 rfl
  have r33 := RD.genMstore r32 d32.head (by evm_ov)
  have d33 := d32.next 1 rfl
  have r34 := r33.swap2 d33.head (by evm_ov)
  have d34 := d33.next 1 rfl
  have r35 := r34.add d34.head (by evm_ov)
  have d35 := d34.next 1 rfl
  have r36 := r35.swap1 d35.head (by evm_ov)
  have d36 := d35.next 1 rfl
  have r37 := r36.push1 (UInt256.ofNat 0) d36.head (by evm_ov)
  have d37 := d36.next 2 rfl
  have r38 := r37.swap1 d37.head (by evm_ov)
  have d38 := d37.next 1 rfl
  have r39 := r38.push1 (UInt256.ofNat 96) d38.head (by evm_ov)
  have d39 := d38.next 2 rfl
  have r40 := r39.dup9 d39.head (by evm_ov)
  have d40 := d39.next 1 rfl
  have r41 := r40.add d40.head (by evm_ov)
  have d41 := d40.next 1 rfl
  have r42 := r41.swap1 d41.head (by evm_ov)
  exact RD.normalizeCounters r42 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2943_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2943) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_2943_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_2943_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2943 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3021. -/
theorem attesterRuntime_block_3021_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3021) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup4 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 3073) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3073) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3021_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3021_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3021. -/
theorem attesterRuntime_block_3021_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3021) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup4 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 3073) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3021_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x2 x0)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3021_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `attesterRuntime_block_3030`. -/
def attesterRuntime_block_3030_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  ((memLoad ((UInt256.ofNat 32) + (memLoad x3 mem)) ((memLoad (memLoad x3 mem) mem).toByteArray.write 0 mem x1.toNat 32)).toByteArray.write 0 ((memLoad (memLoad x3 mem) mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3030. -/
theorem attesterRuntime_block_3030 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) (attesterRuntime_block_3030_memory (mem := mem) (x1 := x1) (x3 := x3)) (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x3 mem)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((56) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x3 mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x3 (⟨32⟩ : UInt256)) (memLoad x3 mem) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x3 mem)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3021) rfl).drop 7 3030 rfl
  have r1 := r0.push2 (UInt256.ofNat 3050) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.dup3 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := RD.genMload r5 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.dup3 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := RD.genMstore r7 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 32) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.swap1 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMload r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.swap2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.add d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := RD.genMstore r15 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.jump d16.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3050) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3030_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3030) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) (attesterRuntime_block_3030_memory (mem := mem) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3030 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3050`. -/
def attesterRuntime_block_3050_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (x1 + (UInt256.ofNat 64)) :: (x2 + (UInt256.ofNat 1)) :: (x3 + (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3050. -/
theorem attesterRuntime_block_3050 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_3050_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 18) (C + ((54))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3050) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup3 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.add d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 32) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.dup5 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.add d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.swap4 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.pop d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push1 (UInt256.ofNat 1) d11.head (by evm_ov)
  have d12 := d11.next 2 rfl
  have r13 := r12.dup4 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.add d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.swap3 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.pop d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.push2 (UInt256.ofNat 3021) d16.head (by evm_ov)
  have d17 := d16.next 3 rfl
  have r18 := r17.jump d17.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3021) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r18 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3050_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3050) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3021) (attesterRuntime_block_3050_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3050 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3073`. -/
def attesterRuntime_block_3073_stack {x1 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x4) :: ((UInt256.ofNat 32) + x5) :: x6 :: ((UInt256.ofNat 32) + x7) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3073. -/
theorem attesterRuntime_block_3073 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_3073_stack (x1 := x1) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ (k + 20) (C + ((59))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3073) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap7 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pop d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 32) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.swap4 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup5 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap4 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.swap2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.swap1 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.swap2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.add d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.swap1 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.push1 (UInt256.ofNat 1) d16.head (by evm_ov)
  have d17 := d16.next 2 rfl
  have r18 := r17.add d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.push2 (UInt256.ofNat 2934) d18.head (by evm_ov)
  have d19 := d18.next 3 rfl
  have r20 := r19.jump d19.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2934) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r20 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3073_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3073) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2934) (attesterRuntime_block_3073_stack (x1 := x1) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3073 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3097`. -/
def attesterRuntime_block_3097_stack {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3097. -/
theorem attesterRuntime_block_3097 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3097_stack (x4 := x4) (R := R)) mem aw rdata σ (k + 12) (C + ((32))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3097) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap3 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap7 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap6 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pop d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.pop d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.pop d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.pop d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.pop d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.jump d11.head hvalid (by evm_ov)
  exact RD.normalizeCounters r12 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3097_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3097_stack (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3097 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3109`. -/
def attesterRuntime_block_3109_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (memLoad (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) ((UInt256.ofNat 192).toByteArray.write 0 ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32) (x1 + (UInt256.ofNat 128)).toNat 32)) :: (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3109`. -/
def attesterRuntime_block_3109_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) ((UInt256.ofNat 192).toByteArray.write 0 ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32) (x1 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 192).toByteArray.write 0 ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32) (x1 + (UInt256.ofNat 128)).toNat 32) (x1 + (UInt256.ofNat 192)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3109. -/
theorem attesterRuntime_block_3109 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3109_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3109_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 53) (C + ((157) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (memLoad (x0 + (UInt256.ofNat 128)) ((memLoad (x0 + (UInt256.ofNat 96)) ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x0 + (UInt256.ofNat 64)) ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x0 + (UInt256.ofNat 32)) ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32)) (UInt256.ofNat 18446744073709551615)).toByteArray.write 0 ((UInt256.land (memLoad x0 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat 32) (x1 + (UInt256.ofNat 64)).toNat 32) (x1 + (UInt256.ofNat 96)).toNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3109) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) d1.head (by evm_ov)
  have d2 := d1.next 21 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.and d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup3 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d7.head (by evm_ov)
  have d8 := d7.next (Nat.succ 8) rfl
  have r9 := r8.push1 (UInt256.ofNat 32) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.dup3 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := RD.genMload r11 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.and d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 32) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.dup4 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.add d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := RD.genMstore r16 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.push1 (UInt256.ofNat 64) d17.head (by evm_ov)
  have d18 := d17.next 2 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.add d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := RD.genMload r20 d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.iszero d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.iszero d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.push1 (UInt256.ofNat 64) d23.head (by evm_ov)
  have d24 := d23.next 2 rfl
  have r25 := r24.dup4 d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.add d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := RD.genMstore r26 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.push1 (UInt256.ofNat 96) d27.head (by evm_ov)
  have d28 := d27.next 2 rfl
  have r29 := r28.dup2 d28.head (by evm_ov)
  have d29 := d28.next 1 rfl
  have r30 := r29.add d29.head (by evm_ov)
  have d30 := d29.next 1 rfl
  have r31 := RD.genMload r30 d30.head (by evm_ov)
  have d31 := d30.next 1 rfl
  have r32 := r31.push1 (UInt256.ofNat 96) d31.head (by evm_ov)
  have d32 := d31.next 2 rfl
  have r33 := r32.dup4 d32.head (by evm_ov)
  have d33 := d32.next 1 rfl
  have r34 := r33.add d33.head (by evm_ov)
  have d34 := d33.next 1 rfl
  have r35 := RD.genMstore r34 d34.head (by evm_ov)
  have d35 := d34.next 1 rfl
  have r36 := r35.push1 (UInt256.ofNat 0) d35.head (by evm_ov)
  have d36 := d35.next 2 rfl
  have r37 := r36.push1 (UInt256.ofNat 128) d36.head (by evm_ov)
  have d37 := d36.next 2 rfl
  have r38 := r37.dup3 d37.head (by evm_ov)
  have d38 := d37.next 1 rfl
  have r39 := r38.add d38.head (by evm_ov)
  have d39 := d38.next 1 rfl
  have r40 := RD.genMload r39 d39.head (by evm_ov)
  have d40 := d39.next 1 rfl
  have r41 := r40.push1 (UInt256.ofNat 192) d40.head (by evm_ov)
  have d41 := d40.next 2 rfl
  have r42 := r41.push1 (UInt256.ofNat 128) d41.head (by evm_ov)
  have d42 := d41.next 2 rfl
  have r43 := r42.dup6 d42.head (by evm_ov)
  have d43 := d42.next 1 rfl
  have r44 := r43.add d43.head (by evm_ov)
  have d44 := d43.next 1 rfl
  have r45 := RD.genMstore r44 d44.head (by evm_ov)
  have d45 := d44.next 1 rfl
  have r46 := r45.dup1 d45.head (by evm_ov)
  have d46 := d45.next 1 rfl
  have r47 := RD.genMload r46 d46.head (by evm_ov)
  have d47 := d46.next 1 rfl
  have r48 := r47.dup1 d47.head (by evm_ov)
  have d48 := d47.next 1 rfl
  have r49 := r48.push1 (UInt256.ofNat 192) d48.head (by evm_ov)
  have d49 := d48.next 2 rfl
  have r50 := r49.dup7 d49.head (by evm_ov)
  have d50 := d49.next 1 rfl
  have r51 := r50.add d50.head (by evm_ov)
  have d51 := d50.next 1 rfl
  have r52 := RD.genMstore r51 d51.head (by evm_ov)
  have d52 := d51.next 1 rfl
  have r53 := r52.push1 (UInt256.ofNat 0) d52.head (by evm_ov)
  exact RD.normalizeCounters r53 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3109_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3109_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3109_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3109 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3202. -/
theorem attesterRuntime_block_3202_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3202) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup2 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 3231) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3231) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3202_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3202_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3202. -/
theorem attesterRuntime_block_3202_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3202) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup2 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 3231) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3202_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3202_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3211`. -/
def attesterRuntime_block_3211_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3211`. -/
def attesterRuntime_block_3211_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x5 : UInt256} : ByteArray :=
  ((memLoad ((UInt256.ofNat 32) + (x2 + x0)) mem).toByteArray.write 0 mem ((x0 + x5) + (UInt256.ofNat 224)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3211. -/
theorem attesterRuntime_block_3211 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3211_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (attesterRuntime_block_3211_memory (mem := mem) (x0 := x0) (x2 := x2) (x5 := x5)) (M (M aw ((UInt256.ofNat 32) + (x2 + x0)) (⟨32⟩ : UInt256)) ((x0 + x5) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((53) + (memExpansionCost aw ((UInt256.ofNat 32) + (x2 + x0)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((UInt256.ofNat 32) + (x2 + x0)) (⟨32⟩ : UInt256)) ((x0 + x5) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3202) rfl).drop 7 3211 rfl
  have r1 := r0.push1 (UInt256.ofNat 32) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup2 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup5 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.add d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMload r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 224) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.dup9 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup5 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.add d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push2 (UInt256.ofNat 3202) d14.head (by evm_ov)
  have d15 := d14.next 3 rfl
  have r16 := r15.jump d15.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3202) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r16 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3211_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3211) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3202) (attesterRuntime_block_3211_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (attesterRuntime_block_3211_memory (mem := mem) (x0 := x0) (x2 := x2) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3211 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3231`. -/
def attesterRuntime_block_3231_stack {x1 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((x5 + (UInt256.land (x1 + (UInt256.ofNat 31)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) + (UInt256.ofNat 224)) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3231`. -/
def attesterRuntime_block_3231_memory {mem : ByteArray} {x1 : UInt256} {x4 : UInt256} {x5 : UInt256} : ByteArray :=
  ((memLoad (x4 + (UInt256.ofNat 160)) ((UInt256.ofNat 0).toByteArray.write 0 mem ((x5 + x1) + (UInt256.ofNat 224)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 0).toByteArray.write 0 mem ((x5 + x1) + (UInt256.ofNat 224)).toNat 32) (x5 + (UInt256.ofNat 160)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3231. -/
theorem attesterRuntime_block_3231 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x6 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x6 (attesterRuntime_block_3231_stack (x1 := x1) (x5 := x5) (R := R)) (attesterRuntime_block_3231_memory (mem := mem) (x1 := x1) (x4 := x4) (x5 := x5)) (M (M (M aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 35) (C + ((102) + (memExpansionCost aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw ((x5 + x1) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3231) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 0) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.push1 (UInt256.ofNat 224) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.dup3 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup8 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.add d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.add d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := RD.genMstore r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 160) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := r10.dup5 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMload r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 160) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.dup7 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.add d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := RD.genMstore r16 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.push1 (UInt256.ofNat 224) d17.head (by evm_ov)
  have d18 := d17.next 2 rfl
  have r19 := r18.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) d18.head (by evm_ov)
  have d19 := d18.next (Nat.succ 32) rfl
  have r20 := r19.push1 (UInt256.ofNat 31) d19.head (by evm_ov)
  have d20 := d19.next 2 rfl
  have r21 := r20.dup4 d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.add d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.and d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.dup7 d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := r24.add d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.add d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := r26.swap3 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.pop d27.head (by evm_ov)
  have d28 := d27.next 1 rfl
  have r29 := r28.pop d28.head (by evm_ov)
  have d29 := d28.next 1 rfl
  have r30 := r29.pop d29.head (by evm_ov)
  have d30 := d29.next 1 rfl
  have r31 := r30.swap3 d30.head (by evm_ov)
  have d31 := d30.next 1 rfl
  have r32 := r31.swap2 d31.head (by evm_ov)
  have d32 := d31.next 1 rfl
  have r33 := r32.pop d32.head (by evm_ov)
  have d33 := d32.next 1 rfl
  have r34 := r33.pop d33.head (by evm_ov)
  have d34 := d33.next 1 rfl
  have r35 := r34.jump d34.head hvalid (by evm_ov)
  exact RD.normalizeCounters r35 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3231_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x6 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3231) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x6 (attesterRuntime_block_3231_stack (x1 := x1) (x5 := x5) (R := R)) (attesterRuntime_block_3231_memory (mem := mem) (x1 := x1) (x4 := x4) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3231 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
