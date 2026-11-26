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

/-- Final stack for bytecode block summary `attesterRuntime_block_1373`. -/
def attesterRuntime_block_1373_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1373. -/
theorem attesterRuntime_block_1373 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1373) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (attesterRuntime_block_1373_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 5) (C + ((11))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1373) rfl
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
theorem attesterRuntime_block_1373_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1373) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (attesterRuntime_block_1373_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1373 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1379. -/
theorem attesterRuntime_block_1379_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1567) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1379) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 1567) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1567) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1379_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1567) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1379_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1379. -/
theorem attesterRuntime_block_1379_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1388) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1379) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 1567) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1379_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1388) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1379_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1388_taken`. -/
def attesterRuntime_block_1388_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))))) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1388_taken`. -/
def attesterRuntime_block_1388_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 0) (UInt256.ofNat 0)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 18446744073709551615) (UInt256.ofNat 0)).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (UInt256.ofNat 0)).toByteArray.write 0 (((UInt256.ofNat 192) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1388. -/
theorem attesterRuntime_block_1388_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1388) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1480) (attesterRuntime_block_1388_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1388_taken_memory (mem := mem)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)))) (⟨32⟩ : UInt256)) rdata σ (k + 44) (C + ((139) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)))) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1379) rfl).drop 7 1388 rfl
  have r1 := r0.push1 (UInt256.ofNat 64) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 192) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 64) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 0) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) d9.head (by evm_ov)
  have d10 := d9.next 21 rfl
  have r11 := r10.and d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 32) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.add d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push1 (UInt256.ofNat 0) d15.head (by evm_ov)
  have d16 := d15.next 2 rfl
  have r17 := r16.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d16.head (by evm_ov)
  have d17 := d16.next (Nat.succ 8) rfl
  have r18 := r17.and d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := RD.genMstore r19 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push1 (UInt256.ofNat 32) d20.head (by evm_ov)
  have d21 := d20.next 2 rfl
  have r22 := r21.add d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.push1 (UInt256.ofNat 1) d22.head (by evm_ov)
  have d23 := d22.next 2 rfl
  have r24 := r23.iszero d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := r24.iszero d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.dup2 d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := RD.genMstore r26 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.push1 (UInt256.ofNat 32) d27.head (by evm_ov)
  have d28 := d27.next 2 rfl
  have r29 := r28.add d28.head (by evm_ov)
  have d29 := d28.next 1 rfl
  have r30 := r29.push1 (UInt256.ofNat 0) d29.head (by evm_ov)
  have d30 := d29.next 2 rfl
  have r31 := r30.dup1 d30.head (by evm_ov)
  have d31 := d30.next 1 rfl
  have r32 := r31.shl d31.head (by evm_ov)
  have d32 := d31.next 1 rfl
  have r33 := r32.dup2 d32.head (by evm_ov)
  have d33 := d32.next 1 rfl
  have r34 := RD.genMstore r33 d33.head (by evm_ov)
  have d34 := d33.next 1 rfl
  have r35 := r34.push1 (UInt256.ofNat 32) d34.head (by evm_ov)
  have d35 := d34.next 2 rfl
  have r36 := r35.add d35.head (by evm_ov)
  have d36 := d35.next 1 rfl
  have r37 := r36.dup7 d36.head (by evm_ov)
  have d37 := d36.next 1 rfl
  have r38 := r37.dup7 d37.head (by evm_ov)
  have d38 := d37.next 1 rfl
  have r39 := r38.dup5 d38.head (by evm_ov)
  have d39 := d38.next 1 rfl
  have r40 := r39.dup2 d39.head (by evm_ov)
  have d40 := d39.next 1 rfl
  have r41 := r40.dup2 d40.head (by evm_ov)
  have d41 := d40.next 1 rfl
  have r42 := r41.lt d41.head (by evm_ov)
  have d42 := d41.next 1 rfl
  have r43 := r42.push2 (UInt256.ofNat 1480) d42.head (by evm_ov)
  have d43 := d42.next 3 rfl
  have r44 := r43.jumpiT d43.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1480) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r44 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1388_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1388) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1480) (attesterRuntime_block_1388_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1388_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1388_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1388_fallthrough`. -/
def attesterRuntime_block_1388_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x3 :: x4 :: ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))))) :: (memLoad (UInt256.ofNat 64) mem) :: x0 :: x1 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1388_fallthrough`. -/
def attesterRuntime_block_1388_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 0) (UInt256.ofNat 0)).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 18446744073709551615) (UInt256.ofNat 0)).toByteArray.write 0 ((UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (UInt256.ofNat 0)).toByteArray.write 0 (((UInt256.ofNat 192) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1388. -/
theorem attesterRuntime_block_1388_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1388) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1473) (attesterRuntime_block_1388_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1388_fallthrough_memory (mem := mem)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)))) (⟨32⟩ : UInt256)) rdata σ (k + 44) (C + ((139) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)))) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1379) rfl).drop 7 1388 rfl
  have r1 := r0.push1 (UInt256.ofNat 64) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 192) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 64) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push1 (UInt256.ofNat 0) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  have r10 := r9.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) d9.head (by evm_ov)
  have d10 := d9.next 21 rfl
  have r11 := r10.and d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 32) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.add d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push1 (UInt256.ofNat 0) d15.head (by evm_ov)
  have d16 := d15.next 2 rfl
  have r17 := r16.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d16.head (by evm_ov)
  have d17 := d16.next (Nat.succ 8) rfl
  have r18 := r17.and d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := RD.genMstore r19 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push1 (UInt256.ofNat 32) d20.head (by evm_ov)
  have d21 := d20.next 2 rfl
  have r22 := r21.add d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.push1 (UInt256.ofNat 1) d22.head (by evm_ov)
  have d23 := d22.next 2 rfl
  have r24 := r23.iszero d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := r24.iszero d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.dup2 d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := RD.genMstore r26 d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.push1 (UInt256.ofNat 32) d27.head (by evm_ov)
  have d28 := d27.next 2 rfl
  have r29 := r28.add d28.head (by evm_ov)
  have d29 := d28.next 1 rfl
  have r30 := r29.push1 (UInt256.ofNat 0) d29.head (by evm_ov)
  have d30 := d29.next 2 rfl
  have r31 := r30.dup1 d30.head (by evm_ov)
  have d31 := d30.next 1 rfl
  have r32 := r31.shl d31.head (by evm_ov)
  have d32 := d31.next 1 rfl
  have r33 := r32.dup2 d32.head (by evm_ov)
  have d33 := d32.next 1 rfl
  have r34 := RD.genMstore r33 d33.head (by evm_ov)
  have d34 := d33.next 1 rfl
  have r35 := r34.push1 (UInt256.ofNat 32) d34.head (by evm_ov)
  have d35 := d34.next 2 rfl
  have r36 := r35.add d35.head (by evm_ov)
  have d36 := d35.next 1 rfl
  have r37 := r36.dup7 d36.head (by evm_ov)
  have d37 := d36.next 1 rfl
  have r38 := r37.dup7 d37.head (by evm_ov)
  have d38 := d37.next 1 rfl
  have r39 := r38.dup5 d38.head (by evm_ov)
  have d39 := d38.next 1 rfl
  have r40 := r39.dup2 d39.head (by evm_ov)
  have d40 := d39.next 1 rfl
  have r41 := r40.dup2 d40.head (by evm_ov)
  have d41 := d40.next 1 rfl
  have r42 := r41.lt d41.head (by evm_ov)
  have d42 := d41.next 1 rfl
  have r43 := r42.push2 (UInt256.ofNat 1480) d42.head (by evm_ov)
  have d43 := d42.next 3 rfl
  have r44 := r43.jumpiNT d43.head hcond (by evm_ov)
  exact RD.normalizeCounters r44 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1388_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.lt x0 x3) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1388) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1473) (attesterRuntime_block_1388_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1388_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1388_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1473`. -/
def attesterRuntime_block_1473_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1480) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1473. -/
theorem attesterRuntime_block_1473 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1473) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1473_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1379) rfl).drop 51 1473 rfl
  have r1 := r0.push2 (UInt256.ofNat 1480) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1473_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1473) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1473_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1473 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1480`. -/
def attesterRuntime_block_1480_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem))) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1480`. -/
def attesterRuntime_block_1480_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1480. -/
theorem attesterRuntime_block_1480 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1480) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1505) (attesterRuntime_block_1480_stack (mem := mem) (R := R)) (attesterRuntime_block_1480_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((61) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1480) rfl
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
  have r8 := r7.push1 (UInt256.ofNat 64) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := RD.genMload r8 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push1 (UInt256.ofNat 32) d9.head (by evm_ov)
  have d10 := d9.next 2 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push2 (UInt256.ofNat 1505) d11.head (by evm_ov)
  have d12 := d11.next 3 rfl
  have r13 := r12.swap2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := RD.genMstore r14 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push1 (UInt256.ofNat 32) d15.head (by evm_ov)
  have d16 := d15.next 2 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.swap1 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.jump d18.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1505) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r19 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1480_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1480) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1505) (attesterRuntime_block_1480_stack (mem := mem) (R := R)) (attesterRuntime_block_1480_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1480 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1505_taken`. -/
def attesterRuntime_block_1505_taken_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1505_taken`. -/
def attesterRuntime_block_1505_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.sub (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) (UInt256.ofNat 32)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) x1.toNat 32) ((UInt256.ofNat 32) + x1).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1505. -/
theorem attesterRuntime_block_1505_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x3 (memLoad x4 ((UInt256.ofNat 0).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.sub (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) (UInt256.ofNat 32)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) x1.toNat 32) ((UInt256.ofNat 32) + x1).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1505) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1548) (attesterRuntime_block_1505_taken_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1505_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) rdata σ (k + 29) (C + ((91) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1505) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 32) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup4 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.sub d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.sub d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := RD.genMstore r9 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap1 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push1 (UInt256.ofNat 64) d11.head (by evm_ov)
  have d12 := d11.next 2 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := RD.genMstore r14 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push1 (UInt256.ofNat 32) d15.head (by evm_ov)
  have d16 := d15.next 2 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.push1 (UInt256.ofNat 0) d17.head (by evm_ov)
  have d18 := d17.next 2 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := RD.genMstore r19 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.pop d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.dup3 d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.dup3 d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.dup2 d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := RD.genMload r24 d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.dup2 d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := r26.lt d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.push2 (UInt256.ofNat 1548) d27.head (by evm_ov)
  have d28 := d27.next 3 rfl
  have r29 := r28.jumpiT d28.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1548) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r29 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1505_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x3 (memLoad x4 ((UInt256.ofNat 0).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.sub (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) (UInt256.ofNat 32)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) x1.toNat 32) ((UInt256.ofNat 32) + x1).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1505) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1548) (attesterRuntime_block_1505_taken_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1505_taken_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1505_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1505_fallthrough`. -/
def attesterRuntime_block_1505_fallthrough_stack {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: x4 :: x2 :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1505_fallthrough`. -/
def attesterRuntime_block_1505_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.sub (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) (UInt256.ofNat 32)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) x1.toNat 32) ((UInt256.ofNat 32) + x1).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1505. -/
theorem attesterRuntime_block_1505_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x3 (memLoad x4 ((UInt256.ofNat 0).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.sub (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) (UInt256.ofNat 32)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) x1.toNat 32) ((UInt256.ofNat 32) + x1).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1505) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1541) (attesterRuntime_block_1505_fallthrough_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1505_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) rdata σ (k + 29) (C + ((91) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1505) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 32) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup4 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.sub d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.sub d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := RD.genMstore r9 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap1 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push1 (UInt256.ofNat 64) d11.head (by evm_ov)
  have d12 := d11.next 2 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := RD.genMstore r14 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push1 (UInt256.ofNat 32) d15.head (by evm_ov)
  have d16 := d15.next 2 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.push1 (UInt256.ofNat 0) d17.head (by evm_ov)
  have d18 := d17.next 2 rfl
  have r19 := r18.dup2 d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := RD.genMstore r19 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.pop d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.dup3 d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.dup3 d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.dup2 d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := RD.genMload r24 d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.dup2 d25.head (by evm_ov)
  have d26 := d25.next 1 rfl
  have r27 := r26.lt d26.head (by evm_ov)
  have d27 := d26.next 1 rfl
  have r28 := r27.push2 (UInt256.ofNat 1548) d27.head (by evm_ov)
  have d28 := d27.next 3 rfl
  have r29 := r28.jumpiNT d28.head hcond (by evm_ov)
  exact RD.normalizeCounters r29 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1505_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hcond : (UInt256.lt x3 (memLoad x4 ((UInt256.ofNat 0).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.sub (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) (UInt256.ofNat 32)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) (UInt256.ofNat 64).toNat 32) x1.toNat 32) ((UInt256.ofNat 32) + x1).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1505) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1541) (attesterRuntime_block_1505_fallthrough_stack (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_1505_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1505_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1541`. -/
def attesterRuntime_block_1541_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1548) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1541. -/
theorem attesterRuntime_block_1541 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1541) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1541_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1505) rfl).drop 29 1541 rfl
  have r1 := r0.push2 (UInt256.ofNat 1548) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1541_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1541) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1541_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1541 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1548`. -/
def attesterRuntime_block_1548_stack {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x3) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1548`. -/
def attesterRuntime_block_1548_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1548. -/
theorem attesterRuntime_block_1548 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1548) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (attesterRuntime_block_1548_stack (x3 := x3) (R := R)) (attesterRuntime_block_1548_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((50) + (memExpansionCost aw (((UInt256.mul (UInt256.ofNat 32) x0) + x1) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1548) rfl
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
  have r14 := r13.push2 (UInt256.ofNat 1379) d13.head (by evm_ov)
  have d14 := d13.next 3 rfl
  have r15 := r14.jump d14.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1379) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r15 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1548_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1548) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1379) (attesterRuntime_block_1548_stack (x3 := x3) (R := R)) (attesterRuntime_block_1548_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1548 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1567_taken`. -/
def attesterRuntime_block_1567_taken_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x11 :: x12 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1567_taken`. -/
def attesterRuntime_block_1567_taken_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1567. -/
theorem attesterRuntime_block_1567_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hcond : (UInt256.lt x5 x11) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1567) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1597) (attesterRuntime_block_1567_taken_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (attesterRuntime_block_1567_taken_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1567) rfl
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
  have r11 := r10.dup14 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup14 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup9 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.lt d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.push2 (UInt256.ofNat 1597) d16.head (by evm_ov)
  have d17 := d16.next 3 rfl
  have r18 := r17.jumpiT d17.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1597) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r18 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1567_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hcond : (UInt256.lt x5 x11) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1567) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1597) (attesterRuntime_block_1567_taken_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (attesterRuntime_block_1567_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1567_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1567_fallthrough`. -/
def attesterRuntime_block_1567_fallthrough_stack {mem : ByteArray} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: x11 :: x12 :: (memLoad (UInt256.ofNat 64) mem) :: (memLoad (UInt256.ofNat 64) mem) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1567_fallthrough`. -/
def attesterRuntime_block_1567_fallthrough_memory {mem : ByteArray} : ByteArray :=
  (((UInt256.ofNat 64) + (memLoad (UInt256.ofNat 64) mem)).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1567. -/
theorem attesterRuntime_block_1567_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hcond : (UInt256.lt x5 x11) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1567) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1590) (attesterRuntime_block_1567_fallthrough_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (attesterRuntime_block_1567_fallthrough_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((58) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1567) rfl
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
  have r11 := r10.dup14 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup14 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.dup9 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.lt d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.push2 (UInt256.ofNat 1597) d16.head (by evm_ov)
  have d17 := d16.next 3 rfl
  have r18 := r17.jumpiNT d17.head hcond (by evm_ov)
  exact RD.normalizeCounters r18 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1567_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hcond : (UInt256.lt x5 x11) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1567) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1590) (attesterRuntime_block_1567_fallthrough_stack (mem := mem) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R := R)) (attesterRuntime_block_1567_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1567_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1590`. -/
def attesterRuntime_block_1590_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1597) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1590. -/
theorem attesterRuntime_block_1590 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1590) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1590_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1567) rfl).drop 18 1590 rfl
  have r1 := r0.push2 (UInt256.ofNat 1597) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1590_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1590) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1590_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1590 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1597_taken`. -/
def attesterRuntime_block_1597_taken_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x10 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1597_taken`. -/
def attesterRuntime_block_1597_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1597. -/
theorem attesterRuntime_block_1597_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1597) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1631) (attesterRuntime_block_1597_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_1597_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1597) rfl
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
  have r22 := r21.push2 (UInt256.ofNat 1631) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiT d22.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1631) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1597_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1597) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1631) (attesterRuntime_block_1597_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_1597_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1597_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1597_fallthrough`. -/
def attesterRuntime_block_1597_fallthrough_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  (x9 :: x10 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1597_fallthrough`. -/
def attesterRuntime_block_1597_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1597. -/
theorem attesterRuntime_block_1597_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1597) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1624) (attesterRuntime_block_1597_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_1597_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) (M (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x3) (⟨32⟩ : UInt256)) x10 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1597) rfl
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
  have r22 := r21.push2 (UInt256.ofNat 1631) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiNT d22.head hcond (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1597_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.lt x9 (memLoad x10 (x5.toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.mul (UInt256.ofNat 32) x0) + x2).toNat 32)).toByteArray.write 0 mem x3.toNat 32) ((UInt256.ofNat 32) + x3).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1597) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1624) (attesterRuntime_block_1597_fallthrough_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) (attesterRuntime_block_1597_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x2 := x2) (x3 := x3) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1597_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1624`. -/
def attesterRuntime_block_1624_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1631) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1624. -/
theorem attesterRuntime_block_1624 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1624) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1624_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1597) rfl).drop 23 1624 rfl
  have r1 := r0.push2 (UInt256.ofNat 1631) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2743) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1624_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) (attesterRuntime_block_1624_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1624 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1631`. -/
def attesterRuntime_block_1631_stack {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x7) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1631`. -/
def attesterRuntime_block_1631_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 mem (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1631. -/
theorem attesterRuntime_block_1631 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1631) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1109) (attesterRuntime_block_1631_stack (x7 := x7) (R := R)) (attesterRuntime_block_1631_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((62) + (memExpansionCost aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1631) rfl
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
  have r20 := r19.push2 (UInt256.ofNat 1109) d19.head (by evm_ov)
  have d20 := d19.next 3 rfl
  have r21 := r20.jump d20.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 1109) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r21 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1631_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1631) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1109) (attesterRuntime_block_1631_stack (x7 := x7) (R := R)) (attesterRuntime_block_1631_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1631 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1657`. -/
def attesterRuntime_block_1657_stack {immWords : String → UInt256} {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: x1 :: (UInt256.ofNat 1772) :: (UInt256.ofNat 1152239886) :: (UInt256.land (immWords "_eas") (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_1657`. -/
def attesterRuntime_block_1657_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 31064325874323733141834184871827779327153766494793685066001561027745075429376).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1657. -/
theorem attesterRuntime_block_1657 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1657) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (attesterRuntime_block_1657_stack (immWords := immWords) (mem := mem) (x1 := x1) (R := R)) (attesterRuntime_block_1657_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 21) (C + ((65) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1657) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 64) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMload r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pushConst (UInt256.ofNat 31064325874323733141834184871827779327153766494793685066001561027745075429376) (width := 32) (op := .PUSH32) (by decide) d4.head (by evm_ov)
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
  have r12 := r11.push4 (UInt256.ofNat 1152239886) d11.head (by evm_ov)
  have d12 := d11.next 5 rfl
  have r13 := r12.swap1 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push2 (UInt256.ofNat 1772) d13.head (by evm_ov)
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
  have r20 := r19.push2 (UInt256.ofNat 3304) d19.head (by evm_ov)
  have d20 := d19.next 3 rfl
  have r21 := r20.jump d20.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3304) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r21 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1657_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1657) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (attesterRuntime_block_1657_stack (immWords := immWords) (mem := mem) (x1 := x1) (R := R)) (attesterRuntime_block_1657_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1657 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_1772`. -/
def attesterRuntime_block_1772_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((28) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x2 :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1772. -/
theorem attesterRuntime_block_1772 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1772) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1786) (attesterRuntime_block_1772_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 1772) rfl
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
  have r11 := RD.genGas (RD.normalizeCounters (k' := k + 10) (C' := C + ((28) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) r10 (by omega) (by omega)) d10.head (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_1772_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1772) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 1786) (attesterRuntime_block_1772_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_1772 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1786: call (0xf1). No RD transition is asserted. Summaries resume at pc 1787 from a fresh symbolic RD state. -/

end attesterRuntimeBlocks
