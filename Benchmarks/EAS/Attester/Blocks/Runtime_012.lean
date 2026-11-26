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

/-- Final stack for bytecode block summary `attesterRuntime_block_3304`. -/
def attesterRuntime_block_3304_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (x1 + (UInt256.ofNat 32)) :: (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) :: (x0 + (UInt256.ofNat 64)) :: ((x0 + (UInt256.shiftLeft (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) (UInt256.ofNat 5))) + (UInt256.ofNat 64)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3304`. -/
def attesterRuntime_block_3304_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3304. -/
theorem attesterRuntime_block_3304 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3304_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3304_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((92) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3304) rfl
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
theorem attesterRuntime_block_3304_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3304) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3304_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3304_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3304 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3344. -/
theorem attesterRuntime_block_3344_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3344) rfl
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
theorem attesterRuntime_block_3344_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3097) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3344_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3344. -/
theorem attesterRuntime_block_3344_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3344) rfl
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
theorem attesterRuntime_block_3344_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x2)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3344_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3353`. -/
def attesterRuntime_block_3353_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) :: (x4 + (UInt256.ofNat 96)) :: ((UInt256.ofNat 96) + (x4 + (UInt256.shiftLeft (memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 5)))) :: ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32))) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3353`. -/
def attesterRuntime_block_3353_memory {mem : ByteArray} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x6 : UInt256} : ByteArray :=
  ((memLoad (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32) (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3353. -/
theorem attesterRuntime_block_3353 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3353_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_3353_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) (M (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 51) (C + ((153) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw x3 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (memLoad ((UInt256.ofNat 32) + (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32))) ((memLoad (memLoad x1 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)) (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32)).toByteArray.write 0 (((UInt256.sub x4 x6) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872)).toByteArray.write 0 mem x3.toNat 32) x4.toNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3344) rfl).drop 7 3353 rfl
  have r1 := r0.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639872) (width := 32) (op := .PUSH32) (by decide) d0.head (by evm_ov)
  have d1 := d0.next (Nat.succ 32) rfl
  have r2 := r1.dup8 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup7 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.sub d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
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
  have r37 := r36.push1 (UInt256.ofNat 96) d36.head (by evm_ov)
  have d37 := d36.next 2 rfl
  have r38 := r37.push1 (UInt256.ofNat 5) d37.head (by evm_ov)
  have d38 := d37.next 2 rfl
  have r39 := r38.dup3 d38.head (by evm_ov)
  have d39 := d38.next 1 rfl
  have r40 := r39.swap1 d39.head (by evm_ov)
  have d40 := d39.next 1 rfl
  have r41 := r40.shl d40.head (by evm_ov)
  have d41 := d40.next 1 rfl
  have r42 := r41.dup9 d41.head (by evm_ov)
  have d42 := d41.next 1 rfl
  have r43 := r42.add d42.head (by evm_ov)
  have d43 := d42.next 1 rfl
  have r44 := r43.dup2 d43.head (by evm_ov)
  have d44 := d43.next 1 rfl
  have r45 := r44.add d44.head (by evm_ov)
  have d45 := d44.next 1 rfl
  have r46 := r45.swap2 d45.head (by evm_ov)
  have d46 := d45.next 1 rfl
  have r47 := r46.swap1 d46.head (by evm_ov)
  have d47 := d46.next 1 rfl
  have r48 := r47.dup9 d47.head (by evm_ov)
  have d48 := d47.next 1 rfl
  have r49 := r48.add d48.head (by evm_ov)
  have d49 := d48.next 1 rfl
  have r50 := r49.swap1 d49.head (by evm_ov)
  have d50 := d49.next 1 rfl
  have r51 := r50.push1 (UInt256.ofNat 0) d50.head (by evm_ov)
  exact RD.normalizeCounters r51 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3353_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3353) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3353_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (attesterRuntime_block_3353_memory (mem := mem) (x1 := x1) (x3 := x3) (x4 := x4) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3353 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3441. -/
theorem attesterRuntime_block_3441_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3441) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 3521) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3521) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3441_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3441_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3441. -/
theorem attesterRuntime_block_3441_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3441) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 3521) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3441_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3441_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3450`. -/
def attesterRuntime_block_3450_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x4 (((UInt256.sub x3 x9) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840)).toByteArray.write 0 mem x2.toNat 32)) :: x3 :: (UInt256.ofNat 3499) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3450`. -/
def attesterRuntime_block_3450_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} {x9 : UInt256} : ByteArray :=
  (((UInt256.sub x3 x9) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840)).toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3450. -/
theorem attesterRuntime_block_3450 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3450_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (attesterRuntime_block_3450_memory (mem := mem) (x2 := x2) (x3 := x3) (x9 := x9)) (M (M aw x2 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x2 (⟨32⟩ : UInt256)) x4 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3441) rfl).drop 7 3450 rfl
  have r1 := r0.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639840) (width := 32) (op := .PUSH32) (by decide) d0.head (by evm_ov)
  have d1 := d0.next (Nat.succ 32) rfl
  have r2 := r1.dup11 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.sub d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup4 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 3499) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.dup5 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup7 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := RD.genMload r10 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.push2 (UInt256.ofNat 3109) d11.head (by evm_ov)
  have d12 := d11.next 3 rfl
  have r13 := r12.jump d12.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3109) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r13 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3450_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3450) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3450_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (attesterRuntime_block_3450_memory (mem := mem) (x2 := x2) (x3 := x3) (x9 := x9)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3450 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3499`. -/
def attesterRuntime_block_3499_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x1) :: x2 :: ((UInt256.ofNat 32) + x3) :: x0 :: ((UInt256.ofNat 32) + x5) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3499. -/
theorem attesterRuntime_block_3499 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3499) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3499_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) mem aw rdata σ (k + 18) (C + ((56))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3499) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.swap6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup7 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.add d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.swap6 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.swap1 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.swap5 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.pop d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.swap3 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap1 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.swap3 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.add d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.swap2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push1 (UInt256.ofNat 1) d14.head (by evm_ov)
  have d15 := d14.next 2 rfl
  have r16 := r15.add d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.push2 (UInt256.ofNat 3441) d16.head (by evm_ov)
  have d17 := d16.next 3 rfl
  have r18 := r17.jump d17.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3441) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r18 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3499_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3499) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3441) (attesterRuntime_block_3499_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3499 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3521`. -/
def attesterRuntime_block_3521_stack {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x5) :: ((UInt256.ofNat 32) + x6) :: x7 :: ((UInt256.ofNat 32) + x8) :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3521. -/
theorem attesterRuntime_block_3521 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3521_stack (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 22) (C + ((64))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3521) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap8 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pop d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 32) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.swap5 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.dup6 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.add d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.swap5 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.swap3 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.swap1 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.swap3 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.add d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.swap2 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.pop d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.push1 (UInt256.ofNat 1) d18.head (by evm_ov)
  have d19 := d18.next 2 rfl
  have r20 := r19.add d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push2 (UInt256.ofNat 3344) d20.head (by evm_ov)
  have d21 := d20.next 3 rfl
  have r22 := r21.jump d21.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3344) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r22 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3521_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3521) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3344) (attesterRuntime_block_3521_stack (x3 := x3) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3521 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3547_taken`. -/
def attesterRuntime_block_3547_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3547. -/
theorem attesterRuntime_block_3547_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (attesterRuntime_block_3547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3547) rfl
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
  have r9 := r8.push2 (UInt256.ofNat 3565) d8.head (by evm_ov)
  have d9 := d8.next 3 rfl
  have r10 := r9.jumpiT d9.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3565) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3547_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (attesterRuntime_block_3547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3547_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3547_fallthrough`. -/
def attesterRuntime_block_3547_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3547. -/
theorem attesterRuntime_block_3547_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) (attesterRuntime_block_3547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3547) rfl
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
  have r9 := r8.push2 (UInt256.ofNat 3565) d8.head (by evm_ov)
  have d9 := d8.next 3 rfl
  have r10 := r9.jumpiNT d9.head hcond (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3547_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) (attesterRuntime_block_3547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3547_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3561. -/
theorem attesterRuntime_block_3561 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3561) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3547) rfl).drop 10 3561 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3565_taken`. -/
def attesterRuntime_block_3565_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3565. -/
theorem attesterRuntime_block_3565_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (attesterRuntime_block_3565_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3565) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup2 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d3.head (by evm_ov)
  have d4 := d3.next (Nat.succ 8) rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.gt d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.iszero d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 3588) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiT d8.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3588) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3565_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (attesterRuntime_block_3565_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3565_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3565_fallthrough`. -/
def attesterRuntime_block_3565_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3565. -/
theorem attesterRuntime_block_3565_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) (attesterRuntime_block_3565_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3565) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup2 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d3.head (by evm_ov)
  have d4 := d3.next (Nat.succ 8) rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.gt d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.iszero d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 3588) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiNT d8.head hcond (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3565_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x1 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3565) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) (attesterRuntime_block_3565_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3565_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3584. -/
theorem attesterRuntime_block_3584 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3584) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3565) rfl).drop 9 3584 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3588_taken`. -/
def attesterRuntime_block_3588_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x2 + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3588. -/
theorem attesterRuntime_block_3588_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (attesterRuntime_block_3588_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3588) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup3 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.add d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 31) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.dup5 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.sgt d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push2 (UInt256.ofNat 3605) d8.head (by evm_ov)
  have d9 := d8.next 3 rfl
  have r10 := r9.jumpiT d9.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3605) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3588_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (attesterRuntime_block_3588_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3588_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3588_fallthrough`. -/
def attesterRuntime_block_3588_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x2 + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3588. -/
theorem attesterRuntime_block_3588_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) (attesterRuntime_block_3588_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3588) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup3 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.add d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 31) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.dup5 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.sgt d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.push2 (UInt256.ofNat 3605) d8.head (by evm_ov)
  have d9 := d8.next 3 rfl
  have r10 := r9.jumpiNT d9.head hcond (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3588_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sgt x3 ((x2 + x0) + (UInt256.ofNat 31))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3588) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) (attesterRuntime_block_3588_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3588_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3601. -/
theorem attesterRuntime_block_3601 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3601) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3588) rfl).drop 10 3601 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3605_taken`. -/
def attesterRuntime_block_3605_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3605. -/
theorem attesterRuntime_block_3605_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (attesterRuntime_block_3605_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3605) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d3.head (by evm_ov)
  have d4 := d3.next (Nat.succ 8) rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.gt d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.iszero d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 3631) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiT d8.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3631) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3605_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (attesterRuntime_block_3605_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3605_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3605_fallthrough`. -/
def attesterRuntime_block_3605_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3605. -/
theorem attesterRuntime_block_3605_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) (attesterRuntime_block_3605_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3605) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d3.head (by evm_ov)
  have d4 := d3.next (Nat.succ 8) rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.gt d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.iszero d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push2 (UInt256.ofNat 3631) d7.head (by evm_ov)
  have d8 := d7.next 3 rfl
  have r9 := r8.jumpiNT d8.head hcond (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3605_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (memLoad x0 mem) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3605) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) (attesterRuntime_block_3605_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3605_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
