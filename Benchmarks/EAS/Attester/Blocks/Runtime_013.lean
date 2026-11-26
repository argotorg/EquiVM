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

/-- Final stack for bytecode block summary `attesterRuntime_block_3624`. -/
def attesterRuntime_block_3624_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3631) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3624. -/
theorem attesterRuntime_block_3624 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3624_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3605) rfl).drop 9 3624 rfl
  have r1 := r0.push2 (UInt256.ofNat 3631) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2696) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2696) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3624_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3624_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3624 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3631_taken`. -/
def attesterRuntime_block_3631_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3631. -/
theorem attesterRuntime_block_3631_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (attesterRuntime_block_3631_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3631) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 5) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.shl d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 64) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := RD.genMload r5 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) d6.head (by evm_ov)
  have d7 := d6.next (Nat.succ 32) rfl
  have r8 := r7.push1 (UInt256.ofNat 63) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.dup4 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.and d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.add d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.lt d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d16.head (by evm_ov)
  have d17 := d16.next (Nat.succ 8) rfl
  have r18 := r17.dup3 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.gt d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.or d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.iszero d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.push2 (UInt256.ofNat 3706) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiT d22.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3706) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3631_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (attesterRuntime_block_3631_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3631_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3631_fallthrough`. -/
def attesterRuntime_block_3631_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.shiftLeft x0 (UInt256.ofNat 5)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3631. -/
theorem attesterRuntime_block_3631_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) (attesterRuntime_block_3631_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((74) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3631) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.push1 (UInt256.ofNat 5) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := r3.shl d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 64) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := RD.genMload r5 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) (width := 32) (op := .PUSH32) (by decide) d6.head (by evm_ov)
  have d7 := d6.next (Nat.succ 32) rfl
  have r8 := r7.push1 (UInt256.ofNat 63) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.dup4 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.and d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.dup2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.add d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.dup2 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.lt d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d16.head (by evm_ov)
  have d17 := d16.next (Nat.succ 8) rfl
  have r18 := r17.dup3 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.gt d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.or d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.iszero d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.push2 (UInt256.ofNat 3706) d21.head (by evm_ov)
  have d22 := d21.next 3 rfl
  have r23 := r22.jumpiNT d22.head hcond (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3631_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (UInt256.ofNat 18446744073709551615)) (UInt256.lt ((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.shiftLeft x0 (UInt256.ofNat 5)) + (UInt256.ofNat 63)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904))) (memLoad (UInt256.ofNat 64) mem)))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3631) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) (attesterRuntime_block_3631_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3631_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3699`. -/
def attesterRuntime_block_3699_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3706) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3699. -/
theorem attesterRuntime_block_3699 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) R mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3699_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3631) rfl).drop 23 3699 rfl
  have r1 := r0.push2 (UInt256.ofNat 3706) d0.head (by evm_ov)
  have d1 := d0.next 3 rfl
  have r2 := r1.push2 (UInt256.ofNat 2696) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.jump d2.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2696) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3699_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3699) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) (attesterRuntime_block_3699_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3699 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3706_taken`. -/
def attesterRuntime_block_3706_taken_stack {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 32)) :: x1 :: x2 :: ((UInt256.ofNat 32) + (x4 + x2)) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3706_taken`. -/
def attesterRuntime_block_3706_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3706. -/
theorem attesterRuntime_block_3706_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (attesterRuntime_block_3706_taken_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3706) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMstore r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap2 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup3 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := RD.genMstore r5 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 32) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup5 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.swap3 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.swap1 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.add d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup8 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.dup5 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.gt d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.iszero d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push2 (UInt256.ofNat 3736) d20.head (by evm_ov)
  have d21 := d20.next 3 rfl
  have r22 := r21.jumpiT d21.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3736) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r22 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3706_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (attesterRuntime_block_3706_taken_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3706_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3706_fallthrough`. -/
def attesterRuntime_block_3706_fallthrough_stack {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 32)) :: x1 :: x2 :: ((UInt256.ofNat 32) + (x4 + x2)) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3706_fallthrough`. -/
def attesterRuntime_block_3706_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} : ByteArray :=
  (x3.toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3706. -/
theorem attesterRuntime_block_3706_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) (attesterRuntime_block_3706_fallthrough_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((71) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3706) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 64) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := RD.genMstore r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap2 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup3 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := RD.genMstore r5 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 32) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.dup2 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup5 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.swap3 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.swap1 d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.dup2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.add d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.dup8 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.dup5 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.gt d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := r19.iszero d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push2 (UInt256.ofNat 3736) d20.head (by evm_ov)
  have d21 := d20.next 3 rfl
  have r22 := r21.jumpiNT d21.head hcond (by evm_ov)
  exact RD.normalizeCounters r22 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3706_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt ((UInt256.ofNat 32) + (x4 + x2)) x7)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3706) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) (attesterRuntime_block_3706_fallthrough_stack (x1 := x1) (x2 := x2) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (attesterRuntime_block_3706_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3706_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3732. -/
theorem attesterRuntime_block_3732 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3732) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3706) rfl).drop 22 3732 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3736`. -/
def attesterRuntime_block_3736_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x2 :: x3 :: (x4 + (UInt256.ofNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3736. -/
theorem attesterRuntime_block_3736 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3736_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ (k + 6) (C + ((15))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3736) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.add d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap5 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3736_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3736) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3736_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3736 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3743. -/
theorem attesterRuntime_block_3743_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3743) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup4 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 3771) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3771) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3743_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3743_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3743. -/
theorem attesterRuntime_block_3743_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3743) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.dup4 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.lt d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.iszero d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push2 (UInt256.ofNat 3771) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3743_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x4 x3)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3743_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3752`. -/
def attesterRuntime_block_3752_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + x0) :: x1 :: (memLoad x4 mem) :: x3 :: ((UInt256.ofNat 32) + x4) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3752`. -/
def attesterRuntime_block_3752_memory {mem : ByteArray} {x0 : UInt256} {x4 : UInt256} : ByteArray :=
  ((memLoad x4 mem).toByteArray.write 0 mem x0.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3752. -/
theorem attesterRuntime_block_3752 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3752_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_3752_memory (mem := mem) (x0 := x0) (x4 := x4)) (M (M aw x4 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((52) + (memExpansionCost aw x4 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x4 (⟨32⟩ : UInt256)) x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3743) rfl).drop 7 3752 rfl
  have r1 := r0.dup5 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := RD.genMstore r4 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.push1 (UInt256.ofNat 32) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := r6.swap6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup7 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.add d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.swap6 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap1 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.swap4 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.pop d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.add d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.push2 (UInt256.ofNat 3743) d14.head (by evm_ov)
  have d15 := d14.next 3 rfl
  have r16 := r15.jump d15.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3743) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r16 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3752_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3752) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3743) (attesterRuntime_block_3752_stack (mem := mem) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (attesterRuntime_block_3752_memory (mem := mem) (x0 := x0) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3752 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3771`. -/
def attesterRuntime_block_3771_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3771. -/
theorem attesterRuntime_block_3771 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3771_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((29))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3771) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap7 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap6 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
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
  have r11 := r10.jump d10.head hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3771_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x8 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3771) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x8 (attesterRuntime_block_3771_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3771 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3782`. -/
def attesterRuntime_block_3782_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x1 + (UInt256.ofNat 32)) ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) :: (x0 + (UInt256.ofNat 96)) :: (UInt256.ofNat 3819) :: (memLoad (x1 + (UInt256.ofNat 32)) ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_3782`. -/
def attesterRuntime_block_3782_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 64).toByteArray.write 0 ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32) (x0 + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3782. -/
theorem attesterRuntime_block_3782 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3782) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3782_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3782_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) rdata σ (k + 27) (C + ((84) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3782) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := RD.genMstore r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup2 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := RD.genMload r5 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 32) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.dup3 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.add d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := RD.genMstore r9 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.push1 (UInt256.ofNat 0) d10.head (by evm_ov)
  have d11 := d10.next 2 rfl
  have r12 := r11.push1 (UInt256.ofNat 32) d11.head (by evm_ov)
  have d12 := d11.next 2 rfl
  have r13 := r12.dup4 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.add d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := RD.genMload r14 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push1 (UInt256.ofNat 64) d15.head (by evm_ov)
  have d16 := d15.next 2 rfl
  have r17 := r16.dup1 d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.dup5 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.add d18.head (by evm_ov)
  have d19 := d18.next 1 rfl
  have r20 := RD.genMstore r19 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.push2 (UInt256.ofNat 3819) d20.head (by evm_ov)
  have d21 := d20.next 3 rfl
  have r22 := r21.push1 (UInt256.ofNat 96) d21.head (by evm_ov)
  have d22 := d21.next 2 rfl
  have r23 := r22.dup5 d22.head (by evm_ov)
  have d23 := d22.next 1 rfl
  have r24 := r23.add d23.head (by evm_ov)
  have d24 := d23.next 1 rfl
  have r25 := r24.dup3 d24.head (by evm_ov)
  have d25 := d24.next 1 rfl
  have r26 := r25.push2 (UInt256.ofNat 3109) d25.head (by evm_ov)
  have d26 := d25.next 3 rfl
  have r27 := r26.jump d26.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3109) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r27 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3782_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3782) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3109) (attesterRuntime_block_3782_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_3782_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3782 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3819`. -/
def attesterRuntime_block_3819_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3819. -/
theorem attesterRuntime_block_3819 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x5 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3819) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x5 (attesterRuntime_block_3819_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((23))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3819) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap5 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap4 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pop d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.pop d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pop d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.jump d7.head hvalid (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3819_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x5 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3819) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x5 (attesterRuntime_block_3819_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3819 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3827_taken`. -/
def attesterRuntime_block_3827_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3827. -/
theorem attesterRuntime_block_3827_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (attesterRuntime_block_3827_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3827) rfl
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
  have r9 := r8.push2 (UInt256.ofNat 3845) d8.head (by evm_ov)
  have d9 := d8.next 3 rfl
  have r10 := r9.jumpiT d9.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 3845) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3827_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (attesterRuntime_block_3827_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3827_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_3827_fallthrough`. -/
def attesterRuntime_block_3827_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3827. -/
theorem attesterRuntime_block_3827_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) (attesterRuntime_block_3827_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((35))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3827) rfl
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
  have r9 := r8.push2 (UInt256.ofNat 3845) d8.head (by evm_ov)
  have d9 := d8.next 3 rfl
  have r10 := r9.jumpiNT d9.head hcond (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3827_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3827) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) (attesterRuntime_block_3827_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3827_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3841. -/
theorem attesterRuntime_block_3841 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3841) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3827) rfl).drop 10 3841 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_3845`. -/
def attesterRuntime_block_3845_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3845. -/
theorem attesterRuntime_block_3845 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x3 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x3 (attesterRuntime_block_3845_stack (mem := mem) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((22) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3845) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := RD.genMload r2 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap2 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap1 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.jump d6.head hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_3845_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x3 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3845) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x3 (attesterRuntime_block_3845_stack (mem := mem) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_3845 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3852. -/
theorem attesterRuntime_block_3852 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 3852) R mem aw rdata σ k C)
    : RDinvalid fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 3845) rfl).drop 7 3852 rfl
  exact RD.invalid r0 d0.head

end attesterRuntimeBlocks
