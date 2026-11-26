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

/-- Final stack for bytecode block summary `attesterRuntime_block_2539_taken`. -/
def attesterRuntime_block_2539_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x7 + (UInt256.ofNat 32)).toNat 32)) :: x3 :: x4 :: x0 :: x1 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2539. -/
theorem attesterRuntime_block_2539_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x7 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2539) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2571) (attesterRuntime_block_2539_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x7 := x7) (R := R)) mem aw rdata σ (k + 17) (C + ((53))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2539) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pop d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap4 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pop d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 32) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.dup6 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.calldataload d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d11.head (by evm_ov)
  have d12 := d11.next (Nat.succ 8) rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.gt d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.iszero d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push2 (UInt256.ofNat 2571) d15.head (by evm_ov)
  have d16 := d15.next 3 rfl
  have r17 := r16.jumpiT d16.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2571) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2539_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x7 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2539) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2571) (attesterRuntime_block_2539_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2539_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2539_fallthrough`. -/
def attesterRuntime_block_2539_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x7 + (UInt256.ofNat 32)).toNat 32)) :: x3 :: x4 :: x0 :: x1 :: x7 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2539. -/
theorem attesterRuntime_block_2539_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x7 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2539) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2567) (attesterRuntime_block_2539_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x7 := x7) (R := R)) mem aw rdata σ (k + 17) (C + ((53))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2539) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap6 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.pop d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap4 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.pop d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 32) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.dup6 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.calldataload d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) d11.head (by evm_ov)
  have d12 := d11.next (Nat.succ 8) rfl
  have r13 := r12.dup2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.gt d13.head (by evm_ov)
  have d14 := d13.next 1 rfl
  have r15 := r14.iszero d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push2 (UInt256.ofNat 2571) d15.head (by evm_ov)
  have d16 := d15.next 3 rfl
  have r17 := r16.jumpiNT d16.head hcond (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2539_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x7 + (UInt256.ofNat 32)).toNat 32)) (UInt256.ofNat 18446744073709551615))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2539) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2567) (attesterRuntime_block_2539_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x3 := x3) (x4 := x4) (x7 := x7) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2539_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2567. -/
theorem attesterRuntime_block_2567 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2567) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2539) rfl).drop 17 2567 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_2571`. -/
def attesterRuntime_block_2571_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x5 + x0) :: x6 :: (UInt256.ofNat 2583) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2571. -/
theorem attesterRuntime_block_2571 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2571) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2406) (attesterRuntime_block_2571_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 8) (C + ((27))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2571) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push2 (UInt256.ofNat 2583) d1.head (by evm_ov)
  have d2 := d1.next 3 rfl
  have r3 := r2.dup8 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.dup9 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.add d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push2 (UInt256.ofNat 2406) d6.head (by evm_ov)
  have d7 := d6.next 3 rfl
  have r8 := r7.jump d7.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2406) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r8 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2571_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2571) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2406) (attesterRuntime_block_2571_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2571 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2583`. -/
def attesterRuntime_block_2583_stack {x0 : UInt256} {x1 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x1 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2583. -/
theorem attesterRuntime_block_2583 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x9 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2583) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x9 (attesterRuntime_block_2583_stack (x0 := x0) (x1 := x1) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata σ (k + 12) (C + ((34))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2583) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.swap6 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap9 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap5 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap8 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pop d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.swap6 d6.head (by evm_ov)
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
theorem attesterRuntime_block_2583_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x9 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2583) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x9 (attesterRuntime_block_2583_stack (x0 := x0) (x1 := x1) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2583 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2595`. -/
def attesterRuntime_block_2595_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)) :: (x0 + (UInt256.ofNat 64)) :: (x1 + (UInt256.ofNat 32)) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_2595`. -/
def attesterRuntime_block_2595_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((memLoad x1 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32)).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem x0.toNat 32) ((UInt256.ofNat 32) + x0).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2595. -/
theorem attesterRuntime_block_2595 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2595) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (attesterRuntime_block_2595_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_2595_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((67) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + x0) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2595) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 32) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := RD.genMstore r4 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup3 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := RD.genMload r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.dup3 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.dup3 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.swap1 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := RD.genMstore r12 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 0) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.swap2 d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.dup5 d15.head (by evm_ov)
  have d16 := d15.next 1 rfl
  have r17 := r16.add d16.head (by evm_ov)
  have d17 := d16.next 1 rfl
  have r18 := r17.swap1 d17.head (by evm_ov)
  have d18 := d17.next 1 rfl
  have r19 := r18.push1 (UInt256.ofNat 64) d18.head (by evm_ov)
  have d19 := d18.next 2 rfl
  have r20 := r19.dup5 d19.head (by evm_ov)
  have d20 := d19.next 1 rfl
  have r21 := r20.add d20.head (by evm_ov)
  have d21 := d20.next 1 rfl
  have r22 := r21.swap1 d21.head (by evm_ov)
  have d22 := d21.next 1 rfl
  have r23 := r22.dup4 d22.head (by evm_ov)
  exact RD.normalizeCounters r23 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2595_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2595) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (attesterRuntime_block_2595_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (attesterRuntime_block_2595_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2595 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2621. -/
theorem attesterRuntime_block_2621_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2651) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2621) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 2651) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiT d6.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2651) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2621_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2651) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2621_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2621. -/
theorem attesterRuntime_block_2621_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2630) (x0 :: x1 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2621) rfl
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
  have r6 := r5.push2 (UInt256.ofNat 2651) d5.head (by evm_ov)
  have d6 := d5.next 3 rfl
  have r7 := r6.jumpiNT d6.head hcond (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2621_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2630) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2621_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2630`. -/
def attesterRuntime_block_2630_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: (x2 + (UInt256.ofNat 32)) :: ((UInt256.ofNat 32) + x3) :: R)

/-- Final memory for bytecode block summary `attesterRuntime_block_2630`. -/
def attesterRuntime_block_2630_memory {mem : ByteArray} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  ((memLoad x3 mem).toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2630. -/
theorem attesterRuntime_block_2630 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2630) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (attesterRuntime_block_2630_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (attesterRuntime_block_2630_memory (mem := mem) (x2 := x2) (x3 := x3)) (M (M aw x3 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((56) + (memExpansionCost aw x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x3 (⟨32⟩ : UInt256)) x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2621) rfl).drop 7 2630 rfl
  have r1 := r0.dup4 d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := RD.genMload r1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.dup4 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := RD.genMstore r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 32) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := r5.swap4 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.dup5 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.add d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.swap4 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.swap1 d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.swap3 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.add d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.swap2 d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.push1 (UInt256.ofNat 1) d13.head (by evm_ov)
  have d14 := d13.next 2 rfl
  have r15 := r14.add d14.head (by evm_ov)
  have d15 := d14.next 1 rfl
  have r16 := r15.push2 (UInt256.ofNat 2621) d15.head (by evm_ov)
  have d16 := d15.next 3 rfl
  have r17 := r16.jump d16.head (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2621) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2630_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2630) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2621) (attesterRuntime_block_2630_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (attesterRuntime_block_2630_memory (mem := mem) (x2 := x2) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2630 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2651`. -/
def attesterRuntime_block_2651_stack {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2651. -/
theorem attesterRuntime_block_2651 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x7 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2651) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x7 (attesterRuntime_block_2651_stack (x2 := x2) (R := R)) mem aw rdata σ (k + 11) (C + ((30))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2651) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.swap1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.swap6 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.swap5 d4.head (by evm_ov)
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
theorem attesterRuntime_block_2651_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x7 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2651) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x7 (attesterRuntime_block_2651_stack (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2651 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2662_taken`. -/
def attesterRuntime_block_2662_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2662. -/
theorem attesterRuntime_block_2662_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2681) (attesterRuntime_block_2662_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2662) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 64) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.dup4 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup6 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.sub d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.slt d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.iszero d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push2 (UInt256.ofNat 2681) d9.head (by evm_ov)
  have d10 := d9.next 3 rfl
  have r11 := r10.jumpiT d10.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2681) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2662_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2681) (attesterRuntime_block_2662_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2662_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2662_fallthrough`. -/
def attesterRuntime_block_2662_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2662. -/
theorem attesterRuntime_block_2662_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2677) (attesterRuntime_block_2662_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((38))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2662) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.push1 (UInt256.ofNat 64) d3.head (by evm_ov)
  have d4 := d3.next 2 rfl
  have r5 := r4.dup4 d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.dup6 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.sub d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.slt d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.iszero d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.push2 (UInt256.ofNat 2681) d9.head (by evm_ov)
  have d10 := d9.next 3 rfl
  have r11 := r10.jumpiNT d10.head hcond (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2662_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2677) (attesterRuntime_block_2662_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2662_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2677. -/
theorem attesterRuntime_block_2677 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2677) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2662) rfl).drop 11 2677 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_2681`. -/
def attesterRuntime_block_2681_stack {ee : ExecutionEnv} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x2 + (UInt256.ofNat 32)).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2681. -/
theorem attesterRuntime_block_2681 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x4 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2681) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x4 (attesterRuntime_block_2681_stack (ee := ee) (x2 := x2) (R := R)) mem aw rdata σ (k + 14) (C + ((42))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2681) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pop d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  have r3 := r2.pop d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup1 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.calldataload d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.swap3 d5.head (by evm_ov)
  have d6 := d5.next 1 rfl
  have r7 := r6.push1 (UInt256.ofNat 32) d6.head (by evm_ov)
  have d7 := d6.next 2 rfl
  have r8 := r7.swap1 d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.swap2 d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.calldataload d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.swap2 d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.pop d12.head (by evm_ov)
  have d13 := d12.next 1 rfl
  have r14 := r13.jump d13.head hvalid (by evm_ov)
  exact RD.normalizeCounters r14 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2681_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) 0).contains x4 = true)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2681) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 x4 (attesterRuntime_block_2681_stack (ee := ee) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2681 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2696. -/
theorem attesterRuntime_block_2696 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2696) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2696) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pushConst (UInt256.ofNat 35408467139433450592217433187231851964531694900788300625387963629091585785856) (width := 32) (op := .PUSH32) (by decide) d1.head (by evm_ov)
  have d2 := d1.next (Nat.succ 32) rfl
  have r3 := r2.push1 (UInt256.ofNat 0) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMstore r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 65) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := r5.push1 (UInt256.ofNat 4) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 36) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.push1 (UInt256.ofNat 0) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  exact RD.genRev r9 d9.head (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 2743. -/
theorem attesterRuntime_block_2743 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2743) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2743) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.pushConst (UInt256.ofNat 35408467139433450592217433187231851964531694900788300625387963629091585785856) (width := 32) (op := .PUSH32) (by decide) d1.head (by evm_ov)
  have d2 := d1.next (Nat.succ 32) rfl
  have r3 := r2.push1 (UInt256.ofNat 0) d2.head (by evm_ov)
  have d3 := d2.next 2 rfl
  have r4 := RD.genMstore r3 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.push1 (UInt256.ofNat 50) d4.head (by evm_ov)
  have d5 := d4.next 2 rfl
  have r6 := r5.push1 (UInt256.ofNat 4) d5.head (by evm_ov)
  have d6 := d5.next 2 rfl
  have r7 := RD.genMstore r6 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.push1 (UInt256.ofNat 36) d7.head (by evm_ov)
  have d8 := d7.next 2 rfl
  have r9 := r8.push1 (UInt256.ofNat 0) d8.head (by evm_ov)
  have d9 := d8.next 2 rfl
  exact RD.genRev r9 d9.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_2790_taken`. -/
def attesterRuntime_block_2790_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2790. -/
theorem attesterRuntime_block_2790_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2790) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (attesterRuntime_block_2790_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((46))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2790) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup4 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.calldataload d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905) (width := 32) (op := .PUSH32) (by decide) d5.head (by evm_ov)
  have d6 := d5.next (Nat.succ 32) rfl
  have r7 := r6.dup5 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.calldatasize d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.sub d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.slt d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.push2 (UInt256.ofNat 2843) d12.head (by evm_ov)
  have d13 := d12.next 3 rfl
  have r14 := r13.jumpiT d13.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2843) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r14 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2790_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2790) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (attesterRuntime_block_2790_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2790_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `attesterRuntime_block_2790_fallthrough`. -/
def attesterRuntime_block_2790_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2790. -/
theorem attesterRuntime_block_2790_fallthrough {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2790) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2839) (attesterRuntime_block_2790_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((46))) := by
  let r0 := h
  have d0 := Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2790) rfl
  have r1 := r0.jumpdest d0.head (by evm_ov)
  have d1 := d0.next 1 rfl
  have r2 := r1.push1 (UInt256.ofNat 0) d1.head (by evm_ov)
  have d2 := d1.next 2 rfl
  have r3 := r2.dup1 d2.head (by evm_ov)
  have d3 := d2.next 1 rfl
  have r4 := r3.dup4 d3.head (by evm_ov)
  have d4 := d3.next 1 rfl
  have r5 := r4.calldataload d4.head (by evm_ov)
  have d5 := d4.next 1 rfl
  have r6 := r5.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905) (width := 32) (op := .PUSH32) (by decide) d5.head (by evm_ov)
  have d6 := d5.next (Nat.succ 32) rfl
  have r7 := r6.dup5 d6.head (by evm_ov)
  have d7 := d6.next 1 rfl
  have r8 := r7.calldatasize d7.head (by evm_ov)
  have d8 := d7.next 1 rfl
  have r9 := r8.sub d8.head (by evm_ov)
  have d9 := d8.next 1 rfl
  have r10 := r9.add d9.head (by evm_ov)
  have d10 := d9.next 1 rfl
  have r11 := r10.dup2 d10.head (by evm_ov)
  have d11 := d10.next 1 rfl
  have r12 := r11.slt d11.head (by evm_ov)
  have d12 := d11.next 1 rfl
  have r13 := r12.push2 (UInt256.ofNat 2843) d12.head (by evm_ov)
  have d13 := d12.next 3 rfl
  have r14 := r13.jumpiNT d13.head hcond (by evm_ov)
  exact RD.normalizeCounters r14 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2790_fallthrough_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.slt (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) ((UInt256.sub (UInt256.ofNat ee.calldata.size) x0) + (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905))) = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2790) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2839) (attesterRuntime_block_2790_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2790_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2839. -/
theorem attesterRuntime_block_2839 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2839) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) g s0 := by
  let r0 := h
  have d0 := (Benchmarks.EAS.Attester.Bytecode.decodes_code immWords (t := 2790) rfl).drop 14 2839 rfl
  have r1 := r0.push1 (UInt256.ofNat 0) d0.head (by evm_ov)
  have d1 := d0.next 2 rfl
  have r2 := r1.dup1 d1.head (by evm_ov)
  have d2 := d1.next 1 rfl
  exact RD.genRev r2 d2.head (by evm_ov)

/-- Final stack for bytecode block summary `attesterRuntime_block_2843_taken`. -/
def attesterRuntime_block_2843_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x3 + x0) :: (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2843. -/
theorem attesterRuntime_block_2843_taken {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (attesterRuntime_block_2843_taken_stack (ee := ee) (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
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
  have r13 := r12.jumpiT d12.head hcond (Benchmarks.EAS.Attester.Bytecode.jumpdest_code immWords (t := 2870) rfl rfl) (by evm_ov)
  exact RD.normalizeCounters r13 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem attesterRuntime_block_2843_taken_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x3 + x0).toNat 32)) (UInt256.ofNat 18446744073709551615))) ≠ (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2843) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.EAS.Attester.Immutables.immutableLayout.runtime Benchmarks.EAS.Attester.attesterBytecode immWords) ee g s0 (UInt256.ofNat 2870) (attesterRuntime_block_2843_taken_stack (ee := ee) (x0 := x0) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (attesterRuntime_block_2843_taken hstack hcond h)
  exact ⟨_, k', C', h'⟩

end attesterRuntimeBlocks
