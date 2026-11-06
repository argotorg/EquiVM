import Reasoning.Reach
import Benchmarks.Midnight.TickLibWrapper.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace tickLibWrapperBlocks

/-- Final stack for bytecode block summary `tickLibWrapper_block_600`. -/
def tickLibWrapper_block_600_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (⟨0⟩ : UInt256) x0) :: (UInt256.ofNat 610) :: R)

/-- Automatically generated RD summary for bytecode block at pc 600. -/
theorem tickLibWrapper_block_600 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 591) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 600) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (tickLibWrapper_block_600_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 610) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 591) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 591)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_600_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 591) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 600) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 591) (tickLibWrapper_block_600_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_600 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 610. -/
theorem tickLibWrapper_block_610_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 456) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 610) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 456) (x0 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 456) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 456)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_610_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains (UInt256.ofNat 456) = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 610) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 456) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_610_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 610. -/
theorem tickLibWrapper_block_610_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 610) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 617) (x0 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 456) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 617)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_610_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 610) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 617) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_610_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_617`. -/
def tickLibWrapper_block_617_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div (UInt256.ofNat 1000000000000000000000000000000000000) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 617. -/
theorem tickLibWrapper_block_617 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 617) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x1 (tickLibWrapper_block_617_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 1000000000000000000000000000000000000) (width := 15) (op := .PUSH15) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.div (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_617_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 617) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x1 (tickLibWrapper_block_617_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_617 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapper_block_636`. -/
def tickLibWrapper_block_636_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft ((((UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309))) + (UInt256.sdiv (UInt256.mul (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309))) (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309)))) (UInt256.ofNat 2000000000000000000))) + (UInt256.sdiv (UInt256.mul (UInt256.sdiv (UInt256.mul (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309))) (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309)))) (UInt256.ofNat 2000000000000000000)) (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309)))) (UInt256.ofNat 3000000000000000000))) + (UInt256.ofNat 1000000000000000000)) (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 636. -/
theorem tickLibWrapper_block_636 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 636) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x1 (tickLibWrapper_block_636_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 31) (C + ((108))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 693147180559945309) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 322611214989459870) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.sdiv (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 693147180559945309) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.dup4 (by native_decide) (by evm_ov)
  have r11 := r10.mul (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 2000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.dup1 (by native_decide) (by evm_ov)
  have r17 := r16.mul (by native_decide) (by evm_ov)
  have r18 := r17.sdiv (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 3000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.mul (by native_decide) (by evm_ov)
  have r23 := r22.sdiv (by native_decide) (by evm_ov)
  have r24 := r23.swap2 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := r26.add (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r31 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapper_block_636_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 636) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 x1 (tickLibWrapper_block_636_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapper_block_636 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 715. -/
theorem tickLibWrapper_block_715 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode ee g s0 (UInt256.ofNat 715) R mem aw rdata σ k C)
    : RDinvalid Benchmarks.Midnight.TickLibWrapper.tickLibWrapperBytecode g s0 := by
  let r0 := h
  exact RD.invalid r0 (by native_decide)

end tickLibWrapperBlocks
