import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Midnight.TickLibWrapper.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace tickLibWrapperCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode

/-- Final stack for bytecode block summary `tickLibWrapperCreation_block_549`. -/
def tickLibWrapperCreation_block_549_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1000000000000000000000000000000000000) + (UInt256.shiftRight (x0 + (UInt256.ofNat 999999999999999999)) (UInt256.ofNat 1))) :: ((UInt256.ofNat 1000000000000000000) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 549. -/
theorem tickLibWrapperCreation_block_549 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 446) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 549) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 446) (tickLibWrapperCreation_block_549_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((42))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 999999999999999999) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 1000000000000000000000000000000000000) (width := 15) (op := .PUSH15) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 446) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 446) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 446)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_549_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 446) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 549) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 446) (tickLibWrapperCreation_block_549_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_549 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapperCreation_block_596`. -/
def tickLibWrapperCreation_block_596_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.div (x0 + x1) x2) x3) :: R)

/-- Automatically generated RD summary for bytecode block at pc 596. -/
theorem tickLibWrapperCreation_block_596 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 596) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 x4 (tickLibWrapperCreation_block_596_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x4 hvalid) (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_596_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains x4 = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 596) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 x4 (tickLibWrapperCreation_block_596_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_596 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 602. -/
theorem tickLibWrapperCreation_block_602 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 602) R mem aw rdata σ k C)
    : RDrev (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3353426433) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 617. -/
theorem tickLibWrapperCreation_block_617_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 636) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 617) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 636) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 636) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 636)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_617_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 636) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 617) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_617_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 617. -/
theorem tickLibWrapperCreation_block_617_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 617) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 626) (x0 :: R) mem aw rdata σ (k + 7) (C + ((25))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.slt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 636) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 626)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_617_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt x0 (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 617) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 626) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_617_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapperCreation_block_626`. -/
def tickLibWrapperCreation_block_626_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (⟨0⟩ : UInt256) x0) :: (UInt256.ofNat 610) :: R)

/-- Automatically generated RD summary for bytecode block at pc 626. -/
theorem tickLibWrapperCreation_block_626 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 591) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 626) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 591) (tickLibWrapperCreation_block_626_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 610) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 591) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 591) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 591)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_626_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 591) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 626) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 591) (tickLibWrapperCreation_block_626_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_626 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 636. -/
theorem tickLibWrapperCreation_block_636_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 456) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 456) (x0 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 456) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 456) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 456)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_636_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains (UInt256.ofNat 456) = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 456) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_636_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 636. -/
theorem tickLibWrapperCreation_block_636_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 643) (x0 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 456) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 643)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_636_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 636) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 643) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_636_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapperCreation_block_643`. -/
def tickLibWrapperCreation_block_643_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.div (UInt256.ofNat 1000000000000000000000000000000000000) x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 643. -/
theorem tickLibWrapperCreation_block_643 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 643) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 x1 (tickLibWrapperCreation_block_643_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.pushConst (UInt256.ofNat 1000000000000000000000000000000000000) (width := 15) (op := .PUSH15) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.div (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_643_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 643) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 x1 (tickLibWrapperCreation_block_643_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_643 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `tickLibWrapperCreation_block_662`. -/
def tickLibWrapperCreation_block_662_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft ((((UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309))) + (UInt256.sdiv (UInt256.mul (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309))) (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309)))) (UInt256.ofNat 2000000000000000000))) + (UInt256.sdiv (UInt256.mul (UInt256.sdiv (UInt256.mul (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309))) (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309)))) (UInt256.ofNat 2000000000000000000)) (UInt256.sub x0 (UInt256.mul (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309)) (UInt256.ofNat 693147180559945309)))) (UInt256.ofNat 3000000000000000000))) + (UInt256.ofNat 1000000000000000000)) (UInt256.sdiv (x0 + (UInt256.ofNat 322611214989459870)) (UInt256.ofNat 693147180559945309))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 662. -/
theorem tickLibWrapperCreation_block_662 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 x1 (tickLibWrapperCreation_block_662_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 31) (C + ((108))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 693147180559945309) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 322611214989459870) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.sdiv (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 693147180559945309) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 2000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.sdiv (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 3000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.mul (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.sdiv (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x1 hvalid) (by evm_ov)
  exact RD.normalizeCounters r31 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem tickLibWrapperCreation_block_662_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode 0).contains x1 = true)
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 662) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 x1 (tickLibWrapperCreation_block_662_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (tickLibWrapperCreation_block_662 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 741. -/
theorem tickLibWrapperCreation_block_741 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 741) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Midnight.TickLibWrapper.tickLibWrapperCreationBytecode.size = 754 := by native_decide
  exact RD.invalid r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide))

end tickLibWrapperCreationBlocks
