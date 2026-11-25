import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final memory for bytecode block summary `midnight_block_1469_taken`. -/
def midnight_block_1469_taken_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1469. -/
theorem midnight_block_1469_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 144)) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1275) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1275) (x0 :: x1 :: R) (midnight_block_1469_taken_memory (mem := mem) (x1 := x1)) (M (M (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r17 := r16.shr (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 1275) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1275)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1469_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 144)) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1275) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1275) (x0 :: x1 :: R) (midnight_block_1469_taken_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_1469_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_1469_fallthrough`. -/
def midnight_block_1469_fallthrough_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1469. -/
theorem midnight_block_1469_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 144)) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1502) (x0 :: x1 :: R) (midnight_block_1469_fallthrough_memory (mem := mem) (x1 := x1)) (M (M (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r17 := r16.shr (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.iszero (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 1275) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1502)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1469_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 144)) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1469) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1502) (x0 :: x1 :: R) (midnight_block_1469_fallthrough_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_1469_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1502_taken`. -/
def midnight_block_1502_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero x0)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1502. -/
theorem midnight_block_1502_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1631) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1502) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1631) (midnight_block_1502_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1631) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1631)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1502_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1631) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1502) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1631) (midnight_block_1502_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1502_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1502_fallthrough`. -/
def midnight_block_1502_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.isZero x0)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1502. -/
theorem midnight_block_1502_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1502) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (midnight_block_1502_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((25))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1631) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1510)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1502_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1502) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (midnight_block_1502_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1502_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1510_taken`. -/
def midnight_block_1510_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1510. -/
theorem midnight_block_1510_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1610) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1610) (midnight_block_1510_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1610) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1610)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1510_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1610) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1610) (midnight_block_1510_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1510_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1510_fallthrough`. -/
def midnight_block_1510_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1510. -/
theorem midnight_block_1510_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1516) (midnight_block_1510_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1610) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1516)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1510_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1516) (midnight_block_1510_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1510_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1516. -/
theorem midnight_block_1516 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1516) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.Midnight.midnightBytecode g s0 (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144)) (UInt256.shiftLeft x0 (UInt256.ofNat 144))) (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 2) + (keccakWord (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32))) (⟨0⟩ : UInt256)))))) ((x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32).readWithPadding (memLoad (UInt256.ofNat 800) (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32)).toNat (memLoad (UInt256.ofNat 800) (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x1.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32)).toNat) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.not (by native_decide) (by evm_ov)
  have r27 := r26.and (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r29 := r28.dup6 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.shl (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.and (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r38⟩ := RD.sstore r37 hperm (by native_decide) (by evm_ov)
  have r39 := RD.genMload r38 (by native_decide) (by evm_ov)
  have r40 := r39.swap2 (by native_decide) (by evm_ov)
  have r41 := r40.dup3 (by native_decide) (by evm_ov)
  have r42 := RD.genMstore r41 (by native_decide) (by evm_ov)
  have r43 := r42.pushConst (UInt256.ofNat 21646346564972509318272176935754915161896178560105693199319359334148154743065) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r44 := r43.swap2 (by native_decide) (by evm_ov)
  have r45 := RD.genLog2 r44 (by native_decide) hperm (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r47 := RD.genMload r46 (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  exact RD.genRet r48 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1610. -/
theorem midnight_block_1610 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1610) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 20463789) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  exact RD.genRev r10 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `midnight_block_1631`. -/
def midnight_block_1631_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 144)) (UInt256.ofNat 255)) :: x1 :: (UInt256.ofNat 1669) :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `midnight_block_1631`. -/
def midnight_block_1631_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1631. -/
theorem midnight_block_1631 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20085) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1631) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20085) (midnight_block_1631_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (R := R)) (midnight_block_1631_memory (mem := mem) (x2 := x2)) (M (M (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 1669) (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r21 := r20.shr (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 20085) (by native_decide) (by evm_ov)
  have r24 := r23.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20085)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1631_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20085) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1631) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20085) (midnight_block_1631_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (R := R)) (midnight_block_1631_memory (mem := mem) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := midnight_block_1631 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1669`. -/
def midnight_block_1669_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1669. -/
theorem midnight_block_1669 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1510) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (midnight_block_1669_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1510) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1510)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1669_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1510) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1510) (midnight_block_1669_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1669 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1675. -/
theorem midnight_block_1675 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1675) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Midnight.midnightBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 714713399) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  exact RD.genRev r10 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1696. -/
theorem midnight_block_1696_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1696) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1696_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1696) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1696_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1696. -/
theorem midnight_block_1696_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1696) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1702) R mem aw rdata σ (k + 4) (C + ((16))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.callvalue (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1702)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1696_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1696) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1702) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1696_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1702. -/
theorem midnight_block_1702_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1702) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1702_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1702) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1702_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1702. -/
theorem midnight_block_1702_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1702) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1714) R mem aw rdata σ (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.slt (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1714)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1702_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.slt ((UInt256.lnot (UInt256.ofNat 3)) + (UInt256.ofNat ee.calldata.size)) (UInt256.ofNat 96)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1702) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1714) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1702_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1714_taken`. -/
def midnight_block_1714_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1714. -/
theorem midnight_block_1714_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1714) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) (midnight_block_1714_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 18) (C + ((61))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r12 := r11.calldataload (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.dup3 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 712)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1714_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 712) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1714) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 712) (midnight_block_1714_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1714_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1714_fallthrough`. -/
def midnight_block_1714_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1714. -/
theorem midnight_block_1714_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1714) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1739) (midnight_block_1714_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 18) (C + ((61))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r12 := r11.calldataload (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.dup3 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 712) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1739)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1714_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.sub (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1714) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1739) (midnight_block_1714_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1714_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1739`. -/
def midnight_block_1739_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1754) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1739. -/
theorem midnight_block_1739 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18276) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1739) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18276) (midnight_block_1739_stack (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1754) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 18276) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18276)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1739_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18276) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1739) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18276) (midnight_block_1739_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1739 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1754_taken`. -/
def midnight_block_1754_taken_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.land x0 x1) (UInt256.ofNat ee.source.val)) :: x3 :: x2 :: (UInt256.land x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1754. -/
theorem midnight_block_1754_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land x0 x1) (UInt256.ofNat ee.source.val))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1963) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1754) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1963) (midnight_block_1754_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.caller (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1963) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1963)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1754_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land x0 x1) (UInt256.ofNat ee.source.val))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 1963) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1754) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1963) (midnight_block_1754_taken_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1754_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_1754_fallthrough`. -/
def midnight_block_1754_fallthrough_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.eq (UInt256.land x0 x1) (UInt256.ofNat ee.source.val)) :: x3 :: x2 :: (UInt256.land x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1754. -/
theorem midnight_block_1754_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land x0 x1) (UInt256.ofNat ee.source.val))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1754) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1766) (midnight_block_1754_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.caller (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1963) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1766)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_1754_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.land x0 x1) (UInt256.ofNat ee.source.val))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1754) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 1766) (midnight_block_1754_fallthrough_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_1754_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
