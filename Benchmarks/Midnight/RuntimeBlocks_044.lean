import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_11391_taken`. -/
def midnight_block_11391_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_11391_taken`. -/
def midnight_block_11391_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (⟨0⟩ : UInt256) mem).toByteArray.write 0 (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11391. -/
theorem midnight_block_11391_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14781) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14781) (midnight_block_11391_taken_stack (R := R)) (midnight_block_11391_taken_memory (mem := mem)) (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 24513) (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 14781) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14781)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11391_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14781) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14781) (midnight_block_11391_taken_stack (R := R)) (midnight_block_11391_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11391_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11391_fallthrough`. -/
def midnight_block_11391_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_11391_fallthrough`. -/
def midnight_block_11391_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (⟨0⟩ : UInt256) mem).toByteArray.write 0 (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11391. -/
theorem midnight_block_11391_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11413) (midnight_block_11391_fallthrough_stack (R := R)) (midnight_block_11391_fallthrough_memory (mem := mem)) (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 24513) (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 14781) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11413)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11391_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.sub x0 (memLoad (⟨0⟩ : UInt256) (Benchmarks.Midnight.midnightBytecode.write (UInt256.ofNat 24513).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11391) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11413) (midnight_block_11391_fallthrough_stack (R := R)) (midnight_block_11391_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11391_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11413_taken`. -/
def midnight_block_11413_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11413. -/
theorem midnight_block_11413_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) mem) (UInt256.ofNat 6744)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14766) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11413) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14766) (midnight_block_11413_taken_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((37) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 6744) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 14766) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14766)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11413_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) mem) (UInt256.ofNat 6744)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14766) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11413) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14766) (midnight_block_11413_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11413_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11413_fallthrough`. -/
def midnight_block_11413_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11413. -/
theorem midnight_block_11413_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) mem) (UInt256.ofNat 6744)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11413) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11430) (midnight_block_11413_fallthrough_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((37) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 6744) (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.gt (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 14766) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11430)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11413_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 160)) mem) (UInt256.ofNat 6744)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11413) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11430) (midnight_block_11413_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11413_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11430`. -/
def midnight_block_11430_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (UInt256.ofNat 4987541511039073) (UInt256.sub (UInt256.ofNat 3372) x0)) :: (UInt256.ofNat 11467) :: (UInt256.ofNat 11514) :: (UInt256.ofNat 49999999999) :: (UInt256.ofNat 100000000000) :: (UInt256.ofNat 100000000000) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11430. -/
theorem midnight_block_11430 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 24388) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11430) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 24388) (midnight_block_11430_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((43))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 100000000000) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 49999999999) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 11514) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11467) (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.swap5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 3372) (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 4987541511039073) (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.mul (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 24388) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 24388)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11430_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 24388) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11430) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 24388) (midnight_block_11430_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11430 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11467`. -/
def midnight_block_11467_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1000000000000000000000000000000000000) + (UInt256.shiftRight (x0 + (UInt256.ofNat 999999999999999999)) (UInt256.ofNat 1))) :: ((UInt256.ofNat 1000000000000000000) + x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11467. -/
theorem midnight_block_11467 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19391) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11467) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19391) (midnight_block_11467_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((42))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 999999999999999999) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.shr (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 1000000000000000000000000000000000000) (width := 15) (op := .PUSH15) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 19391) (by native_decide) (by evm_ov)
  have r13 := r12.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19391)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11467_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19391) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11467) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19391) (midnight_block_11467_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11467 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11514`. -/
def midnight_block_11514_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 512) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) :: (UInt256.mul (UInt256.lt (UInt256.ofNat ee.header.timestamp) (memLoad ((memLoad (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) + (UInt256.ofNat 128)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32))) (UInt256.sub (memLoad ((memLoad (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) + (UInt256.ofNat 128)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) (UInt256.ofNat ee.header.timestamp))) :: (UInt256.ofNat 11556) :: (UInt256.ofNat 11591) :: (UInt256.mul (UInt256.div (x0 + x1) x2) x3) :: x5 :: x4 :: (UInt256.mul (UInt256.lt (UInt256.ofNat ee.header.timestamp) (memLoad ((memLoad (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) + (UInt256.ofNat 128)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32))) (UInt256.sub (memLoad ((memLoad (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) + (UInt256.ofNat 128)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) (UInt256.ofNat ee.header.timestamp))) :: R)

/-- Final memory for bytecode block summary `midnight_block_11514`. -/
def midnight_block_11514_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11514. -/
theorem midnight_block_11514 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21835) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11514) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21835) (midnight_block_11514_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_11514_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)) rdata σ (k + 29) (C + ((93) + (memExpansionCost aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) (⟨32⟩ : UInt256)) ((memLoad (memLoad (UInt256.ofNat 384) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 800).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 512) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.div (by native_decide) (by evm_ov)
  have r7 := r6.mul (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have r15 := r14.timestamp (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.sub (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.timestamp (by native_decide) (by evm_ov)
  have r20 := r19.lt (by native_decide) (by evm_ov)
  have r21 := r20.mul (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 11591) (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 11556) (by native_decide) (by evm_ov)
  have r25 := r24.dup6 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 21835) (by native_decide) (by evm_ov)
  have r29 := r28.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 21835)) r29 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11514_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 21835) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11514) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 21835) (midnight_block_11514_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_11514_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11514 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11556_taken`. -/
def midnight_block_11556_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11556. -/
theorem midnight_block_11556_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14759) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11556) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14759) (midnight_block_11556_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((46) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := r11.eq (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 14759) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14759)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11556_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14759) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11556) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14759) (midnight_block_11556_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11556_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11556_fallthrough`. -/
def midnight_block_11556_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11556. -/
theorem midnight_block_11556_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11556) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11575) (midnight_block_11556_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((46) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := r11.eq (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 14759) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11575)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11556_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.isZero (UInt256.isZero (memLoad ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11556) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11575) (midnight_block_11556_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11556_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11575`. -/
def midnight_block_11575_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: (UInt256.ofNat 11583) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11575. -/
theorem midnight_block_11575 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11575) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_11575_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 11583) (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 19447) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19447)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11575_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19447) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11575) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19447) (midnight_block_11575_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11575 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11583`. -/
def midnight_block_11583_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11583. -/
theorem midnight_block_11583 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11583) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11585) (midnight_block_11583_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11585)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11583_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11583) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11585) (midnight_block_11583_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11583 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11585`. -/
def midnight_block_11585_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11585. -/
theorem midnight_block_11585 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11585) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_11585_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 19536) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19536)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11585_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19536) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11585) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19536) (midnight_block_11585_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11585 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11591_taken`. -/
def midnight_block_11591_taken_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11591. -/
theorem midnight_block_11591_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14738) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11591) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14738) R (midnight_block_11591_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((40) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14738) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14738)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11591_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14738) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11591) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14738) R (midnight_block_11591_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11591_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11591_fallthrough`. -/
def midnight_block_11591_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11591. -/
theorem midnight_block_11591_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11591) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11610) R (midnight_block_11591_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((40) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14738) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11610)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11591_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11591) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11610) R (midnight_block_11591_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11591_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11610`. -/
def midnight_block_11610_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: x0 :: (UInt256.ofNat 11630) :: (UInt256.ofNat 1000000000000000000) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11610. -/
theorem midnight_block_11610 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11610) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_11610_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 11630) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r5 := r4.calldataload (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 20413) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20413)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11610_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11610) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_11610_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11610 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11630`. -/
def midnight_block_11630_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_11630`. -/
def midnight_block_11630_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.div x0 x1).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11630. -/
theorem midnight_block_11630 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11630) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11636) (midnight_block_11630_stack (R := R)) (midnight_block_11630_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((12) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.div (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11636)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11630_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11630) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11636) (midnight_block_11630_stack (R := R)) (midnight_block_11630_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11630 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11636_taken`. -/
def midnight_block_11636_taken_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11636. -/
theorem midnight_block_11636_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14717) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11636) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14717) R (midnight_block_11636_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((40) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14717) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14717)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11636_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 14717) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11636) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 14717) R (midnight_block_11636_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11636_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `midnight_block_11636_fallthrough`. -/
def midnight_block_11636_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11636. -/
theorem midnight_block_11636_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11636) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11655) R (midnight_block_11636_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((40) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 416) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 14717) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11655)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11636_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 384) mem)) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11636) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11655) R (midnight_block_11636_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11636_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11655`. -/
def midnight_block_11655_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: x0 :: (UInt256.ofNat 11675) :: (UInt256.ofNat 1000000000000000000) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11655. -/
theorem midnight_block_11655 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11655) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_11655_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 11675) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r5 := r4.calldataload (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 20413) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20413)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11655_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11655) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_11655_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11655 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_11675`. -/
def midnight_block_11675_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `midnight_block_11675`. -/
def midnight_block_11675_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.div x0 x1).toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11675. -/
theorem midnight_block_11675 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11675) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11681) (midnight_block_11675_stack (R := R)) (midnight_block_11675_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((12) + (memExpansionCost aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.div (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11681)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_11675_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11675) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 11681) (midnight_block_11675_stack (R := R)) (midnight_block_11675_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_11675 hstack h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
