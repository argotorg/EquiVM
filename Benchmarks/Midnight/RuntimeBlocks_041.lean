import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_10457_taken`. -/
def midnight_block_10457_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) :: R)

/-- Final memory for bytecode block summary `midnight_block_10457_taken`. -/
def midnight_block_10457_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10457. -/
theorem midnight_block_10457_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) (UInt256.lt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 15087) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10457) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15087) (midnight_block_10457_taken_stack (mem := mem) (R := R)) (midnight_block_10457_taken_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((73) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.lt (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.shl (by native_decide) (by evm_ov)
  have r17 := r16.sub (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := r18.gt (by native_decide) (by evm_ov)
  have r20 := r19.or (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 15087) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15087)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10457_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) (UInt256.lt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 15087) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10457) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15087) (midnight_block_10457_taken_stack (mem := mem) (R := R)) (midnight_block_10457_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10457_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10457_fallthrough`. -/
def midnight_block_10457_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) :: R)

/-- Final memory for bytecode block summary `midnight_block_10457_fallthrough`. -/
def midnight_block_10457_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10457. -/
theorem midnight_block_10457_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) (UInt256.lt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10457) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10493) (midnight_block_10457_fallthrough_stack (mem := mem) (R := R)) (midnight_block_10457_fallthrough_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((73) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.lt (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.shl (by native_decide) (by evm_ov)
  have r17 := r16.sub (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := r18.gt (by native_decide) (by evm_ov)
  have r20 := r19.or (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 15087) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10493)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10457_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.gt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) (UInt256.lt ((memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)) + (UInt256.ofNat 480)) (memLoad (UInt256.ofNat 384) ((memLoad (UInt256.ofNat 64) mem).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10457) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10493) (midnight_block_10457_fallthrough_stack (mem := mem) (R := R)) (midnight_block_10457_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10457_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10493_taken`. -/
def midnight_block_10493_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + x1).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10493_taken`. -/
def midnight_block_10493_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10493. -/
theorem midnight_block_10493_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + x1).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10493) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_10493_taken_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10493_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((52) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.calldataload (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.gt (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6350)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10493_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + x1).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10493) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_10493_taken_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10493_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10493_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10493_fallthrough`. -/
def midnight_block_10493_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + x1).toNat 32)) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10493_fallthrough`. -/
def midnight_block_10493_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10493. -/
theorem midnight_block_10493_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + x1).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10493) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10515) (midnight_block_10493_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10493_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((52) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.calldataload (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.gt (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10515)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10493_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + x1).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10493) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10515) (midnight_block_10493_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10493_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10493_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10515`. -/
def midnight_block_10515_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((x1 + x0) + (UInt256.ofNat 4)) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 10530) :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10515. -/
theorem midnight_block_10515 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18574) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10515) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18574) (midnight_block_10515_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 10530) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.calldatasize (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 18574) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18574)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10515_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18574) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10515) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18574) (midnight_block_10515_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10515 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10530`. -/
def midnight_block_10530_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 36)) :: (UInt256.ofNat 10547) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10530`. -/
def midnight_block_10530_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (memLoad (UInt256.ofNat 384) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10530. -/
theorem midnight_block_10530 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19003) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10530) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19003) (midnight_block_10530_stack (x1 := x1) (R := R)) (midnight_block_10530_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((33) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 384) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 10547) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 19003) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19003)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10530_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19003) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10530) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19003) (midnight_block_10530_stack (x1 := x1) (R := R)) (midnight_block_10530_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10530 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10547`. -/
def midnight_block_10547_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 68)) :: (UInt256.ofNat 10567) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10547`. -/
def midnight_block_10547_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10547. -/
theorem midnight_block_10547 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10547_stack (x1 := x1) (R := R)) (midnight_block_10547_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10567) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 18342) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18342)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10547_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10547_stack (x1 := x1) (R := R)) (midnight_block_10547_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10547 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10567`. -/
def midnight_block_10567_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 228)) :: (UInt256.ofNat 10639) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10567`. -/
def midnight_block_10567_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 196)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 164)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 164)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)).toNat 32)) + (UInt256.ofNat 192)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10567. -/
theorem midnight_block_10567 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10567) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10567_stack (x1 := x1) (R := R)) (midnight_block_10567_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 164)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)).toNat 32)) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 48) (C + ((147) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 164)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 132)).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 384) ((uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 100)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 64)).toNat 32)) + (UInt256.ofNat 96)).toNat 32)) + (UInt256.ofNat 128)).toNat 32)) + (UInt256.ofNat 160)).toNat 32)) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.calldataload (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := r18.calldataload (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r22 := RD.genMload r21 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r26 := r25.dup2 (by native_decide) (by evm_ov)
  have r27 := r26.add (by native_decide) (by evm_ov)
  have r28 := r27.calldataload (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r31 := RD.genMload r30 (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := RD.genMstore r32 (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := r36.calldataload (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r39 := r38.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := RD.genMstore r41 (by native_decide) (by evm_ov)
  have r43 := r42.push2 (UInt256.ofNat 10639) (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r45 := r44.dup3 (by native_decide) (by evm_ov)
  have r46 := r45.add (by native_decide) (by evm_ov)
  have r47 := r46.push2 (UInt256.ofNat 18342) (by native_decide) (by evm_ov)
  have r48 := r47.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18342)) r48 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10567_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10567) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10567_stack (x1 := x1) (R := R)) (midnight_block_10567_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10567 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10639_taken`. -/
def midnight_block_10639_taken_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 260)).toNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_10639_taken`. -/
def midnight_block_10639_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10639. -/
theorem midnight_block_10639_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 260)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_10639_taken_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10639_taken_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((65) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 260) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.calldataload (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.gt (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6350)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10639_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 260)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_10639_taken_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10639_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10639_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10639_fallthrough`. -/
def midnight_block_10639_fallthrough_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 260)).toNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_10639_fallthrough`. -/
def midnight_block_10639_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10639. -/
theorem midnight_block_10639_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 260)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10669) (midnight_block_10639_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10639_fallthrough_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((65) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 260) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.calldataload (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.gt (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10669)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10639_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (x1 + (UInt256.ofNat 260)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10639) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10669) (midnight_block_10639_fallthrough_stack (ee := ee) (x1 := x1) (R := R)) (midnight_block_10639_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10639_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10669`. -/
def midnight_block_10669_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((x0 + x1) + (UInt256.ofNat 4)) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 10687) :: x0 :: (UInt256.ofNat 452) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10669. -/
theorem midnight_block_10669 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19043) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10669) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19043) (midnight_block_10669_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 11) (C + ((37))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 10687) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 452) (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.dup5 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 19043) (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19043)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10669_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19043) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10669) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19043) (midnight_block_10669_stack (ee := ee) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10669 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10687`. -/
def midnight_block_10687_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 292)) :: (UInt256.ofNat 10709) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10687`. -/
def midnight_block_10687_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 256)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10687. -/
theorem midnight_block_10687 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10687) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10687_stack (x1 := x1) (R := R)) (midnight_block_10687_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10709) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 292) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 18342) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18342)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10687_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10687) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10687_stack (x1 := x1) (R := R)) (midnight_block_10687_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10687 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10709`. -/
def midnight_block_10709_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 324)) :: (UInt256.ofNat 10731) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10709`. -/
def midnight_block_10709_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 288)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10709. -/
theorem midnight_block_10709 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10709) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10709_stack (x1 := x1) (R := R)) (midnight_block_10709_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10731) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 324) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 18342) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18342)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10709_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18342) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10709) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18342) (midnight_block_10709_stack (x1 := x1) (R := R)) (midnight_block_10709_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10709 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10731`. -/
def midnight_block_10731_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 356)) :: (UInt256.ofNat 10753) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10731`. -/
def midnight_block_10731_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10731. -/
theorem midnight_block_10731 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19003) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10731) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19003) (midnight_block_10731_stack (x1 := x1) (R := R)) (midnight_block_10731_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10753) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 356) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 19003) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19003)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10731_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19003) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10731) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19003) (midnight_block_10731_stack (x1 := x1) (R := R)) (midnight_block_10731_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10731 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10753`. -/
def midnight_block_10753_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 388)) :: (UInt256.ofNat 10775) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10753`. -/
def midnight_block_10753_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 352)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10753. -/
theorem midnight_block_10753 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19113) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10753) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (midnight_block_10753_stack (x1 := x1) (R := R)) (midnight_block_10753_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10775) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 388) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 19113) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19113)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10753_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19113) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10753) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (midnight_block_10753_stack (x1 := x1) (R := R)) (midnight_block_10753_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10753 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10775`. -/
def midnight_block_10775_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x1 + (UInt256.ofNat 420)) :: (UInt256.ofNat 10795) :: x1 :: R)

/-- Final memory for bytecode block summary `midnight_block_10775`. -/
def midnight_block_10775_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 384)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10775. -/
theorem midnight_block_10775 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19113) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10775) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (midnight_block_10775_stack (x1 := x1) (R := R)) (midnight_block_10775_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10795) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 420) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 19113) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19113)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10775_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19113) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10775) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19113) (midnight_block_10775_stack (x1 := x1) (R := R)) (midnight_block_10775_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10775 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10795_taken`. -/
def midnight_block_10795_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_10795_taken`. -/
def midnight_block_10795_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x1 + x2).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32)) + (UInt256.ofNat 448)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10795. -/
theorem midnight_block_10795_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10795) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_10795_taken_stack (ee := ee) (R := R)) (midnight_block_10795_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32)) + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((77) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32)) + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.calldataload (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r15 := r14.calldataload (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.gt (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r24 := r23.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6350)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10795_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10795) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_10795_taken_stack (ee := ee) (R := R)) (midnight_block_10795_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10795_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10795_fallthrough`. -/
def midnight_block_10795_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_10795_fallthrough`. -/
def midnight_block_10795_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (x1 + x2).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32)) + (UInt256.ofNat 448)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 10795. -/
theorem midnight_block_10795_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10795) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10833) (midnight_block_10795_fallthrough_stack (ee := ee) (R := R)) (midnight_block_10795_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32)) + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((77) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 384) (x0.toByteArray.write 0 mem ((memLoad (UInt256.ofNat 384) mem) + (UInt256.ofNat 416)).toNat 32)) + (UInt256.ofNat 448)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.calldataload (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r15 := r14.calldataload (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.gt (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r24 := r23.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10833)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10795_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10795) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10833) (midnight_block_10795_fallthrough_stack (ee := ee) (R := R)) (midnight_block_10795_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10795_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10833`. -/
def midnight_block_10833_stack {ee : ExecutionEnv} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + x0) :: (UInt256.ofNat ee.calldata.size) :: (UInt256.ofNat 10846) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10833. -/
theorem midnight_block_10833 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19043) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10833) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19043) (midnight_block_10833_stack (ee := ee) (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 10846) (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.calldatasize (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 19043) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19043)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10833_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19043) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10833) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19043) (midnight_block_10833_stack (ee := ee) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10833 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_10846`. -/
def midnight_block_10846_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 10854) :: R)

/-- Automatically generated RD summary for bytecode block at pc 10846. -/
theorem midnight_block_10846 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18298) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10846) R mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18298) (midnight_block_10846_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10854) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 18298) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18298)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_10846_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 18298) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 10846) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 18298) (midnight_block_10846_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_10846 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
