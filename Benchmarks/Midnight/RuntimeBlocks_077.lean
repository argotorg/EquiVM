import Reasoning.Reach
import Benchmarks.Midnight.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace midnightBlocks

/-- Final stack for bytecode block summary `midnight_block_20077`. -/
def midnight_block_20077_stack {rdata : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat rdata.size) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20077. -/
theorem midnight_block_20077 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20045) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20077) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20045) (midnight_block_20077_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 20045) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20045)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20077_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20045) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20077) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20045) (midnight_block_20077_stack (rdata := rdata) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20077 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20085. -/
theorem midnight_block_20085_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19401) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20085) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19401) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19401) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19401)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20085_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19401) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20085) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19401) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20085_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 20085. -/
theorem midnight_block_20085_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20085) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20092) (x0 :: x1 :: R) mem aw rdata σ (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 19401) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20092)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20085_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20085) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20092) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20085_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20092`. -/
def midnight_block_20092_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mod x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20092. -/
theorem midnight_block_20092 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20092) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x2 (midnight_block_20092_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have r1 := r0.mod (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20092_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20092) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x2 (midnight_block_20092_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20092 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20095`. -/
def midnight_block_20095_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((UInt256.land (UInt256.lnot (UInt256.ofNat 31)) ((UInt256.ofNat 31) + (memLoad x0 mem))) + x1) + (UInt256.ofNat 32)) :: R)

/-- Final memory for bytecode block summary `midnight_block_20095`. -/
def midnight_block_20095_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32).write ((UInt256.ofNat 32) + x0).toNat ((memLoad x0 mem).toByteArray.write 0 mem x1.toNat 32) (x1 + (UInt256.ofNat 32)).toNat (memLoad x0 mem).toNat) ((UInt256.ofNat 32) + ((memLoad x0 mem) + x1)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20095. -/
theorem midnight_block_20095 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20095) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x2 (midnight_block_20095_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20095_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (Mmcopy (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) ((UInt256.ofNat 32) + x0) (memLoad x0 mem)) ((UInt256.ofNat 32) + ((memLoad x0 mem) + x1)) (⟨32⟩ : UInt256)) rdata σ (k + 33) (C + ((98) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) + (mcopyExpansionCost (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) ((UInt256.ofNat 32) + x0) (memLoad x0 mem)) + (3 + 3 * (((memLoad x0 mem).toNat + 31) / 32)) + (memExpansionCost (Mmcopy (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) ((UInt256.ofNat 32) + x0) (memLoad x0 mem)) ((UInt256.ofNat 32) + ((memLoad x0 mem) + x1)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := r11.dup5 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup5 (by native_decide) (by evm_ov)
  have r15 := r14.dup5 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := RD.genMcopy r16 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.add (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r28 := r27.not (by native_decide) (by evm_ov)
  have r29 := r28.and (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  have r33 := r32.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r33 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20095_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20095) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x2 (midnight_block_20095_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20095_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20095 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20131`. -/
def midnight_block_20131_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: (x1 + (UInt256.ofNat 480)) :: (UInt256.ofNat 20160) :: (UInt256.ofNat 20270) :: (UInt256.ofNat 448) :: (UInt256.ofNat 448) :: x1 :: x0 :: R)

/-- Final memory for bytecode block summary `midnight_block_20131`. -/
def midnight_block_20131_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 480).toByteArray.write 0 mem x1.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20131. -/
theorem midnight_block_20131 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19181) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20131) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (midnight_block_20131_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20131_memory (mem := mem) (x1 := x1)) (M (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((54) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 20270) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 20160) (by native_decide) (by evm_ov)
  have r7 := r6.dup6 (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r10 := r9.dup7 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r13 := r12.dup7 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 19181) (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19181)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20131_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19181) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20131) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19181) (midnight_block_20131_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) (midnight_block_20131_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20131 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20160`. -/
def midnight_block_20160_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: (UInt256.ofNat 224) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `midnight_block_20160`. -/
def midnight_block_20160_memory {mem : ByteArray} {x4 : UInt256} {x5 : UInt256} : ByteArray :=
  ((memLoad (x5 + (UInt256.ofNat 192)) ((memLoad (x5 + (UInt256.ofNat 160)) ((memLoad (x5 + (UInt256.ofNat 128)) ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32)).toByteArray.write 0 ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32) (x4 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((memLoad (x5 + (UInt256.ofNat 128)) ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32)).toByteArray.write 0 ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32) (x4 + (UInt256.ofNat 128)).toNat 32) (x4 + (UInt256.ofNat 160)).toNat 32)).toByteArray.write 0 ((memLoad (x5 + (UInt256.ofNat 160)) ((memLoad (x5 + (UInt256.ofNat 128)) ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32)).toByteArray.write 0 ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32) (x4 + (UInt256.ofNat 128)).toNat 32)).toByteArray.write 0 ((memLoad (x5 + (UInt256.ofNat 128)) ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32)).toByteArray.write 0 ((memLoad (x5 + (UInt256.ofNat 96)) ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32)).toByteArray.write 0 ((UInt256.land (memLoad (x5 + (UInt256.ofNat 64)) ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x5 + (UInt256.ofNat 32)) mem))).toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32) (x4 + (UInt256.ofNat 128)).toNat 32) (x4 + (UInt256.ofNat 160)).toNat 32) (x4 + (UInt256.ofNat 192)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20160. -/
theorem midnight_block_20160 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20160) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20243) (midnight_block_20160_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_20160_memory (mem := mem) (x4 := x4) (x5 := x5)) (M (M (M (M (M (M (M (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((190) + (memExpansionCost aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M aw (x5 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x5 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup7 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup7 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.dup8 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r23 := r22.dup7 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r27 := r26.dup7 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have r29 := RD.genMload r28 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r31 := r30.dup7 (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := RD.genMstore r32 (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r35 := r34.dup7 (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := RD.genMload r36 (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r39 := r38.dup7 (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := RD.genMstore r40 (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r43 := r42.dup7 (by native_decide) (by evm_ov)
  have r44 := r43.add (by native_decide) (by evm_ov)
  have r45 := RD.genMload r44 (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r47 := r46.dup7 (by native_decide) (by evm_ov)
  have r48 := r47.add (by native_decide) (by evm_ov)
  have r49 := RD.genMstore r48 (by native_decide) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r51 := r50.dup7 (by native_decide) (by evm_ov)
  have r52 := r51.add (by native_decide) (by evm_ov)
  have r53 := RD.genMload r52 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r55 := r54.dup7 (by native_decide) (by evm_ov)
  have r56 := r55.add (by native_decide) (by evm_ov)
  have r57 := RD.genMstore r56 (by native_decide) (by evm_ov)
  have r58 := r57.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r61 := r60.shl (by native_decide) (by evm_ov)
  have r62 := r61.sub (by native_decide) (by evm_ov)
  have r63 := r62.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r64 := r63.dup8 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20243)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20160_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20160) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20243) (midnight_block_20160_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (midnight_block_20160_memory (mem := mem) (x4 := x4) (x5 := x5)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20160 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20243`. -/
def midnight_block_20243_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x8 + (UInt256.ofNat 256)) ((UInt256.land (memLoad (x0 + x1) mem) x2).toByteArray.write 0 mem (x7 + (UInt256.ofNat 224)).toNat 32)) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Final memory for bytecode block summary `midnight_block_20243`. -/
def midnight_block_20243_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x7 : UInt256} : ByteArray :=
  ((UInt256.sub x3 x7).toByteArray.write 0 ((UInt256.land (memLoad (x0 + x1) mem) x2).toByteArray.write 0 mem (x7 + (UInt256.ofNat 224)).toNat 32) (x7 + (UInt256.ofNat 256)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20243. -/
theorem midnight_block_20243 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20095) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20243) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20095) (midnight_block_20243_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (midnight_block_20243_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x7 := x7)) (M (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((65) + (memExpansionCost aw (x0 + x1) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x0 + x1) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (x8 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) (x7 + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.add (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.and (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r5 := r4.dup7 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r9 := r8.dup7 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup6 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r16 := r15.dup8 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 20095) (by native_decide) (by evm_ov)
  have r20 := r19.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20095)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20243_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20095) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20243) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20095) (midnight_block_20243_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (midnight_block_20243_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x7 := x7)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20243 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20270`. -/
def midnight_block_20270_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (memLoad (x4 + (UInt256.ofNat 416)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 384)) ((UInt256.isZero (UInt256.isZero (memLoad (x4 + (UInt256.ofNat 352)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) (x3 + (UInt256.ofNat 352)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x4 + (UInt256.ofNat 352)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) (x3 + (UInt256.ofNat 352)).toNat 32) (x3 + (UInt256.ofNat 384)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) :: x4 :: x1 :: x2 :: x3 :: x0 :: R)

/-- Final memory for bytecode block summary `midnight_block_20270`. -/
def midnight_block_20270_memory {mem : ByteArray} {x3 : UInt256} {x4 : UInt256} : ByteArray :=
  ((UInt256.land (memLoad (x4 + (UInt256.ofNat 384)) ((UInt256.isZero (UInt256.isZero (memLoad (x4 + (UInt256.ofNat 352)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) (x3 + (UInt256.ofNat 352)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.isZero (UInt256.isZero (memLoad (x4 + (UInt256.ofNat 352)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 320)) ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (memLoad (x4 + (UInt256.ofNat 288)) mem) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) (x3 + (UInt256.ofNat 352)).toNat 32) (x3 + (UInt256.ofNat 384)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20270. -/
theorem midnight_block_20270 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20270) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20364) (midnight_block_20270_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (midnight_block_20270_memory (mem := mem) (x3 := x3) (x4 := x4)) (M (M (M (M (M (M (M (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((190) + (memExpansionCost aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (x4 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 352)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 384)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap4 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r14 := r13.dup6 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r20 := r19.shl (by native_decide) (by evm_ov)
  have r21 := r20.sub (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.genMload r24 (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r28 := r27.dup6 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r32 := r31.dup2 (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := RD.genMload r33 (by native_decide) (by evm_ov)
  have r35 := r34.iszero (by native_decide) (by evm_ov)
  have r36 := r35.iszero (by native_decide) (by evm_ov)
  have r37 := r36.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r38 := r37.dup6 (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := RD.genMstore r39 (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r44 := r43.shl (by native_decide) (by evm_ov)
  have r45 := r44.sub (by native_decide) (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r47 := r46.dup3 (by native_decide) (by evm_ov)
  have r48 := r47.add (by native_decide) (by evm_ov)
  have r49 := RD.genMload r48 (by native_decide) (by evm_ov)
  have r50 := r49.and (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r52 := r51.dup6 (by native_decide) (by evm_ov)
  have r53 := r52.add (by native_decide) (by evm_ov)
  have r54 := RD.genMstore r53 (by native_decide) (by evm_ov)
  have r55 := r54.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r58 := r57.shl (by native_decide) (by evm_ov)
  have r59 := r58.sub (by native_decide) (by evm_ov)
  have r60 := r59.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r61 := r60.dup3 (by native_decide) (by evm_ov)
  have r62 := r61.add (by native_decide) (by evm_ov)
  have r63 := RD.genMload r62 (by native_decide) (by evm_ov)
  have r64 := r63.and (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20364)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20270_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20270) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20364) (midnight_block_20270_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (midnight_block_20270_memory (mem := mem) (x3 := x3) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20270 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20364`. -/
def midnight_block_20364_stack {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  (x5 :: R)

/-- Final memory for bytecode block summary `midnight_block_20364`. -/
def midnight_block_20364_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} : ByteArray :=
  ((memLoad (x1 + x2) (x0.toByteArray.write 0 mem (x4 + (UInt256.ofNat 416)).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (x4 + (UInt256.ofNat 416)).toNat 32) (x4 + x3).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 20364. -/
theorem midnight_block_20364 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20364) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x6 (midnight_block_20364_stack (x5 := x5) (R := R)) (midnight_block_20364_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4)) (M (M (M aw (x4 + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (x1 + x2) (⟨32⟩ : UInt256)) (x4 + x3) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((38) + (memExpansionCost aw (x4 + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x4 + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (x1 + x2) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x4 + (UInt256.ofNat 416)) (⟨32⟩ : UInt256)) (x1 + x2) (⟨32⟩ : UInt256)) (x4 + x3) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r2 := r1.dup6 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20364_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x6 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20364) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x6 (midnight_block_20364_stack (x5 := x5) (R := R)) (midnight_block_20364_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20364 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20377_taken`. -/
def midnight_block_20377_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20377. -/
theorem midnight_block_20377_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero x0) (UInt256.eq (UInt256.ofNat 1000000000000000000) (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) x0)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20377) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_20377_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 17) (C + ((60))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.mul (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.eq (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.or (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20377_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero x0) (UInt256.eq (UInt256.ofNat 1000000000000000000) (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) x0)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20377) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_20377_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20377_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20377_fallthrough`. -/
def midnight_block_20377_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20377. -/
theorem midnight_block_20377_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero x0) (UInt256.eq (UInt256.ofNat 1000000000000000000) (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) x0)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20377) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20412) (midnight_block_20377_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 17) (C + ((60))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.mul (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.eq (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.or (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20412)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20377_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.isZero x0) (UInt256.eq (UInt256.ofNat 1000000000000000000) (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) x0)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20377) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20412) (midnight_block_20377_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20377_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20412`. -/
def midnight_block_20412_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 20412. -/
theorem midnight_block_20412 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20412) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_20412_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20412_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20412) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_20412_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20412 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20413_taken`. -/
def midnight_block_20413_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.mul x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20413. -/
theorem midnight_block_20413_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul x0 x1) x0) x1) (UInt256.isZero x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_20413_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 16) (C + ((57))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.mul (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.dup5 (by native_decide) (by evm_ov)
  have r11 := r10.div (by native_decide) (by evm_ov)
  have r12 := r11.eq (by native_decide) (by evm_ov)
  have r13 := r12.or (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7302)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20413_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul x0 x1) x0) x1) (UInt256.isZero x0))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7302) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7302) (midnight_block_20413_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20413_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20413_fallthrough`. -/
def midnight_block_20413_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (UInt256.mul x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20413. -/
theorem midnight_block_20413_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul x0 x1) x0) x1) (UInt256.isZero x0))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20431) (midnight_block_20413_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 16) (C + ((57))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.mul (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.dup5 (by native_decide) (by evm_ov)
  have r11 := r10.div (by native_decide) (by evm_ov)
  have r12 := r11.eq (by native_decide) (by evm_ov)
  have r13 := r12.or (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20431)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20413_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul x0 x1) x0) x1) (UInt256.isZero x0))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20431) (midnight_block_20413_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20413_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20431`. -/
def midnight_block_20431_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 20431. -/
theorem midnight_block_20431 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20431) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_20431_stack (R := R)) mem aw rdata σ (k + 1) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20431_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x0 = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20431) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x0 (midnight_block_20431_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20431 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20432_taken`. -/
def midnight_block_20432_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20432. -/
theorem midnight_block_20432_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20432) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_20432_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6350)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20432_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20432) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_20432_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20432_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20432_fallthrough`. -/
def midnight_block_20432_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 20432. -/
theorem midnight_block_20432_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20432) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20444) (midnight_block_20432_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20444)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20432_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20432) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20444) (midnight_block_20432_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20432_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20444_taken`. -/
def midnight_block_20444_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20444. -/
theorem midnight_block_20444_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (memLoad x0 mem) (UInt256.isZero (UInt256.isZero (memLoad x0 mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20444) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_20444_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((31) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.genMload r0 (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6350)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20444_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (memLoad x0 mem) (UInt256.isZero (UInt256.isZero (memLoad x0 mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6350) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20444) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6350) (midnight_block_20444_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20444_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `midnight_block_20444_fallthrough`. -/
def midnight_block_20444_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x0 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 20444. -/
theorem midnight_block_20444_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (memLoad x0 mem) (UInt256.isZero (UInt256.isZero (memLoad x0 mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20444) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20454) (midnight_block_20444_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((31) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.genMload r0 (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 6350) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20454)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem midnight_block_20444_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub (memLoad x0 mem) (UInt256.isZero (UInt256.isZero (memLoad x0 mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20444) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20454) (midnight_block_20444_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (midnight_block_20444_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end midnightBlocks
