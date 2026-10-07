import Reasoning.Reach
import Benchmarks.Safe.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace safeRuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_3629_taken`. -/
def safeRuntime_block_3629_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3629. -/
theorem safeRuntime_block_3629_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3758) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3629) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3758) (safeRuntime_block_3629_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 3758) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3758)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3629_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3758) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3629) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3758) (safeRuntime_block_3629_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3629_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3629_fallthrough`. -/
def safeRuntime_block_3629_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3629. -/
theorem safeRuntime_block_3629_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3629) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3647) (safeRuntime_block_3629_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 13) (C + ((43))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 3758) (by native_decide) (by evm_ov)
  have r13 := r12.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3647)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3629_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3629) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3647) (safeRuntime_block_3629_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3629_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3647`. -/
def safeRuntime_block_3647_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat ee.source.val) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: (UInt256.ofNat 3712) :: (UInt256.ofNat 1978710866) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_3647`. -/
def safeRuntime_block_3647_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1978710866)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3647. -/
theorem safeRuntime_block_3647 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 31 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11256) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3647) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11256) (safeRuntime_block_3647_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) (safeRuntime_block_3647_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 47) (C + ((145) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.push4 (UInt256.ofNat 1978710866) (by native_decide) (by evm_ov)
  have r9 := r8.dup16 (by native_decide) (by evm_ov)
  have r10 := r9.dup16 (by native_decide) (by evm_ov)
  have r11 := r10.dup16 (by native_decide) (by evm_ov)
  have r12 := r11.dup16 (by native_decide) (by evm_ov)
  have r13 := r12.dup16 (by native_decide) (by evm_ov)
  have r14 := r13.dup16 (by native_decide) (by evm_ov)
  have r15 := r14.dup16 (by native_decide) (by evm_ov)
  have r16 := r15.dup16 (by native_decide) (by evm_ov)
  have r17 := r16.dup16 (by native_decide) (by evm_ov)
  have r18 := r17.dup16 (by native_decide) (by evm_ov)
  have r19 := r18.dup16 (by native_decide) (by evm_ov)
  have r20 := r19.caller (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r22 := RD.genMload r21 (by native_decide) (by evm_ov)
  have r23 := r22.dup14 (by native_decide) (by evm_ov)
  have r24 := r23.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r27 := r26.shl (by native_decide) (by evm_ov)
  have r28 := r27.dup2 (by native_decide) (by evm_ov)
  have r29 := RD.genMstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 3712) (by native_decide) (by evm_ov)
  have r33 := r32.swap13 (by native_decide) (by evm_ov)
  have r34 := r33.swap12 (by native_decide) (by evm_ov)
  have r35 := r34.swap11 (by native_decide) (by evm_ov)
  have r36 := r35.swap10 (by native_decide) (by evm_ov)
  have r37 := r36.swap9 (by native_decide) (by evm_ov)
  have r38 := r37.swap8 (by native_decide) (by evm_ov)
  have r39 := r38.swap7 (by native_decide) (by evm_ov)
  have r40 := r39.swap6 (by native_decide) (by evm_ov)
  have r41 := r40.swap5 (by native_decide) (by evm_ov)
  have r42 := r41.swap4 (by native_decide) (by evm_ov)
  have r43 := r42.swap3 (by native_decide) (by evm_ov)
  have r44 := r43.swap2 (by native_decide) (by evm_ov)
  have r45 := r44.swap1 (by native_decide) (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 11256) (by native_decide) (by evm_ov)
  have r47 := r46.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11256)) r47 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3647_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 31 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11256) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3647) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11256) (safeRuntime_block_3647_stack (ee := ee) (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) (safeRuntime_block_3647_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3647 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3712_taken`. -/
def safeRuntime_block_3712_taken_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x2)) :: x2 :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3712. -/
theorem safeRuntime_block_3712_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3735) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3712) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3735) (safeRuntime_block_3712_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.dup8 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := r11.extcodesize (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 3735) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3735)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3712_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3735) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3712) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3735) (safeRuntime_block_3712_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_3712_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3712_fallthrough`. -/
def safeRuntime_block_3712_fallthrough_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x2)) :: x2 :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3712. -/
theorem safeRuntime_block_3712_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3712) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3732) (safeRuntime_block_3712_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.dup8 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := r11.extcodesize (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.iszero (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 3735) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3732)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3712_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x2))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3712) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3732) (safeRuntime_block_3712_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_3712_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3732. -/
theorem safeRuntime_block_3732 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3732) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_3735`. -/
def safeRuntime_block_3735_stack {g : Sat256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((3)) + 2)).toUInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3735. -/
theorem safeRuntime_block_3735 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3735) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3738) (safeRuntime_block_3735_stack (g := g) (C := C) (R := R)) mem aw rdata σ (k + 3) (C + ((5))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.genGas (RD.normalizeCounters (k' := k + 2) (C' := C + ((3))) r2 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3738)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3735_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3735) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3738) (safeRuntime_block_3735_stack (g := g) (C := C) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3735 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 3738: call (0xf1). No RD transition is asserted. Summaries resume at pc 3739 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `safeRuntime_block_3739_taken`. -/
def safeRuntime_block_3739_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3739. -/
theorem safeRuntime_block_3739_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3753) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3739) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3753) (safeRuntime_block_3739_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3753) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3753)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3739_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3753) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3739) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3753) (safeRuntime_block_3739_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3739_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3739_fallthrough`. -/
def safeRuntime_block_3739_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3739. -/
theorem safeRuntime_block_3739_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3739) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3746) (safeRuntime_block_3739_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3753) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3746)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3739_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3739) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3746) (safeRuntime_block_3739_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3739_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3746. -/
theorem safeRuntime_block_3746 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3746) R mem aw rdata σ k C)
    : RDrev Benchmarks.Safe.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by native_decide) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r6 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_3753`. -/
def safeRuntime_block_3753_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3753. -/
theorem safeRuntime_block_3753 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3753) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3758) (safeRuntime_block_3753_stack (R := R)) mem aw rdata σ (k + 5) (C + ((9))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3758)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3753_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3753) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3758) (safeRuntime_block_3753_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3753 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3758`. -/
def safeRuntime_block_3758_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 2500) :: x8 :: (UInt256.ofNat 3773) :: (UInt256.ofNat 3794) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3758. -/
theorem safeRuntime_block_3758 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11455) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3758) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11455) (safeRuntime_block_3758_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw rdata σ (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 3794) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 3773) (by native_decide) (by evm_ov)
  have r4 := r3.dup11 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 2500) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11455) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11455)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3758_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11455) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3758) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11455) (safeRuntime_block_3758_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3758 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3773`. -/
def safeRuntime_block_3773_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft x10 (UInt256.ofNat 6)) :: (UInt256.ofNat 63) :: (UInt256.ofNat 3788) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3773. -/
theorem safeRuntime_block_3773 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11474) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3773) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11474) (safeRuntime_block_3773_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata σ (k + 9) (C + ((30))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 3788) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 63) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r5 := r4.dup14 (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 11474) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11474)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3773_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11474) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3773) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11474) (safeRuntime_block_3773_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3773 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3788`. -/
def safeRuntime_block_3788_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3788. -/
theorem safeRuntime_block_3788 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 7685) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3788) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 7685) (safeRuntime_block_3788_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 7685) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7685)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3788_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 7685) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3788) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 7685) (safeRuntime_block_3788_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3788 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3794`. -/
def safeRuntime_block_3794_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 500) :: x0 :: (UInt256.ofNat 3806) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3794. -/
theorem safeRuntime_block_3794 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11455) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3794) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11455) (safeRuntime_block_3794_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 3806) (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 500) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11455) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11455)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3794_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 11455) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3794) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 11455) (safeRuntime_block_3794_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3794 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3806_taken`. -/
def safeRuntime_block_3806_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3806. -/
theorem safeRuntime_block_3806_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((g.subNat (C + ((1)) + 2)).toUInt256) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3830) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3806) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3830) (safeRuntime_block_3806_taken_stack (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genGas (RD.normalizeCounters (k' := k + 1) (C' := C + ((1))) r1 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3830) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3830)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3806_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((g.subNat (C + ((1)) + 2)).toUInt256) x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3830) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3806) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3830) (safeRuntime_block_3806_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3806_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3806_fallthrough`. -/
def safeRuntime_block_3806_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3806. -/
theorem safeRuntime_block_3806_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((g.subNat (C + ((1)) + 2)).toUInt256) x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3806) (x0 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3814) (safeRuntime_block_3806_fallthrough_stack (R := R)) mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genGas (RD.normalizeCounters (k' := k + 1) (C' := C + ((1))) r1 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3830) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3814)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3806_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt ((g.subNat (C + ((1)) + 2)).toUInt256) x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3806) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3814) (safeRuntime_block_3806_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3806_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3814`. -/
def safeRuntime_block_3814_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 19146146579) (UInt256.ofNat 220)) :: (UInt256.ofNat 3830) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3814. -/
theorem safeRuntime_block_3814 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3814) R mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_3814_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 3830) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 19146146579) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 220) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6898) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6898)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3814_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 6898) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3814) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 6898) (safeRuntime_block_3814_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3814 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3830`. -/
def safeRuntime_block_3830_stack {g : Sat256} {mem : ByteArray} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) + (UInt256.land (x10 + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: x10 :: x10 :: x11 :: (memLoad (UInt256.ofNat 64) mem) :: x12 :: x13 :: (UInt256.ofNat 3940) :: ((g.subNat (C + ((3)) + 2)).toUInt256) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_3830`. -/
def safeRuntime_block_3830_memory {ee : ExecutionEnv} {mem : ByteArray} {x10 : UInt256} {x11 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (ee.calldata.write x11.toNat (x10.toByteArray.write 0 (((memLoad (UInt256.ofNat 64) mem) + ((UInt256.ofNat 32) + (UInt256.mul (UInt256.div ((UInt256.ofNat 31) + x10) (UInt256.ofNat 32)) (UInt256.ofNat 32)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)).toNat x10.toNat) (((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) + x10).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3830. -/
theorem safeRuntime_block_3830 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 28 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3830) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3904) (safeRuntime_block_3830_stack (g := g) (mem := mem) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) (safeRuntime_block_3830_memory (ee := ee) (mem := mem) (x10 := x10) (x11 := x11)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) x10) (((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) + x10) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((183) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) x10) + (3 + 3 * ((x10.toNat + 31) / 32)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) x10) (((UInt256.ofNat 32) + (memLoad (UInt256.ofNat 64) mem)) + x10) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genGas (RD.normalizeCounters (k' := k + 2) (C' := C + ((3))) r2 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 3940) (by native_decide) (by evm_ov)
  have r7 := r6.dup16 (by native_decide) (by evm_ov)
  have r8 := r7.dup16 (by native_decide) (by evm_ov)
  have r9 := r8.dup16 (by native_decide) (by evm_ov)
  have r10 := r9.dup16 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r16 := r15.dup1 (by native_decide) (by evm_ov)
  have r17 := r16.swap2 (by native_decide) (by evm_ov)
  have r18 := r17.div (by native_decide) (by evm_ov)
  have r19 := r18.mul (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r21 := r20.add (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r23 := RD.genMload r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r28 := RD.genMstore r27 (by native_decide) (by evm_ov)
  have r29 := r28.dup1 (by native_decide) (by evm_ov)
  have r30 := r29.swap4 (by native_decide) (by evm_ov)
  have r31 := r30.swap3 (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.dup2 (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := RD.genMstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := r38.dup4 (by native_decide) (by evm_ov)
  have r40 := r39.dup4 (by native_decide) (by evm_ov)
  have r41 := r40.dup1 (by native_decide) (by evm_ov)
  have r42 := r41.dup3 (by native_decide) (by evm_ov)
  have r43 := r42.dup5 (by native_decide) (by evm_ov)
  have r44 := RD.genCalldatacopy r43 (by native_decide) (by evm_ov)
  have r45 := r44.push0 (by native_decide) (by evm_ov)
  have r46 := r45.dup2 (by native_decide) (by evm_ov)
  have r47 := r46.dup5 (by native_decide) (by evm_ov)
  have r48 := r47.add (by native_decide) (by evm_ov)
  have r49 := RD.genMstore r48 (by native_decide) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r51 := r50.not (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r53 := r52.dup3 (by native_decide) (by evm_ov)
  have r54 := r53.add (by native_decide) (by evm_ov)
  have r55 := r54.and (by native_decide) (by evm_ov)
  have r56 := r55.swap1 (by native_decide) (by evm_ov)
  have r57 := r56.pop (by native_decide) (by evm_ov)
  have r58 := r57.dup1 (by native_decide) (by evm_ov)
  have r59 := r58.dup4 (by native_decide) (by evm_ov)
  have r60 := r59.add (by native_decide) (by evm_ov)
  have r61 := r60.swap3 (by native_decide) (by evm_ov)
  have r62 := r61.pop (by native_decide) (by evm_ov)
  have r63 := r62.pop (by native_decide) (by evm_ov)
  have r64 := r63.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3904)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3830_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 28 ≤ 1024)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3830) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3904) (safeRuntime_block_3830_stack (g := g) (mem := mem) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (R := R)) (safeRuntime_block_3830_memory (ee := ee) (mem := mem) (x10 := x10) (x11 := x11)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3830 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_3904_taken`. -/
def safeRuntime_block_3904_taken_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} {x14 : UInt256} {x15 : UInt256} {x16 : UInt256} {x17 : UInt256} {x18 : UInt256} {R : List UInt256} : List UInt256 :=
  (x18 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3904. -/
theorem safeRuntime_block_3904_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) x15) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3921) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3904) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: R) mem aw rdata σ k C)
    : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3921) (safeRuntime_block_3904_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (x15 := x15) (x16 := x16) (x17 := x17) (x18 := x18) (R := R)) mem aw rdata σ (k + 10) (C + ((32))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup15 (by native_decide) (by evm_ov)
  have r6 := r5.dup13 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.eq (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3921) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3921)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_3904_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) x15) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeBytecode 0).contains (UInt256.ofNat 3921) = true)
    (h : RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3904) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Safe.safeBytecode ee g s0 (UInt256.ofNat 3921) (safeRuntime_block_3904_taken_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13) (x14 := x14) (x15 := x15) (x16 := x16) (x17 := x17) (x18 := x18) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_3904_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end safeRuntimeBlocks
