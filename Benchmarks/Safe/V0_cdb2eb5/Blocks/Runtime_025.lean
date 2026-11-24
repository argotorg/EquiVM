import Reasoning.Reach
import Benchmarks.Safe.V0_cdb2eb5.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

/-- Final stack for bytecode block summary `safeRuntime_block_4952_fallthrough`. -/
def safeRuntime_block_4952_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: x2 :: x1 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 4952. -/
theorem safeRuntime_block_4952_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x2 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4952) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4963) (safeRuntime_block_4952_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw x2 (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.lt (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 4970) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4963)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4952_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x2 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4952) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4963) (safeRuntime_block_4952_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4952_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4963`. -/
def safeRuntime_block_4963_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 4970) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4963. -/
theorem safeRuntime_block_4963 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11374) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4963) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11374) (safeRuntime_block_4963_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 4970) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11374) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11374)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4963_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11374) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4963) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11374) (safeRuntime_block_4963_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_4963 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_4970`. -/
def safeRuntime_block_4970_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x3 :: (UInt256.ofNat 5027) :: x3 :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 mem ((UInt256.ofNat 32) + ((UInt256.mul (UInt256.ofNat 32) x0) + x1)).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_4970`. -/
def safeRuntime_block_4970_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x4 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x4).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 mem ((UInt256.ofNat 32) + ((UInt256.mul (UInt256.ofNat 32) x0) + x1)).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 4970. -/
theorem safeRuntime_block_4970 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11030) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4970) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11030) (safeRuntime_block_4970_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_4970_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) (M (M (M (M aw ((UInt256.ofNat 32) + ((UInt256.mul (UInt256.ofNat 32) x0) + x1)) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.swap3 (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.mul (by native_decide) (by evm_ov)
  have r14 := r13.swap3 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.swap3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := r17.dup2 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.swap2 (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap3 (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  have r33 := r32.swap4 (by native_decide) (by evm_ov)
  have r34 := RD.genMstore r33 (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r36 := r35.swap1 (by native_decide) (by evm_ov)
  have r37 := r36.swap3 (by native_decide) (by evm_ov)
  have r38 := RD.genKeccak256 r37 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r39⟩ := RD.sload r38 (by native_decide) (by evm_ov)
  have r40 := r39.swap1 (by native_decide) (by evm_ov)
  have r41 := r40.swap2 (by native_decide) (by evm_ov)
  have r42 := r41.and (by native_decide) (by evm_ov)
  have r43 := r42.swap1 (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 5027) (by native_decide) (by evm_ov)
  have r45 := r44.dup2 (by native_decide) (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 11030) (by native_decide) (by evm_ov)
  have r47 := r46.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11030)) r47 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_4970_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11030) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4970) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11030) (safeRuntime_block_4970_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (safeRuntime_block_4970_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x4 := x4)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_4970 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5027`. -/
def safeRuntime_block_5027_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5027. -/
theorem safeRuntime_block_5027 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 4901) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5027) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4901) (safeRuntime_block_5027_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 4901) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4901)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5027_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 4901) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5027) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 4901) (safeRuntime_block_5027_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5027 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5034. -/
theorem safeRuntime_block_5034_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5090) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5034) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5090) (x0 :: x1 :: R) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.eq (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 5090) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5090)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5034_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5090) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5034) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5090) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5034_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5034. -/
theorem safeRuntime_block_5034_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5034) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5052) (x0 :: x1 :: R) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.eq (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 5090) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5052)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5034_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5034) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5052) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5034_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5052`. -/
def safeRuntime_block_5052_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (UInt256.ofNat 1) :: (UInt256.ofNat 5063) :: x2 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5052. -/
theorem safeRuntime_block_5052 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11054) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5052) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11054) (safeRuntime_block_5052_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.dup3 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5063) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 11054) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11054)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5052_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11054) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5052) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11054) (safeRuntime_block_5052_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5052 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5063. -/
theorem safeRuntime_block_5063_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x1 mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5079) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5079) (x0 :: x1 :: R) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5079) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5079)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5063_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x1 mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5079) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5079) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5063_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5063. -/
theorem safeRuntime_block_5063_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x1 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5072) (x0 :: x1 :: R) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5079) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5072)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5063_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt x0 (memLoad x1 mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5063) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5072) (x0 :: x1 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5063_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5072`. -/
def safeRuntime_block_5072_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5079) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5072. -/
theorem safeRuntime_block_5072 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11374) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5072) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11374) (safeRuntime_block_5072_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5079) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11374) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11374)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5072_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 11374) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5072) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 11374) (safeRuntime_block_5072_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5072 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5079`. -/
def safeRuntime_block_5079_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: (memLoad (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5079. -/
theorem safeRuntime_block_5079 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5079) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5090) (safeRuntime_block_5079_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((26) + (memExpansionCost aw (((UInt256.ofNat 32) + (UInt256.mul (UInt256.ofNat 32) x0)) + x1) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.mul (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5090)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5079_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5079) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5090) (safeRuntime_block_5079_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5079 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5090`. -/
def safeRuntime_block_5090_stack {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x2 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_5090`. -/
def safeRuntime_block_5090_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5090. -/
theorem safeRuntime_block_5090 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x5 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5090) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x5 (safeRuntime_block_5090_stack (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_5090_memory (mem := mem) (x0 := x0) (x2 := x2)) (M aw x2 (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((33) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.swap3 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5090_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x5 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5090) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x5 (safeRuntime_block_5090_stack (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_5090_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5090 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_5101_taken`. -/
def safeRuntime_block_5101_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5101. -/
theorem safeRuntime_block_5101_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5146) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5101) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5146) R (safeRuntime_block_5101_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 5146) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5146)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5101_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5146) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5101) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5146) R (safeRuntime_block_5101_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_5101_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `safeRuntime_block_5101_fallthrough`. -/
def safeRuntime_block_5101_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5101. -/
theorem safeRuntime_block_5101_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5101) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5130) R (safeRuntime_block_5101_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 5146) (by native_decide) (by evm_ov)
  have r21 := r20.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5130)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5101_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 2).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5101) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5130) R (safeRuntime_block_5101_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_5101_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5130`. -/
def safeRuntime_block_5130_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftLeft (UInt256.ofNat 19146146611) (UInt256.ofNat 220)) :: (UInt256.ofNat 5146) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5130. -/
theorem safeRuntime_block_5130 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 6990) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5130) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 6990) (safeRuntime_block_5130_stack (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5146) (by native_decide) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 19146146611) (width := 5) (op := .PUSH5) (by decide) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 220) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 6990) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6990)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5130_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 6990) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5130) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 6990) (safeRuntime_block_5130_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5130 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5146`. -/
def safeRuntime_block_5146_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `safeRuntime_block_5146`. -/
def safeRuntime_block_5146_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5146. -/
theorem safeRuntime_block_5146 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5146) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x1 (safeRuntime_block_5146_stack (R := R)) (safeRuntime_block_5146_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 1)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := RD.genKeccak256 r14 (by native_decide) (by evm_ov)
  have r16 := r15.dup6 (by native_decide) (by evm_ov)
  have r17 := r16.dup5 (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := r21.dup1 (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r27⟩ := RD.sstore r26 hperm (by native_decide) (by evm_ov)
  have r28 := RD.genMload r27 (by native_decide) (by evm_ov)
  have r29 := r28.dup4 (by native_decide) (by evm_ov)
  have r30 := r29.swap2 (by native_decide) (by evm_ov)
  have r31 := r30.pushConst (UInt256.ofNat 109744027374643845595422045803650255011224469847570155378144108490179203321244) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := RD.genLog3 r32 (by native_decide) hperm (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r35⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5146_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x1 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5146) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x1 (safeRuntime_block_5146_stack (R := R)) (safeRuntime_block_5146_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.ofNat 8).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := safeRuntime_block_5146 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5217`. -/
def safeRuntime_block_5217_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((keccakWord (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96) ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32)) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_5217`. -/
def safeRuntime_block_5217_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0 ((UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5217. -/
theorem safeRuntime_block_5217 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5283) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5217) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5283) (safeRuntime_block_5217_stack (ee := ee) (mem := mem) (R := R)) (safeRuntime_block_5217_memory (ee := ee) (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)) rdata σ (k + 28) (C + ((77) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)) + (30 + 6 * (((UInt256.ofNat 96).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5283) (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 32523383700587834770323112271211932718128200013265661849047136999858837557784) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.chainid (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.address (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := RD.genKeccak256 r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap2 (by native_decide) (by evm_ov)
  have r25 := r24.pop (by native_decide) (by evm_ov)
  have r26 := r25.pop (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5283)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5217_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 5283) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5217) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5283) (safeRuntime_block_5217_stack (ee := ee) (mem := mem) (R := R)) (safeRuntime_block_5217_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5217 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5283`. -/
def safeRuntime_block_5283_stack {mem : ByteArray} {x0 : UInt256} {x3 : UInt256} {x4 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: x3 :: x0 :: (memLoad (UInt256.ofNat 64) mem) :: x11 :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_5283`. -/
def safeRuntime_block_5283_memory {ee : ExecutionEnv} {mem : ByteArray} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {x12 : UInt256} {x13 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 (x6.toByteArray.write 0 (x7.toByteArray.write 0 (x8.toByteArray.write 0 (x9.toByteArray.write 0 ((keccakWord (memLoad (UInt256.ofNat 64) mem) x10 (ee.calldata.write x11.toNat mem (memLoad (UInt256.ofNat 64) mem).toNat x10.toNat)).toByteArray.write 0 (x12.toByteArray.write 0 (x13.toByteArray.write 0 ((UInt256.ofNat 84814075808141314178395468817534025465894426928601295766380145544921651250904).toByteArray.write 0 (ee.calldata.write x11.toNat mem (memLoad (UInt256.ofNat 64) mem).toNat x10.toNat) (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 192)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 224)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 256)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5283. -/
theorem safeRuntime_block_5283 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5283) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5389) (safeRuntime_block_5283_stack (mem := mem) (x0 := x0) (x3 := x3) (x4 := x4) (x11 := x11) (R := R)) (safeRuntime_block_5283_memory (ee := ee) (mem := mem) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13)) (M (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((182) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) + (3 + 3 * ((x10.toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) + (30 + 6 * ((x10.toNat + 31) / 32)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) x10) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 128)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 192)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 256)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup11 (by native_decide) (by evm_ov)
  have r7 := r6.dup13 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := RD.genCalldatacopy r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap10 (by native_decide) (by evm_ov)
  have r11 := r10.dup11 (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  have r13 := r12.pushConst (UInt256.ofNat 84814075808141314178395468817534025465894426928601295766380145544921651250904) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r14 := r13.dup12 (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := r16.dup12 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := r18.swap14 (by native_decide) (by evm_ov)
  have r20 := r19.dup15 (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r23 := r22.dup12 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.swap13 (by native_decide) (by evm_ov)
  have r26 := r25.dup14 (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r29 := r28.dup12 (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := RD.genMstore r30 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r33 := r32.dup11 (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := r34.swap9 (by native_decide) (by evm_ov)
  have r36 := r35.swap1 (by native_decide) (by evm_ov)
  have r37 := r36.swap9 (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.pop (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r41 := r40.dup9 (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := r42.swap6 (by native_decide) (by evm_ov)
  have r44 := r43.swap1 (by native_decide) (by evm_ov)
  have r45 := r44.swap6 (by native_decide) (by evm_ov)
  have r46 := RD.genMstore r45 (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r48 := r47.dup8 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := r49.swap4 (by native_decide) (by evm_ov)
  have r51 := r50.swap1 (by native_decide) (by evm_ov)
  have r52 := r51.swap4 (by native_decide) (by evm_ov)
  have r53 := RD.genMstore r52 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r55 := r54.dup7 (by native_decide) (by evm_ov)
  have r56 := r55.add (by native_decide) (by evm_ov)
  have r57 := r56.swap2 (by native_decide) (by evm_ov)
  have r58 := r57.swap1 (by native_decide) (by evm_ov)
  have r59 := r58.swap2 (by native_decide) (by evm_ov)
  have r60 := RD.genMstore r59 (by native_decide) (by evm_ov)
  have r61 := r60.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r62 := r61.dup6 (by native_decide) (by evm_ov)
  have r63 := r62.add (by native_decide) (by evm_ov)
  have r64 := RD.genMstore r63 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5389)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5283_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5283) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5389) (safeRuntime_block_5283_stack (mem := mem) (x0 := x0) (x3 := x3) (x4 := x4) (x11 := x11) (R := R)) (safeRuntime_block_5283_memory (ee := ee) (mem := mem) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (x13 := x13)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5283 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5389`. -/
def safeRuntime_block_5389_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((keccakWord (x3 + (UInt256.ofNat 30)) (UInt256.ofNat 66) (x2.toByteArray.write 0 ((UInt256.ofNat 6401).toByteArray.write 0 ((keccakWord x3 (UInt256.ofNat 352) (x1.toByteArray.write 0 (x0.toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)).toByteArray.write 0 (x1.toByteArray.write 0 (x0.toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) x5.toNat 32) x3.toNat 32) x6.toNat 32)) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_5389`. -/
def safeRuntime_block_5389_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x5 : UInt256} {x6 : UInt256} : ByteArray :=
  (x2.toByteArray.write 0 ((UInt256.ofNat 6401).toByteArray.write 0 ((keccakWord x3 (UInt256.ofNat 352) (x1.toByteArray.write 0 (x0.toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32)).toByteArray.write 0 (x1.toByteArray.write 0 (x0.toByteArray.write 0 mem (x3 + (UInt256.ofNat 288)).toNat 32) (x3 + (UInt256.ofNat 320)).toNat 32) x5.toNat 32) x3.toNat 32) x6.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5389. -/
theorem safeRuntime_block_5389 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x7 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5389) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x7 (safeRuntime_block_5389_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (R := R)) (safeRuntime_block_5389_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6)) (M (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) x3 (UInt256.ofNat 352)) x5 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 30)) (UInt256.ofNat 66)) rdata σ (k + 31) (C + ((91) + (memExpansionCost aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) x3 (UInt256.ofNat 352)) + (30 + 6 * (((UInt256.ofNat 352).toNat + 31) / 32)) + (memExpansionCost (M (M (M aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) x3 (UInt256.ofNat 352)) x5 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) x3 (UInt256.ofNat 352)) x5 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) x3 (UInt256.ofNat 352)) x5 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (x3 + (UInt256.ofNat 288)) (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 320)) (⟨32⟩ : UInt256)) x3 (UInt256.ofNat 352)) x5 (⟨32⟩ : UInt256)) x3 (⟨32⟩ : UInt256)) x6 (⟨32⟩ : UInt256)) (x3 + (UInt256.ofNat 30)) (UInt256.ofNat 66)) + (30 + 6 * (((UInt256.ofNat 66).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r2 := r1.dup5 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap4 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 6401) (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.swap2 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap3 (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 66) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 30) (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.swap2 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := RD.genKeccak256 r26 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := r29.pop (by native_decide) (by evm_ov)
  have r31 := r30.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r31 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5389_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains x7 = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5389) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 x7 (safeRuntime_block_5389_stack (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6) (R := R)) (safeRuntime_block_5389_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x5 := x5) (x6 := x6)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5389 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_5430`. -/
def safeRuntime_block_5430_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5438) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5430. -/
theorem safeRuntime_block_5430 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 6964) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5430) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 6964) (safeRuntime_block_5430_stack (R := R)) mem aw rdata σ (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5438) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6964) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6964)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_5430_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V0_cdb2eb5.safeBytecode 0).contains (UInt256.ofNat 6964) = true)
    (h : RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 5430) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V0_cdb2eb5.safeBytecode ee g s0 (UInt256.ofNat 6964) (safeRuntime_block_5430_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_5430 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks
