import Reasoning.Reach
import Benchmarks.Safe.V2_0e91d99.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 11406. -/
theorem safeRuntime_block_11406_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x8)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11406) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11415) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup9 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11454) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11415)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11406_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x8)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11406) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11415) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11406_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11415`. -/
def safeRuntime_block_11415_stack {ee : ExecutionEnv} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) :: (UInt256.ofNat 11425) :: (uInt256OfByteArray (ee.calldata.readBytes x2.toNat 32)) :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11415. -/
theorem safeRuntime_block_11415 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8949) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11415) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8949) (safeRuntime_block_11415_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.dup3 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 11425) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8949) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8949)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11415_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 8949) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11415) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 8949) (safeRuntime_block_11415_stack (ee := ee) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11415 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11425`. -/
def safeRuntime_block_11425_stack {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x1) :: (x2 + (UInt256.ofNat 32)) :: ((UInt256.ofNat 32) + x3) :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_11425`. -/
def safeRuntime_block_11425_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0).toByteArray.write 0 mem x2.toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11425. -/
theorem safeRuntime_block_11425 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11406) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11425) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11406) (safeRuntime_block_11425_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (safeRuntime_block_11425_memory (mem := mem) (x0 := x0) (x2 := x2)) (M aw x2 (⟨32⟩ : UInt256)) rdata σ (k + 22) (C + ((69) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.swap3 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.swap3 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.swap2 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 11406) (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11406)) r22 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11425_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11406) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11425) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11406) (safeRuntime_block_11425_stack (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (safeRuntime_block_11425_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11425 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11454`. -/
def safeRuntime_block_11454_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_11454`. -/
def safeRuntime_block_11454_memory {mem : ByteArray} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x5).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x6).toByteArray.write 0 (x7.toByteArray.write 0 mem (x4 + (UInt256.ofNat 32)).toNat 32) (x4 + (UInt256.ofNat 64)).toNat 32) (x4 + (UInt256.ofNat 96)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11454. -/
theorem safeRuntime_block_11454 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x10 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11454) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x10 (safeRuntime_block_11454_stack (x1 := x1) (R := R)) (safeRuntime_block_11454_memory (mem := mem) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7)) (M (M (M aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)) rdata σ (k + 35) (C + ((103) + (memExpansionCost aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (x4 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 64)) (⟨32⟩ : UInt256)) (x4 + (UInt256.ofNat 96)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap7 (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.swap7 (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.pop (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.swap3 (by native_decide) (by evm_ov)
  have r18 := r17.dup4 (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.genMstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap2 (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.swap3 (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := r32.pop (by native_decide) (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r35 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11454_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x10 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11454) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x10 (safeRuntime_block_11454_stack (x1 := x1) (R := R)) (safeRuntime_block_11454_memory (mem := mem) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11454 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11495_taken`. -/
def safeRuntime_block_11495_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11495. -/
theorem safeRuntime_block_11495_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11511) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11495) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11511) (safeRuntime_block_11495_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 11511) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11511)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11495_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11511) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11495) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11511) (safeRuntime_block_11495_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11495_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11495_fallthrough`. -/
def safeRuntime_block_11495_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11495. -/
theorem safeRuntime_block_11495_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11495) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11508) (safeRuntime_block_11495_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 11511) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11508)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11495_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11495) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11508) (safeRuntime_block_11495_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11495_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11508. -/
theorem safeRuntime_block_11508 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11508) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V2_0e91d99.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_11511_taken`. -/
def safeRuntime_block_11511_taken_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11511. -/
theorem safeRuntime_block_11511_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.isZero (UInt256.isZero (memLoad x1 mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6891) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11511) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6891) (safeRuntime_block_11511_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((35) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.eq (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 6891) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6891)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11511_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.isZero (UInt256.isZero (memLoad x1 mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 6891) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11511) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 6891) (safeRuntime_block_11511_taken_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11511_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11511_fallthrough`. -/
def safeRuntime_block_11511_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11511. -/
theorem safeRuntime_block_11511_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.isZero (UInt256.isZero (memLoad x1 mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11511) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11523) (safeRuntime_block_11511_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata σ (k + 10) (C + ((35) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.eq (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 6891) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11523)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11511_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.eq (memLoad x1 mem) (UInt256.isZero (UInt256.isZero (memLoad x1 mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11511) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11523) (safeRuntime_block_11511_fallthrough_stack (mem := mem) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11511_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11523. -/
theorem safeRuntime_block_11523 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11523) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.Safe.V2_0e91d99.safeBytecode g s0 := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `safeRuntime_block_11526_taken`. -/
def safeRuntime_block_11526_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11526. -/
theorem safeRuntime_block_11526_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11540) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11526) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11540) (safeRuntime_block_11526_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11540) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11540)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11526_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11540) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11526) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11540) (safeRuntime_block_11526_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11526_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11526_fallthrough`. -/
def safeRuntime_block_11526_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11526. -/
theorem safeRuntime_block_11526_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11526) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11533) (safeRuntime_block_11526_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11540) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11533)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11526_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11526) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11533) (safeRuntime_block_11526_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11526_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11533`. -/
def safeRuntime_block_11533_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 11540) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11533. -/
theorem safeRuntime_block_11533 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11004) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11533) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11004) (safeRuntime_block_11533_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 11540) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11004) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11004)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11533_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11004) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11533) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11004) (safeRuntime_block_11533_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11533 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11540`. -/
def safeRuntime_block_11540_stack {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.lnot (⟨0⟩ : UInt256)) + x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11540. -/
theorem safeRuntime_block_11540 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11540) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x2 (safeRuntime_block_11540_stack (x1 := x1) (R := R)) mem aw rdata σ (k + 7) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11540_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains x2 = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11540) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 x2 (safeRuntime_block_11540_stack (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11540 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11547_taken`. -/
def safeRuntime_block_11547_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul x1 x0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11547. -/
theorem safeRuntime_block_11547_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.eq x1 (UInt256.div (UInt256.mul x1 x0) x0)) (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 2853) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 2853) (safeRuntime_block_11547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((51))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.mul (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.dup5 (by native_decide) (by evm_ov)
  have r11 := r10.eq (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 2853) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2853)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11547_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.eq x1 (UInt256.div (UInt256.mul x1 x0) x0)) (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 2853) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 2853) (safeRuntime_block_11547_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11547_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11547_fallthrough`. -/
def safeRuntime_block_11547_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul x1 x0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11547. -/
theorem safeRuntime_block_11547_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.eq x1 (UInt256.div (UInt256.mul x1 x0) x0)) (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11563) (safeRuntime_block_11547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 14) (C + ((51))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.mul (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.dup5 (by native_decide) (by evm_ov)
  have r11 := r10.eq (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 2853) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11563)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11547_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lor (UInt256.eq x1 (UInt256.div (UInt256.mul x1 x0) x0)) (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11547) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11563) (safeRuntime_block_11547_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11547_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11563`. -/
def safeRuntime_block_11563_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 2853) :: R)

/-- Automatically generated RD summary for bytecode block at pc 11563. -/
theorem safeRuntime_block_11563 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11004) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11563) R mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11004) (safeRuntime_block_11563_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 2853) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 11004) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11004)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11563_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11004) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11563) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11004) (safeRuntime_block_11563_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11563 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11570`. -/
def safeRuntime_block_11570_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: (x0 + (UInt256.ofNat 64)) :: (UInt256.ofNat 9699) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `safeRuntime_block_11570`. -/
def safeRuntime_block_11570_memory {mem : ByteArray} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 64).toByteArray.write 0 (x2.toByteArray.write 0 mem x0.toNat 32) (x0 + (UInt256.ofNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 11570. -/
theorem safeRuntime_block_11570 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 9606) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11570) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 9606) (safeRuntime_block_11570_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_11570_memory (mem := mem) (x0 := x0) (x2 := x2)) (M (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((53) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x0 (⟨32⟩ : UInt256)) (x0 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 9699) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.dup5 (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 9606) (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9606)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11570_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 9606) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11570) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 9606) (safeRuntime_block_11570_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (safeRuntime_block_11570_memory (mem := mem) (x0 := x0) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11570 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11594_taken`. -/
def safeRuntime_block_11594_taken_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11594. -/
theorem safeRuntime_block_11594_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11610) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11594) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11610) (safeRuntime_block_11594_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 11610) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11610)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11594_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.V2_0e91d99.safeBytecode 0).contains (UInt256.ofNat 11610) = true)
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11594) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11610) (safeRuntime_block_11594_taken_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11594_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeRuntime_block_11594_fallthrough`. -/
def safeRuntime_block_11594_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 11594. -/
theorem safeRuntime_block_11594_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11594) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11607) (safeRuntime_block_11594_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 11610) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11607)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeRuntime_block_11594_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11594) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.Safe.V2_0e91d99.safeBytecode ee g s0 (UInt256.ofNat 11607) (safeRuntime_block_11594_fallthrough_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeRuntime_block_11594_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end Benchmarks.Safe.V2_0e91d99.RuntimeBlocks
