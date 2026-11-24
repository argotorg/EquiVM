import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final stack for bytecode block summary `vault_block_441_taken`. -/
def vault_block_441_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) mem) :: ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 441. -/
theorem vault_block_441_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) + ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) mem))) ((UInt256.ofNat 288) + x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 441) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_441_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((61) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_441_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) + ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) mem))) ((UInt256.ofNat 288) + x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 441) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_441_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_441_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_441_fallthrough`. -/
def vault_block_441_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) mem) :: ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 441. -/
theorem vault_block_441_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) + ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) mem))) ((UInt256.ofNat 288) + x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 441) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 468) (vault_block_441_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((61) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 468)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_441_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) + ((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 288) + (memLoad (UInt256.ofNat 288) mem)) mem))) ((UInt256.ofNat 288) + x0)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 441) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 468) (vault_block_441_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_441_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 468. -/
theorem vault_block_468_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 468) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.gt (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_468_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 468) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_468_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 468. -/
theorem vault_block_468_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 468) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 476) (x0 :: R) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.gt (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 476)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_468_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 468) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 476) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_468_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_476`. -/
def vault_block_476_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 352) :: (((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32))) + (memLoad (UInt256.ofNat 224) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32))) :: R)

/-- Final memory for bytecode block summary `vault_block_476`. -/
def vault_block_476_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32))) + (memLoad (UInt256.ofNat 224) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32))).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32)).toByteArray.write 0 ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))).toNat 32) (UInt256.ofNat 352).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 476. -/
theorem vault_block_476 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 476) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 598) (vault_block_476_stack (mem := mem) (x1 := x1) (R := R)) (vault_block_476_memory (mem := mem) (x1 := x1)) (M (M (M (M (M (M (M (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((172) + (mcopyExpansionCost aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (mcopyExpansionCost (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (memExpansionCost (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (Mmcopy (Mmcopy aw (UInt256.ofNat 416) x1 (UInt256.ofNat 64)) (UInt256.ofNat 224) (UInt256.ofNat 416) (UInt256.ofNat 64)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat).write (UInt256.ofNat 416).toNat (mem.write x1.toNat mem (UInt256.ofNat 416).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 224).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r5 := RD.genMcopy r4 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r14 := RD.genMcopy r13 (by native_decide) (by evm_ov)
  have r15 := r14.pop (by native_decide) (by evm_ov)
  have r16 := r15.push0 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.pushConst (UInt256.ofNat 30512471952665004139033967429211496598118903519306648920024834264573625237504) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r24 := r23.dup1 (by native_decide) (by evm_ov)
  have r25 := RD.genMload r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have r29 := r28.dup4 (by native_decide) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.dup2 (by native_decide) (by evm_ov)
  have r33 := RD.genMload r32 (by native_decide) (by evm_ov)
  have r34 := r33.dup2 (by native_decide) (by evm_ov)
  have r35 := RD.genMstore r34 (by native_decide) (by evm_ov)
  have r36 := r35.pop (by native_decide) (by evm_ov)
  have r37 := r36.pop (by native_decide) (by evm_ov)
  have r38 := r37.dup1 (by native_decide) (by evm_ov)
  have r39 := r38.dup4 (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.swap3 (by native_decide) (by evm_ov)
  have r42 := r41.pop (by native_decide) (by evm_ov)
  have r43 := r42.pop (by native_decide) (by evm_ov)
  have r44 := r43.pop (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r46 := RD.genMload r45 (by native_decide) (by evm_ov)
  have r47 := r46.dup2 (by native_decide) (by evm_ov)
  have r48 := r47.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := r49.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r51 := RD.genMload r50 (by native_decide) (by evm_ov)
  have r52 := r51.dup2 (by native_decide) (by evm_ov)
  have r53 := RD.genMstore r52 (by native_decide) (by evm_ov)
  have r54 := r53.pop (by native_decide) (by evm_ov)
  have r55 := r54.dup1 (by native_decide) (by evm_ov)
  have r56 := r55.dup3 (by native_decide) (by evm_ov)
  have r57 := r56.add (by native_decide) (by evm_ov)
  have r58 := r57.swap2 (by native_decide) (by evm_ov)
  have r59 := r58.pop (by native_decide) (by evm_ov)
  have r60 := r59.pop (by native_decide) (by evm_ov)
  have r61 := r60.dup1 (by native_decide) (by evm_ov)
  have r62 := r61.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r63 := RD.genMstore r62 (by native_decide) (by evm_ov)
  have r64 := r63.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 598)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_476_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 476) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 598) (vault_block_476_stack (mem := mem) (x1 := x1) (R := R)) (vault_block_476_memory (mem := mem) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_476 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_598_taken`. -/
def vault_block_598_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((UInt256.ofNat 31) + ((memLoad x0 mem) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) :: (⟨0⟩ : UInt256) :: ((memLoad x0 mem) + (UInt256.ofNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 598. -/
theorem vault_block_598_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((memLoad x0 mem) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 598) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_598_taken_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((56) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r12 := r11.shr (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.gt (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_598_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((memLoad x0 mem) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 598) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_598_taken_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_598_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_598_fallthrough`. -/
def vault_block_598_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((UInt256.ofNat 31) + ((memLoad x0 mem) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) :: (⟨0⟩ : UInt256) :: ((memLoad x0 mem) + (UInt256.ofNat 32)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 598. -/
theorem vault_block_598_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((memLoad x0 mem) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 598) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 621) (vault_block_598_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem (M aw x0 (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((56) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r12 := r11.shr (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.gt (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r17 := r16.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 621)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_598_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((memLoad x0 mem) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 598) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 621) (vault_block_598_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_598_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 621. -/
theorem vault_block_621_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 651) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 621) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 651) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 651) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 651)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_621_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 651) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 621) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 651) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_621_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 621. -/
theorem vault_block_621_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 621) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 627) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 651) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 627)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_621_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 621) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 627) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_621_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_627`. -/
def vault_block_627_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 627. -/
theorem vault_block_627 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 627) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (vault_block_627_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((3))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 628)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_627_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 627) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (vault_block_627_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_627 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_628_taken`. -/
def vault_block_628_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 628. -/
theorem vault_block_628_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 628) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (vault_block_628_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 6) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 628) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 628)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_628_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 628) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (vault_block_628_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 6) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_628_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_628_fallthrough`. -/
def vault_block_628_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 628. -/
theorem vault_block_628_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 651) (vault_block_628_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 6) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 628) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 651)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_628_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 628) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 651) (vault_block_628_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 6) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_628_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_651`. -/
def vault_block_651_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 31) + ((memLoad (UInt256.ofNat 352) ((((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32))) + (memLoad (UInt256.ofNat 224) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32))).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32)).toByteArray.write 0 ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))).toNat 32) (UInt256.ofNat 352).toNat 32)) + (UInt256.ofNat 32))) :: (⟨0⟩ : UInt256) :: ((memLoad (UInt256.ofNat 352) ((((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32))) + (memLoad (UInt256.ofNat 224) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32))).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32)).toByteArray.write 0 ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))).toNat 32) (UInt256.ofNat 352).toNat 32)) + (UInt256.ofNat 32)) :: (UInt256.ofNat 352) :: R)

/-- Final memory for bytecode block summary `vault_block_651`. -/
def vault_block_651_memory {mem : ByteArray} : ByteArray :=
  ((((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32))) + (memLoad (UInt256.ofNat 224) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32))).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32)).toByteArray.write 0 ((memLoad ((UInt256.ofNat 288) + (UInt256.ofNat 32)) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)).toNat 32) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))).toNat 32) (UInt256.ofNat 352).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 651. -/
theorem vault_block_651 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 651) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 768) (vault_block_651_stack (mem := mem) (R := R)) (vault_block_651_memory (mem := mem)) (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((175) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) ((UInt256.ofNat 288) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + (⟨0⟩ : UInt256)) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) ((UInt256.ofNat 384) + ((⟨0⟩ : UInt256) + (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512).toByteArray.write 0 ((UInt256.ofNat 2).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32) (UInt256.ofNat 320).toNat 32)))) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 44987459963387221799849920963916191249999394982247009911692337097312684736512) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := r18.dup4 (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r21 := r20.add (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := RD.genMload r22 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.pop (by native_decide) (by evm_ov)
  have r27 := r26.pop (by native_decide) (by evm_ov)
  have r28 := r27.dup1 (by native_decide) (by evm_ov)
  have r29 := r28.dup4 (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := r30.swap3 (by native_decide) (by evm_ov)
  have r32 := r31.pop (by native_decide) (by evm_ov)
  have r33 := r32.pop (by native_decide) (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r36 := RD.genMload r35 (by native_decide) (by evm_ov)
  have r37 := r36.dup2 (by native_decide) (by evm_ov)
  have r38 := r37.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := r39.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r41 := RD.genMload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := RD.genMstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.pop (by native_decide) (by evm_ov)
  have r45 := r44.dup1 (by native_decide) (by evm_ov)
  have r46 := r45.dup3 (by native_decide) (by evm_ov)
  have r47 := r46.add (by native_decide) (by evm_ov)
  have r48 := r47.swap2 (by native_decide) (by evm_ov)
  have r49 := r48.pop (by native_decide) (by evm_ov)
  have r50 := r49.pop (by native_decide) (by evm_ov)
  have r51 := r50.dup1 (by native_decide) (by evm_ov)
  have r52 := r51.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r53 := RD.genMstore r52 (by native_decide) (by evm_ov)
  have r54 := r53.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r55 := r54.swap1 (by native_decide) (by evm_ov)
  have r56 := r55.pop (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r58 := r57.dup2 (by native_decide) (by evm_ov)
  have r59 := RD.genMload r58 (by native_decide) (by evm_ov)
  have r60 := r59.add (by native_decide) (by evm_ov)
  have r61 := r60.push0 (by native_decide) (by evm_ov)
  have r62 := r61.dup2 (by native_decide) (by evm_ov)
  have r63 := r62.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r64 := r63.add (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 768)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_651_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 651) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 768) (vault_block_651_stack (mem := mem) (R := R)) (vault_block_651_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_651 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_768_taken`. -/
def vault_block_768_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight x0 (UInt256.ofNat 5)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 768. -/
theorem vault_block_768_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight x0 (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 768) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_768_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r2 := r1.shr (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_768_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight x0 (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 768) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_768_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_768_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_768_fallthrough`. -/
def vault_block_768_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight x0 (UInt256.ofNat 5)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 768. -/
theorem vault_block_768_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight x0 (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 768) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 779) (vault_block_768_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r2 := r1.shr (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 779)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_768_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight x0 (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 768) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 779) (vault_block_768_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_768_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 779. -/
theorem vault_block_779_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 809) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 779) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 809) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 809) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 809)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_779_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 809) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 779) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 809) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_779_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 779. -/
theorem vault_block_779_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 779) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 785) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 809) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 785)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_779_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 779) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 785) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_779_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_785`. -/
def vault_block_785_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 785. -/
theorem vault_block_785 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 785) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (vault_block_785_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((3))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 786)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_785_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 785) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (vault_block_785_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_785 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_786_taken`. -/
def vault_block_786_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 786. -/
theorem vault_block_786_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 786) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (vault_block_786_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 9) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 786) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 786)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_786_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 786) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (vault_block_786_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 9) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_786_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_786_fallthrough`. -/
def vault_block_786_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 786. -/
theorem vault_block_786_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 809) (vault_block_786_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 9) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 786) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 809)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_786_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 786) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 809) (vault_block_786_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 9) + x0) (memLoad (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) mem)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_786_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end vaultBlocks
