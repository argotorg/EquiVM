import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final stack for bytecode block summary `vault_block_5272_taken`. -/
def vault_block_5272_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) :: (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) :: (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) :: (UInt256.ofNat 10000) :: R)

/-- Final memory for bytecode block summary `vault_block_5272_taken`. -/
def vault_block_5272_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5272. -/
theorem vault_block_5272_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5272) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5272_taken_stack (mem := mem) (R := R)) (vault_block_5272_taken_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((59) + (memExpansionCost aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 10000) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.dup3 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5272_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5272) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5272_taken_stack (mem := mem) (R := R)) (vault_block_5272_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5272_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5272_fallthrough`. -/
def vault_block_5272_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) :: (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) :: (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) :: (UInt256.ofNat 10000) :: R)

/-- Final memory for bytecode block summary `vault_block_5272_fallthrough`. -/
def vault_block_5272_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5272. -/
theorem vault_block_5272_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5272) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5302) (vault_block_5272_fallthrough_stack (mem := mem) (R := R)) (vault_block_5272_fallthrough_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) rdata σ (k + 18) (C + ((59) + (memExpansionCost aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 10000) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.dup3 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5302)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5272_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32)) (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 704) mem).toByteArray.write 0 mem (UInt256.ofNat 672).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5272) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5302) (vault_block_5272_fallthrough_stack (mem := mem) (R := R)) (vault_block_5272_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5272_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5302_taken`. -/
def vault_block_5302_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5302. -/
theorem vault_block_5302_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5326) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5302) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5326) (vault_block_5302_taken_stack (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 5326) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5326)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5302_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5326) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5302) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5326) (vault_block_5302_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5302_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5302_fallthrough`. -/
def vault_block_5302_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5302. -/
theorem vault_block_5302_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5302) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5312) (vault_block_5302_fallthrough_stack (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 5326) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5312)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5302_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5302) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5312) (vault_block_5302_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5302_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5312`. -/
def vault_block_5312_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.xor (memLoad (UInt256.ofNat 640) mem) (memLoad (UInt256.ofNat 672) mem))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5312. -/
theorem vault_block_5312 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5329) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5312) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (vault_block_5312_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((29) + (memExpansionCost aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.xor (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 5329) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5329)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5312_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5329) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5312) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (vault_block_5312_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5312 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5326`. -/
def vault_block_5326_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5326. -/
theorem vault_block_5326 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5326) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (vault_block_5326_stack (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5329)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5326_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5326) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (vault_block_5326_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5326 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5329_taken`. -/
def vault_block_5329_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5329. -/
theorem vault_block_5329_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5453) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5453) (vault_block_5329_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5453) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5453)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5329_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5453) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5453) (vault_block_5329_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5329_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5329_fallthrough`. -/
def vault_block_5329_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5329. -/
theorem vault_block_5329_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5334) (vault_block_5329_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5453) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5334)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5329_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5329) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5334) (vault_block_5329_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5329_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5334. -/
theorem vault_block_5334 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5334) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.CurveVault.vaultBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 35459553518828100093186665586298673531776264337881065331359090201300605861888) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := RD.genMcopy r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.dup4 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.push0 (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.calldatasize (by native_decide) (by evm_ov)
  have r32 := r31.dup3 (by native_decide) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by native_decide) (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.pop (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r37 := r36.not (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r39 := r38.dup3 (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := r43.and (by native_decide) (by evm_ov)
  have r45 := r44.swap1 (by native_decide) (by evm_ov)
  have r46 := r45.pop (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.pop (by native_decide) (by evm_ov)
  have r49 := r48.dup2 (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := r50.swap1 (by native_decide) (by evm_ov)
  have r52 := r51.pop (by native_decide) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by native_decide) (by evm_ov)
  have r54 := r53.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r55 := RD.genMstore r54 (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r58 := r57.add (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 796) (by native_decide) (by evm_ov)
  exact RD.genRev r59 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_5453`. -/
def vault_block_5453_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5474) :: R)

/-- Final memory for bytecode block summary `vault_block_5453`. -/
def vault_block_5453_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5453. -/
theorem vault_block_5453 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8024) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5453) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8024) (vault_block_5453_stack (R := R)) (vault_block_5453_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((39) + (memExpansionCost aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 5474) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8024) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8024)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5453_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8024) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5453) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8024) (vault_block_5453_stack (R := R)) (vault_block_5453_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5453 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5474_taken`. -/
def vault_block_5474_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5474_taken`. -/
def vault_block_5474_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((memLoad (UInt256.ofNat 672) ((UInt256.ofNat 1065911937).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32) (UInt256.ofNat 736).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 1065911937).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32) (UInt256.ofNat 736).toNat 32) (UInt256.ofNat 768).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5474. -/
theorem vault_block_5474_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5474) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5474_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vault_block_5474_taken_memory (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push4 (UInt256.ofNat 1065911937) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := r15.extcodesize (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5474_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5474) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5474_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vault_block_5474_taken_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5474_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5474_fallthrough`. -/
def vault_block_5474_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5474_fallthrough`. -/
def vault_block_5474_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((memLoad (UInt256.ofNat 672) ((UInt256.ofNat 1065911937).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32) (UInt256.ofNat 736).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 1065911937).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32) (UInt256.ofNat 736).toNat 32) (UInt256.ofNat 768).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5474. -/
theorem vault_block_5474_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5474) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5510) (vault_block_5474_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vault_block_5474_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 768) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push4 (UInt256.ofNat 1065911937) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := r15.extcodesize (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5510)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5474_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5474) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5510) (vault_block_5474_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vault_block_5474_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5474_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5510`. -/
def vault_block_5510_stack {g : Sat256} {C : ℕ} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((16)) + 2)).toUInt256) :: x0 :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 764) :: (UInt256.ofNat 36) :: (UInt256.ofNat 736) :: (⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5510. -/
theorem vault_block_5510 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5510) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5522) (vault_block_5510_stack (g := g) (C := C) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((18))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 764) (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := RD.genGas (RD.normalizeCounters (k' := k + 6) (C' := C + ((16))) r6 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5522)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5510_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5510) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5522) (vault_block_5510_stack (g := g) (C := C) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5510 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 5522: call (0xf1). No RD transition is asserted. Summaries resume at pc 5523 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vault_block_5523_taken`. -/
def vault_block_5523_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5523. -/
theorem vault_block_5523_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5534) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5523) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5534) (vault_block_5523_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5534) (by native_decide) (by evm_ov)
  have r2 := r1.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5534)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5523_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5534) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5523) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5534) (vault_block_5523_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5523_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5523_fallthrough`. -/
def vault_block_5523_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5523. -/
theorem vault_block_5523_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5523) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5527) (vault_block_5523_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5534) (by native_decide) (by evm_ov)
  have r2 := r1.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5527)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5523_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5523) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5527) (vault_block_5523_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5523_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5527. -/
theorem vault_block_5527 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5527) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.CurveVault.vaultBytecode g s0 := by
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

/-- Final stack for bytecode block summary `vault_block_5534`. -/
def vault_block_5534_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5569) :: R)

/-- Final memory for bytecode block summary `vault_block_5534`. -/
def vault_block_5534_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 576) ((memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 576) ((memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 704) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5534. -/
theorem vault_block_5534 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7556) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5534) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7556) (vault_block_5534_stack (R := R)) (vault_block_5534_memory (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 5569) (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 7556) (by native_decide) (by evm_ov)
  have r21 := r20.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7556)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5534_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7556) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5534) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7556) (vault_block_5534_stack (R := R)) (vault_block_5534_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5534 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5569_taken`. -/
def vault_block_5569_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 704) mem) :: R)

/-- Final memory for bytecode block summary `vault_block_5569_taken`. -/
def vault_block_5569_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1774616654).toByteArray.write 0 mem (UInt256.ofNat 736).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5569. -/
theorem vault_block_5569_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5569) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5569_taken_stack (mem := mem) (R := R)) (vault_block_5569_taken_memory (mem := mem)) (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push4 (UInt256.ofNat 1774616654) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := r7.extcodesize (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5569_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) mem))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5569) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5569_taken_stack (mem := mem) (R := R)) (vault_block_5569_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5569_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5569_fallthrough`. -/
def vault_block_5569_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 704) mem) :: R)

/-- Final memory for bytecode block summary `vault_block_5569_fallthrough`. -/
def vault_block_5569_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1774616654).toByteArray.write 0 mem (UInt256.ofNat 736).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5569. -/
theorem vault_block_5569_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) mem))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5569) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5590) (vault_block_5569_fallthrough_stack (mem := mem) (R := R)) (vault_block_5569_fallthrough_memory (mem := mem)) (M (M aw (UInt256.ofNat 704) (⟨32⟩ : UInt256)) (UInt256.ofNat 736) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push4 (UInt256.ofNat 1774616654) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := r7.extcodesize (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5590)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5569_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (memLoad (UInt256.ofNat 704) mem))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5569) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5590) (vault_block_5569_fallthrough_stack (mem := mem) (R := R)) (vault_block_5569_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5569_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5590`. -/
def vault_block_5590_stack {g : Sat256} {C : ℕ} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((16)) + 2)).toUInt256) :: x0 :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 764) :: (UInt256.ofNat 4) :: (UInt256.ofNat 736) :: (⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5590. -/
theorem vault_block_5590 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5590) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5602) (vault_block_5590_stack (g := g) (C := C) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((18))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 764) (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := RD.genGas (RD.normalizeCounters (k' := k + 6) (C' := C + ((16))) r6 (by omega) (by omega)) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5602)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5590_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5590) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5602) (vault_block_5590_stack (g := g) (C := C) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5590 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 5602: call (0xf1). No RD transition is asserted. Summaries resume at pc 5603 from a fresh symbolic RD state. -/

end vaultBlocks
