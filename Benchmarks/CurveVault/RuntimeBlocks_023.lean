import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final stack for bytecode block summary `vault_block_6394_fallthrough`. -/
def vault_block_6394_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6394. -/
theorem vault_block_6394_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6394) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6405) (vault_block_6394_fallthrough_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6405)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6394_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6394) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6405) (vault_block_6394_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_6394_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6405. -/
theorem vault_block_6405 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6405) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ ((x0.toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32).readWithPadding (UInt256.ofNat 128).toNat x3.toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  exact RD.genRet r6 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 6414. -/
theorem vault_block_6414 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6414) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r7 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 6426. -/
theorem vault_block_6426 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6426) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (((UInt256.ofNat 18).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r6 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_6437_taken`. -/
def vault_block_6437_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) :: (⟨0⟩ : UInt256) :: ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32)) :: ((UInt256.ofNat 64) + (UInt256.ofNat 32)) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_6437_taken`. -/
def vault_block_6437_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6437. -/
theorem vault_block_6437_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6437) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_6437_taken_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6437_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r18 := r17.shr (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6437_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6437) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_6437_taken_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6437_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6437_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6437_fallthrough`. -/
def vault_block_6437_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) :: (⟨0⟩ : UInt256) :: ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32)) :: ((UInt256.ofNat 64) + (UInt256.ofNat 32)) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_6437_fallthrough`. -/
def vault_block_6437_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6437. -/
theorem vault_block_6437_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6437) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6470) (vault_block_6437_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6437_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r18 := r17.shr (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6470)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6437_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 6) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6437) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6470) (vault_block_6437_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6437_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6437_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6470. -/
theorem vault_block_6470_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6500) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6470) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6500) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6500) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6500)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6470_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6500) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6470) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6500) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_6470_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6470. -/
theorem vault_block_6470_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6470) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6476) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6500) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6476)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6470_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6470) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6476) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_6470_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6476`. -/
def vault_block_6476_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6476. -/
theorem vault_block_6476 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6476) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (vault_block_6476_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((3))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6477)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6476_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6476) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (vault_block_6476_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_6476 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6477_taken`. -/
def vault_block_6477_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `vault_block_6477_taken`. -/
def vault_block_6477_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 6) + x0) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6477. -/
theorem vault_block_6477_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6477) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (vault_block_6477_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6477_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup6 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 6477) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6477)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6477_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6477) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (vault_block_6477_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6477_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6477_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6477_fallthrough`. -/
def vault_block_6477_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `vault_block_6477_fallthrough`. -/
def vault_block_6477_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 6) + x0) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6477. -/
theorem vault_block_6477_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6500) (vault_block_6477_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6477_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup6 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 6477) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6500)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6477_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6477) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6500) (vault_block_6477_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6477_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6477_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6500. -/
theorem vault_block_6500 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6500) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ ((ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem ((x3 + (UInt256.ofNat 32)) + (memLoad x3 mem)).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad x3 mem)) (UInt256.ofNat 31)).toNat).readWithPadding (UInt256.ofNat 64).toNat (x4 + (UInt256.land (((UInt256.ofNat 32) + (memLoad x3 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem ((x3 + (UInt256.ofNat 32)) + (memLoad x3 mem)).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad x3 mem)) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.calldatasize (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := RD.genCalldatacopy r18 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r23 := r22.not (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.swap1 (by native_decide) (by evm_ov)
  have r32 := r31.pop (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := r34.swap1 (by native_decide) (by evm_ov)
  have r36 := r35.pop (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r37 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_6544_taken`. -/
def vault_block_6544_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) :: (⟨0⟩ : UInt256) :: ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32)) :: ((UInt256.ofNat 64) + (UInt256.ofNat 32)) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_6544_taken`. -/
def vault_block_6544_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6544. -/
theorem vault_block_6544_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6544) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_6544_taken_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6544_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r18 := r17.shr (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6544_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6544) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_6544_taken_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6544_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6544_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6544_fallthrough`. -/
def vault_block_6544_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) :: (⟨0⟩ : UInt256) :: ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32)) :: ((UInt256.ofNat 64) + (UInt256.ofNat 32)) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_6544_fallthrough`. -/
def vault_block_6544_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6544. -/
theorem vault_block_6544_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6544) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6577) (vault_block_6544_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6544_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r18 := r17.shr (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.gt (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r23 := r22.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6577)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6544_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.shiftRight ((UInt256.ofNat 31) + ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 9) (⟨0⟩ : UInt256))) + (UInt256.ofNat 32))) (UInt256.ofNat 5)) (UInt256.ofNat 3)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6544) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6577) (vault_block_6544_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (vault_block_6544_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6544_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6577. -/
theorem vault_block_6577_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6607) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6577) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6607) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6607) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6607)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6577_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6607) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6577) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6607) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_6577_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6577. -/
theorem vault_block_6577_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6577) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6583) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 6607) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6583)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6577_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6577) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6583) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_6577_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6583`. -/
def vault_block_6583_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6583. -/
theorem vault_block_6583 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6583) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (vault_block_6583_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((3))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6584)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6583_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6583) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (vault_block_6583_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_6583 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6584_taken`. -/
def vault_block_6584_taken_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `vault_block_6584_taken`. -/
def vault_block_6584_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 9) + x0) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6584. -/
theorem vault_block_6584_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6584) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (vault_block_6584_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6584_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup6 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 6584) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6584)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6584_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6584) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (vault_block_6584_taken_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6584_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6584_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_6584_fallthrough`. -/
def vault_block_6584_fallthrough_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 1) + x0) :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `vault_block_6584_fallthrough`. -/
def vault_block_6584_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 9) + x0) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6584. -/
theorem vault_block_6584_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6607) (vault_block_6584_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6584_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) (M aw (x3 + (UInt256.shiftLeft x0 (UInt256.ofNat 5))) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup6 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.xor (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 6584) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6607)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_6584_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.xor ((UInt256.ofNat 1) + x0) x1) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6584) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6607) (vault_block_6584_fallthrough_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vault_block_6584_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_6584_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6607. -/
theorem vault_block_6607 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6607) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ ((ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem ((x3 + (UInt256.ofNat 32)) + (memLoad x3 mem)).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad x3 mem)) (UInt256.ofNat 31)).toNat).readWithPadding (UInt256.ofNat 64).toNat (x4 + (UInt256.land (((UInt256.ofNat 32) + (memLoad x3 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat mem ((x3 + (UInt256.ofNat 32)) + (memLoad x3 mem)).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad x3 mem)) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.calldatasize (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := RD.genCalldatacopy r18 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r23 := r22.not (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.swap1 (by native_decide) (by evm_ov)
  have r32 := r31.pop (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := r34.swap1 (by native_decide) (by evm_ov)
  have r36 := r35.pop (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  exact RD.genRet r37 (by native_decide) (by evm_ov)

end vaultBlocks
