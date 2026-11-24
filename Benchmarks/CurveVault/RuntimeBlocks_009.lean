import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Automatically generated RD summary for bytecode block at pc 1780. -/
theorem vault_block_1780 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1780) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (mem.readWithPadding x0.toNat x1.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  exact RD.genRet r1 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1782. -/
theorem vault_block_1782_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1782) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw rdata σ (k + 7) (C + ((22) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1782_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1782) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1782_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1782. -/
theorem vault_block_1782_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1782) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1792) R mem aw rdata σ (k + 7) (C + ((22) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1792)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1782_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1782) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1792) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1782_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1792`. -/
def vault_block_1792_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 576) :: (UInt256.ofNat 1854) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_1792`. -/
def vault_block_1792_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32) (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1792. -/
theorem vault_block_1792 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7108) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1792) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7108) (vault_block_1792_stack (R := R)) (vault_block_1792_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((50) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1854) (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 7108) (by native_decide) (by evm_ov)
  have r15 := r14.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7108)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1792_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7108) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1792) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7108) (vault_block_1792_stack (R := R)) (vault_block_1792_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1792 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1854. -/
theorem vault_block_1854 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1854) (x0 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (mem.readWithPadding (UInt256.ofNat 576).toNat x0.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  exact RD.genRet r2 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1859. -/
theorem vault_block_1859_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1859) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw rdata σ (k + 7) (C + ((22) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1859_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1859) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1859_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1859. -/
theorem vault_block_1859_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1859) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1869) R mem aw rdata σ (k + 7) (C + ((22) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1869)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1859_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1859) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1869) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1859_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1869`. -/
def vault_block_1869_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 576) :: (UInt256.ofNat 1931) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_1869`. -/
def vault_block_1869_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32) (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1869. -/
theorem vault_block_1869 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7332) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1869) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7332) (vault_block_1869_stack (R := R)) (vault_block_1869_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((50) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1931) (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 7332) (by native_decide) (by evm_ov)
  have r15 := r14.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7332)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1869_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7332) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1869) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7332) (vault_block_1869_stack (R := R)) (vault_block_1869_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1869 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1931. -/
theorem vault_block_1931 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1931) (x0 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (mem.readWithPadding (UInt256.ofNat 576).toNat x0.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  exact RD.genRet r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_1936_taken`. -/
def vault_block_1936_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1936. -/
theorem vault_block_1936_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1936) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1936_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1936_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1936) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1936_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1936_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1936_fallthrough`. -/
def vault_block_1936_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1936. -/
theorem vault_block_1936_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1936) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1948) (vault_block_1936_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1948)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1936_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1936) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1948) (vault_block_1936_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1936_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1948_taken`. -/
def vault_block_1948_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1948_taken`. -/
def vault_block_1948_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1948. -/
theorem vault_block_1948_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1948) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1948_taken_stack (R := R)) (vault_block_1948_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.tload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1948_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1948) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1948_taken_stack (R := R)) (vault_block_1948_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1948_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1948_fallthrough`. -/
def vault_block_1948_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1948_fallthrough`. -/
def vault_block_1948_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1948. -/
theorem vault_block_1948_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1948) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1961) (vault_block_1948_fallthrough_stack (R := R)) (vault_block_1948_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.tload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1961)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1948_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1948) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1961) (vault_block_1948_fallthrough_stack (R := R)) (vault_block_1948_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1948_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_1961_taken`. -/
def vault_block_1961_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1961. -/
theorem vault_block_1961_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 288) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1986) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1961) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1986) R (vault_block_1961_taken_memory (ee := ee) (mem := mem) (σ := σ)) (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.not (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1986) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1986)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1961_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 288) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1986) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1961) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1986) R (vault_block_1961_taken_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1961_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_1961_fallthrough`. -/
def vault_block_1961_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1961. -/
theorem vault_block_1961_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 288) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1961) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1977) R (vault_block_1961_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) (M (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.not (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1986) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1977)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1961_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 288) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1961) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1977) R (vault_block_1961_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1961_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1977`. -/
def vault_block_1977_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 288) :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1977. -/
theorem vault_block_1977 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 2054) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1977) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2054) (vault_block_1977_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 2054) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2054)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1977_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 2054) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1977) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2054) (vault_block_1977_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1977 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1986`. -/
def vault_block_1986_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 352) :: (UInt256.ofNat 1997) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1986. -/
theorem vault_block_1986 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1986) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_1986_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1997) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6772) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6772)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1986_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1986) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_1986_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1986 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1997_taken`. -/
def vault_block_1997_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) :: (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) :: (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) :: R)

/-- Final memory for bytecode block summary `vault_block_1997_taken`. -/
def vault_block_1997_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1997. -/
theorem vault_block_1997_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1997) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1997_taken_stack (mem := mem) (R := R)) (vault_block_1997_taken_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((101) + (memExpansionCost aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.xor (by native_decide) (by evm_ov)
  have r14 := r13.dup3 (by native_decide) (by evm_ov)
  have r15 := r14.dup5 (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.mul (by native_decide) (by evm_ov)
  have r18 := r17.xor (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.pop (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have r25 := r24.dup1 (by native_decide) (by evm_ov)
  have r26 := r25.dup3 (by native_decide) (by evm_ov)
  have r27 := r26.sub (by native_decide) (by evm_ov)
  have r28 := r27.dup3 (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := r29.gt (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r32 := r31.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r32 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1997_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1997) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1997_taken_stack (mem := mem) (R := R)) (vault_block_1997_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1997_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1997_fallthrough`. -/
def vault_block_1997_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) :: (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) :: (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) :: R)

/-- Final memory for bytecode block summary `vault_block_1997_fallthrough`. -/
def vault_block_1997_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1997. -/
theorem vault_block_1997_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1997) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2041) (vault_block_1997_fallthrough_stack (mem := mem) (R := R)) (vault_block_1997_fallthrough_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) rdata σ (k + 32) (C + ((101) + (memExpansionCost aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.xor (by native_decide) (by evm_ov)
  have r14 := r13.dup3 (by native_decide) (by evm_ov)
  have r15 := r14.dup5 (by native_decide) (by evm_ov)
  have r16 := r15.gt (by native_decide) (by evm_ov)
  have r17 := r16.mul (by native_decide) (by evm_ov)
  have r18 := r17.xor (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.pop (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have r25 := r24.dup1 (by native_decide) (by evm_ov)
  have r26 := r25.dup3 (by native_decide) (by evm_ov)
  have r27 := r26.sub (by native_decide) (by evm_ov)
  have r28 := r27.dup3 (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := r29.gt (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r32 := r31.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2041)) r32 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1997_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) (memLoad (UInt256.ofNat 288) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) (memLoad (UInt256.ofNat 320) ((memLoad (UInt256.ofNat 352) mem).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1997) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2041) (vault_block_1997_fallthrough_stack (mem := mem) (R := R)) (vault_block_1997_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1997_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2041`. -/
def vault_block_2041_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 352) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_2041`. -/
def vault_block_2041_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2041. -/
theorem vault_block_2041 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2041) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2054) (vault_block_2041_stack (R := R)) (vault_block_2041_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((22) + (memExpansionCost aw (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2054)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2041_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2041) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2054) (vault_block_2041_stack (R := R)) (vault_block_2041_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2041 hstack h)
  exact ⟨_, k', C', h'⟩

end vaultBlocks
