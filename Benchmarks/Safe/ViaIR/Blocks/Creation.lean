import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Safe.ViaIR.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR.CreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Safe.ViaIR.safeCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Safe.ViaIR.safeCreationBytecode

/-- Final stack for bytecode block summary `safeCreation_block_0_taken`. -/
def safeCreation_block_0_taken_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 128) :: R)

/-- Final memory for bytecode block summary `safeCreation_block_0_taken`. -/
def safeCreation_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem safeCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeCreationBytecode 0).contains (UInt256.ofNat 26) = true)
    (h : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (safeCreation_block_0_taken_stack (R := R)) (safeCreation_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.ViaIR.safeCreationBytecode.size = 11034 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 26) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 26) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 26)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeCreation_block_0_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.ViaIR.safeCreationBytecode 0).contains (UInt256.ofNat 26) = true)
    (h : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (safeCreation_block_0_taken_stack (R := R)) (safeCreation_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeCreation_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeCreation_block_0_fallthrough`. -/
def safeCreation_block_0_fallthrough_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 128) :: R)

/-- Final memory for bytecode block summary `safeCreation_block_0_fallthrough`. -/
def safeCreation_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem safeCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10) (safeCreation_block_0_fallthrough_stack (R := R)) (safeCreation_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.ViaIR.safeCreationBytecode.size = 11034 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 26) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeCreation_block_0_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10) (safeCreation_block_0_fallthrough_stack (R := R)) (safeCreation_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeCreation_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10. -/
theorem safeCreation_block_10 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 10) (x0 :: R) mem aw rdata σ k C)
    : RDret fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) (UInt256.ofNat 1)) (((Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail).write (UInt256.ofNat 31).toNat mem x0.toNat (UInt256.ofNat 11003).toNat).readWithPadding x0.toNat (UInt256.ofNat 11003).toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.ViaIR.safeCreationBytecode.size = 11034 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 11003) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genCodecopy r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem safeCreation_block_26 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) R mem aw rdata σ k C)
    : RDrev fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.ViaIR.safeCreationBytecode.size = 11034 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 30. -/
theorem safeCreation_block_30 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 30) R mem aw rdata σ k C)
    : RDinvalid fork (Benchmarks.Safe.ViaIR.safeCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.ViaIR.safeCreationBytecode.size = 11034 := by native_decide
  exact RD.invalid r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide))

end Benchmarks.Safe.ViaIR.CreationBlocks
