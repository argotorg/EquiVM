import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.Safe.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace safeCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.Safe.safeCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.Safe.safeCreationBytecode

/-- Final stack for bytecode block summary `safeCreation_block_0_taken`. -/
def safeCreation_block_0_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `safeCreation_block_0_taken`. -/
def safeCreation_block_0_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem safeCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeCreationBytecode 0).contains (UInt256.ofNat 14) = true)
    (h : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14) (safeCreation_block_0_taken_stack (ee := ee) (R := R)) (safeCreation_block_0_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.safeCreationBytecode.size = 11907 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 14) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 14) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 14)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeCreation_block_0_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Safe.safeCreationBytecode 0).contains (UInt256.ofNat 14) = true)
    (h : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14) (safeCreation_block_0_taken_stack (ee := ee) (R := R)) (safeCreation_block_0_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeCreation_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `safeCreation_block_0_fallthrough`. -/
def safeCreation_block_0_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  (ee.weiValue :: R)

/-- Final memory for bytecode block summary `safeCreation_block_0_fallthrough`. -/
def safeCreation_block_0_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem safeCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) (safeCreation_block_0_fallthrough_stack (ee := ee) (R := R)) (safeCreation_block_0_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.safeCreationBytecode.size = 11907 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMstore r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 14) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem safeCreation_block_0_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero ee.weiValue) = (UInt256.ofNat 0))
    (h : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) (safeCreation_block_0_fallthrough_stack (ee := ee) (R := R)) (safeCreation_block_0_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (safeCreation_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 11. -/
theorem safeCreation_block_11 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 11) R mem aw rdata σ k C)
    : RDrev (Benchmarks.Safe.safeCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.safeCreationBytecode.size = 11907 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 14. -/
theorem safeCreation_block_14 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 14) (x0 :: R) mem aw rdata σ k C)
    : RDret (Benchmarks.Safe.safeCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) (UInt256.ofNat 1)) (((Benchmarks.Safe.safeCreationBytecode ++ tail).write (UInt256.ofNat 33).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 11874).toNat).readWithPadding (⟨0⟩ : UInt256).toNat (UInt256.ofNat 11874).toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.safeCreationBytecode.size = 11907 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sstore r4 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 11874) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 33) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genCodecopy r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 32. -/
theorem safeCreation_block_32 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD (Benchmarks.Safe.safeCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 32) R mem aw rdata σ k C)
    : RDinvalid (Benchmarks.Safe.safeCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.Safe.safeCreationBytecode.size = 11907 := by native_decide
  exact RD.invalid r0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide))

end safeCreationBlocks
