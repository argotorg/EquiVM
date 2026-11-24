import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vyperVaultCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Tests.Pipeline.VyperVault.vyperVaultCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Tests.Pipeline.VyperVault.vyperVaultCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 1020. -/
theorem vyperVaultCreation_block_1020_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1020) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1020_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1020) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1020_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1020. -/
theorem vyperVaultCreation_block_1020_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1020) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1030) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1030)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1020_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1020) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1030) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1020_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_1030_taken`. -/
def vyperVaultCreation_block_1030_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1030. -/
theorem vyperVaultCreation_block_1030_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1030) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_1030_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1030_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1030) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_1030_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1030_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_1030_fallthrough`. -/
def vyperVaultCreation_block_1030_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1030. -/
theorem vyperVaultCreation_block_1030_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1030) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1041) (vyperVaultCreation_block_1030_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1041)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1030_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1030) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1041) (vyperVaultCreation_block_1030_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1030_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_1041_taken`. -/
def vyperVaultCreation_block_1041_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vyperVaultCreation_block_1041_taken`. -/
def vyperVaultCreation_block_1041_taken_memory {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 1041. -/
theorem vyperVaultCreation_block_1041_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1145) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1041) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1145) (vyperVaultCreation_block_1041_taken_stack (R := R)) (vyperVaultCreation_block_1041_taken_memory (tail := tail) (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((40) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1429) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genCodecopy r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1145) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1145) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1145)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1041_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1145) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1041) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1145) (vyperVaultCreation_block_1041_taken_stack (R := R)) (vyperVaultCreation_block_1041_taken_memory (tail := tail) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1041_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_1041_fallthrough`. -/
def vyperVaultCreation_block_1041_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vyperVaultCreation_block_1041_fallthrough`. -/
def vyperVaultCreation_block_1041_fallthrough_memory {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 1041. -/
theorem vyperVaultCreation_block_1041_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1041) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1060) (vyperVaultCreation_block_1041_fallthrough_stack (R := R)) (vyperVaultCreation_block_1041_fallthrough_memory (tail := tail) (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((40) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1429) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genCodecopy r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1145) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1060)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1041_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1041) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1060) (vyperVaultCreation_block_1041_fallthrough_stack (R := R)) (vyperVaultCreation_block_1041_fallthrough_memory (tail := tail) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1041_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_1060`. -/
def vyperVaultCreation_block_1060_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: ((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: R)

/-- Final memory for bytecode block summary `vyperVaultCreation_block_1060`. -/
def vyperVaultCreation_block_1060_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 147028384).toByteArray.write 0 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat) (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1060. -/
theorem vyperVaultCreation_block_1060 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1060) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1175) (vyperVaultCreation_block_1060_stack (ee := ee) (mem := mem) (R := R)) (vyperVaultCreation_block_1060_memory (ee := ee) (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((182) + (memExpansionCost aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) + (3 + 3 * (((UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat + 31) / 32)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 96) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 192) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 96) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) ((UInt256.ofNat 192) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 192) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 192) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 9) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMstore r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 192) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMload r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := RD.genMload r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := RD.genMstore r25 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := RD.genMload r27 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := RD.genCalldatacopy r40 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := RD.genMload r47 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := r54.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r60 := r59.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r61 := r60.push4 (UInt256.ofNat 147028384) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r62 := r61.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := RD.genMstore r62 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1175)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1060_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1060) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1175) (vyperVaultCreation_block_1060_stack (ee := ee) (mem := mem) (R := R)) (vyperVaultCreation_block_1060_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1060 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1175. -/
theorem vyperVaultCreation_block_1175 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1175) (x0 :: R) mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 188) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1181. -/
theorem vyperVaultCreation_block_1181 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1181) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 4) (memLoad (UInt256.ofNat 64) mem)) ByteArray.empty := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sstore r4 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact r5.stop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1189. -/
theorem vyperVaultCreation_block_1189_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1189) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1553423035) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1399) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1189_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1189) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1189_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1189. -/
theorem vyperVaultCreation_block_1189_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1189) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1201) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1553423035) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1201)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1189_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1553423035)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1189) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1201) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1189_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1201. -/
theorem vyperVaultCreation_block_1201_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1201) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1201_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1201) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1201_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1201. -/
theorem vyperVaultCreation_block_1201_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1201) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1206) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1206)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1201_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1201) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1206) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1201_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1206. -/
theorem vyperVaultCreation_block_1206 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1206) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1217. -/
theorem vyperVaultCreation_block_1217_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1211) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1217) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1211) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1211) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1211)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1217_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1211) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1217) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1211) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1217_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1217. -/
theorem vyperVaultCreation_block_1217_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1217) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1229) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1211) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1229)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1217_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1217) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1229) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1217_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1229. -/
theorem vyperVaultCreation_block_1229_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1229) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1229_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1229) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1229_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1229. -/
theorem vyperVaultCreation_block_1229_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1229) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1234) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1234)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1229_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1229) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1234) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1229_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1234. -/
theorem vyperVaultCreation_block_1234 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1234) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 σ (((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat mem (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1429) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1247. -/
theorem vyperVaultCreation_block_1247_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 669136355)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1247) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 669136355) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1399) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1247_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 669136355)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1247) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1247_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end vyperVaultCreationBlocks
