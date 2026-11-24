import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vyperVaultCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Tests.Pipeline.VyperVault.vyperVaultCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Tests.Pipeline.VyperVault.vyperVaultCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 707. -/
theorem vyperVaultCreation_block_707_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 707) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 773487949) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1399) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_707_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 707) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_707_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 707. -/
theorem vyperVaultCreation_block_707_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 707) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 719) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 773487949) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 719)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_707_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 773487949)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 707) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 719) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_707_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 719. -/
theorem vyperVaultCreation_block_719_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 719) R mem aw rdata σ k C)
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
theorem vyperVaultCreation_block_719_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 719) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_719_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 719. -/
theorem vyperVaultCreation_block_719_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 719) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 729)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_719_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 719) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 729) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_719_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 729. -/
theorem vyperVaultCreation_block_729_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_729_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_729_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 729. -/
theorem vyperVaultCreation_block_729_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 738) R mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 738)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_729_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 729) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 738) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_729_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vyperVaultCreation_block_738_taken`. -/
def vyperVaultCreation_block_738_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 738. -/
theorem vyperVaultCreation_block_738_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt ((sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 849) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 738) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 849) R (vyperVaultCreation_block_738_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 849) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 849) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 849)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_738_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt ((sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 849) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 738) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 849) R (vyperVaultCreation_block_738_taken_memory (ee := ee) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_738_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vyperVaultCreation_block_738_fallthrough`. -/
def vyperVaultCreation_block_738_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 738. -/
theorem vyperVaultCreation_block_738_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt ((sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 738) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 764) R (vyperVaultCreation_block_738_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMstore r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 849) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 764)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_738_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.lt ((sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 738) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 764) R (vyperVaultCreation_block_738_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_738_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_764`. -/
def vyperVaultCreation_block_764_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: ((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: R)

/-- Final memory for bytecode block summary `vyperVaultCreation_block_764`. -/
def vyperVaultCreation_block_764_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 147028384).toByteArray.write 0 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat) (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 764. -/
theorem vyperVaultCreation_block_764 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 764) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 879) (vyperVaultCreation_block_764_stack (ee := ee) (mem := mem) (R := R)) (vyperVaultCreation_block_764_memory (ee := ee) (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((182) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) + (3 + 3 * (((UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat + 31) / 32)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 12) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 47687999144296217495830161024715922219131381522400987873099915989063997325312) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMstore r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
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
  have r62 := r61.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r63 := RD.genMstore r62 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r64 := r63.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 879)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_764_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 764) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 879) (vyperVaultCreation_block_764_stack (ee := ee) (mem := mem) (R := R)) (vyperVaultCreation_block_764_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_764 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 879. -/
theorem vyperVaultCreation_block_879 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 879) (x0 :: R) mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 156) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `vyperVaultCreation_block_885_taken`. -/
def vyperVaultCreation_block_885_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vyperVaultCreation_block_885_taken`. -/
def vyperVaultCreation_block_885_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 885. -/
theorem vyperVaultCreation_block_885_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 885) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_885_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVaultCreation_block_885_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_885_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 885) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_885_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVaultCreation_block_885_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_885_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_885_fallthrough`. -/
def vyperVaultCreation_block_885_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vyperVaultCreation_block_885_fallthrough`. -/
def vyperVaultCreation_block_885_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 885. -/
theorem vyperVaultCreation_block_885_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 885) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 913) (vyperVaultCreation_block_885_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVaultCreation_block_885_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 913)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_885_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 885) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 913) (vyperVaultCreation_block_885_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVaultCreation_block_885_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_885_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_913_taken`. -/
def vyperVaultCreation_block_913_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 913. -/
theorem vyperVaultCreation_block_913_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 913) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_913_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_913_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 913) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_913_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_913_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_913_fallthrough`. -/
def vyperVaultCreation_block_913_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 913. -/
theorem vyperVaultCreation_block_913_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 913) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 936) (vyperVaultCreation_block_913_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 936)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_913_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 913) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 936) (vyperVaultCreation_block_913_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_913_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_936`. -/
def vyperVaultCreation_block_936_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (UInt256.ofNat ee.source.val) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 936. -/
theorem vyperVaultCreation_block_936 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 936) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 952) (vyperVaultCreation_block_936_stack (ee := ee) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 952)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_936_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 936) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 952) (vyperVaultCreation_block_936_stack (ee := ee) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_936 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 952: call (0xf1). No RD transition is asserted. Summaries resume at pc 953 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vyperVaultCreation_block_953_taken`. -/
def vyperVaultCreation_block_953_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 953. -/
theorem vyperVaultCreation_block_953_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 953) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_953_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_953_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 953) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_953_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_953_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_953_fallthrough`. -/
def vyperVaultCreation_block_953_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 953. -/
theorem vyperVaultCreation_block_953_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 953) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 958) (vyperVaultCreation_block_953_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 958)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_953_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 953) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 958) (vyperVaultCreation_block_953_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_953_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 958. -/
theorem vyperVaultCreation_block_958 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 958) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 3)) ByteArray.empty := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 50893955706639834605299804440155310915055312867673792774376955235295819007445) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.calldataload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genLog2 r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sstore r11 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact r12.stop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1008. -/
theorem vyperVaultCreation_block_1008_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 381913916)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1153) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1008) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1153) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 381913916) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1153) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1153) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1153)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1008_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 381913916)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1153) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1008) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1153) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1008_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1008. -/
theorem vyperVaultCreation_block_1008_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 381913916)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1008) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1020) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 381913916) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1153) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1020)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1008_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 381913916)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1008) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1020) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1008_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end vyperVaultCreationBlocks
