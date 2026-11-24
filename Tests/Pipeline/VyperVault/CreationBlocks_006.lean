import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vyperVaultCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Tests.Pipeline.VyperVault.vyperVaultCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Tests.Pipeline.VyperVault.vyperVaultCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 1407. -/
theorem vyperVaultCreation_block_1407_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4033993562)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1407) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1419) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4033993562) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1419)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1407_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4033993562)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1407) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1419) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1407_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1419. -/
theorem vyperVaultCreation_block_1419_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1419) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1419_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1419) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1419_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1419. -/
theorem vyperVaultCreation_block_1419_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1419) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1424) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1424)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1419_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1419) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1424) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1419_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1424. -/
theorem vyperVaultCreation_block_1424 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1424) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1435. -/
theorem vyperVaultCreation_block_1435 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1435) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1439. -/
theorem vyperVaultCreation_block_1439 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1439) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `vyperVaultCreation_block_1443`. -/
def vyperVaultCreation_block_1443_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sdiv x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1443. -/
theorem vyperVaultCreation_block_1443 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1443) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1444) (vyperVaultCreation_block_1443_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((5))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.sdiv (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1444)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_1443_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1443) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1444) (vyperVaultCreation_block_1443_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_1443 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1444: push24 (0x77). No RD transition is asserted. -/

end vyperVaultCreationBlocks
