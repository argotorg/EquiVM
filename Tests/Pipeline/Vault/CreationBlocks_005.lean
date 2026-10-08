import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.Vault.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Tests.Pipeline.Vault.vaultCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Tests.Pipeline.Vault.vaultCreationBytecode

/-- Final stack for bytecode block summary `vaultCreation_block_955_taken`. -/
def vaultCreation_block_955_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 955. -/
theorem vaultCreation_block_955_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 768) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 955) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 768) (vaultCreation_block_955_taken_stack (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 768) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 768) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 768)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_955_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 768) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 955) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 768) (vaultCreation_block_955_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vaultCreation_block_955_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_955_fallthrough`. -/
def vaultCreation_block_955_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 955. -/
theorem vaultCreation_block_955_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 955) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 967) (vaultCreation_block_955_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 768) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 967)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_955_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.gt x0 (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 955) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 967) (vaultCreation_block_955_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vaultCreation_block_955_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_967`. -/
def vaultCreation_block_967_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `vaultCreation_block_967`. -/
def vaultCreation_block_967_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 9174611594969401989829893562605917783) (UInt256.ofNat 132)).toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 967. -/
theorem vaultCreation_block_967 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 967) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (vaultCreation_block_967_stack (mem := mem) (R := R)) (vaultCreation_block_967_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((89) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genMstore r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 16) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := RD.genMstore r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 9174611594969401989829893562605917783) (width := 16) (op := .PUSH16) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 132) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := RD.genMstore r23 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 100) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 535) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_967_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 967) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (vaultCreation_block_967_stack (mem := mem) (R := R)) (vaultCreation_block_967_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_967 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1025`. -/
def vaultCreation_block_1025_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 803) :: x1 :: (UInt256.ofNat 2835717307) :: (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1025. -/
theorem vaultCreation_block_1025 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1025) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2213) (vaultCreation_block_1025_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push4 (UInt256.ofNat 2835717307) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 803) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 2213) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2213) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2213)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1025_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1025) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2213) (vaultCreation_block_1025_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vaultCreation_block_1025 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1060`. -/
def vaultCreation_block_1060_stack {g : Sat256} {mem : ByteArray} {aw : UInt256} {C : ℕ} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((126) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: x3 :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (UInt256.shiftLeft x2 (UInt256.ofNat 224)) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224)) (UInt256.ofNat 1)))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (UInt256.shiftLeft x2 (UInt256.ofNat 224)) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224)) (UInt256.ofNat 1)))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (UInt256.shiftLeft x2 (UInt256.ofNat 224)) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224)) (UInt256.ofNat 1)))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.ofNat 32) :: ((UInt256.ofNat 68) + (memLoad (UInt256.ofNat 64) mem)) :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `vaultCreation_block_1060`. -/
def vaultCreation_block_1060_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((UInt256.land x1 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((UInt256.land (UInt256.shiftLeft x2 (UInt256.ofNat 224)) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224)) (UInt256.ofNat 1)))).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1060. -/
theorem vaultCreation_block_1060 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1060) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1117) (vaultCreation_block_1060_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vaultCreation_block_1060_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 44) (C + ((128) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := RD.genMload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 224) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMstore r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := RD.genMstore r27 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := RD.genMstore r31 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 68) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := RD.genMload r36 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := r39.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.dup8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := RD.genGas (RD.normalizeCounters (k' := k + 43) (C' := C + ((126) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) r43 (by omega) (by omega)) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1117)) r44 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1060_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1060) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1117) (vaultCreation_block_1060_stack (g := g) (mem := mem) (aw := aw) (C := C) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (vaultCreation_block_1060_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1060 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1117: call (0xf1). No RD transition is asserted. Summaries resume at pc 1118 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vaultCreation_block_1118_taken`. -/
def vaultCreation_block_1118_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1118. -/
theorem vaultCreation_block_1118_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 875) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1118) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 875) (vaultCreation_block_1118_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 875) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 875) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 875)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1118_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 875) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1118) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 875) (vaultCreation_block_1118_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1118_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1118_fallthrough`. -/
def vaultCreation_block_1118_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1118. -/
theorem vaultCreation_block_1118_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1118) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1125) (vaultCreation_block_1118_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 5) (C + ((22))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 875) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1125)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1118_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1118) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1125) (vaultCreation_block_1118_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1118_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1125. -/
theorem vaultCreation_block_1125 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1125) R mem aw rdata σ k C)
    : RDrev (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `vaultCreation_block_1132`. -/
def vaultCreation_block_1132_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat rdata.size)) :: (UInt256.ofNat 911) :: R)

/-- Final memory for bytecode block summary `vaultCreation_block_1132`. -/
def vaultCreation_block_1132_memory {mem : ByteArray} {rdata : ByteArray} : ByteArray :=
  (((memLoad (UInt256.ofNat 64) mem) + (UInt256.land ((UInt256.ofNat rdata.size) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1132. -/
theorem vaultCreation_block_1132 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2238) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1132) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2238) (vaultCreation_block_1132_stack (mem := mem) (rdata := rdata) (R := R)) (vaultCreation_block_1132_memory (mem := mem) (rdata := rdata)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((81) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMload r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.returndatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := RD.genMstore r18 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 911) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.swap2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 2238) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2238) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2238)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1132_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2238) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1132) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2238) (vaultCreation_block_1132_stack (mem := mem) (rdata := rdata) (R := R)) (vaultCreation_block_1132_memory (mem := mem) (rdata := rdata)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1132 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1168_taken`. -/
def vaultCreation_block_1168_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1168. -/
theorem vaultCreation_block_1168_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 939) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1168) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 939) (vaultCreation_block_1168_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 939) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 939) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 939)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1168_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 939) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1168) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 939) (vaultCreation_block_1168_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1168_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1168_fallthrough`. -/
def vaultCreation_block_1168_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1168. -/
theorem vaultCreation_block_1168_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1168) (x0 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1173) (vaultCreation_block_1168_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 939) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1173)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1168_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1168) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1173) (vaultCreation_block_1168_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1168_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1173`. -/
def vaultCreation_block_1173_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 535) :: R)

/-- Final memory for bytecode block summary `vaultCreation_block_1173`. -/
def vaultCreation_block_1173_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1173. -/
theorem vaultCreation_block_1173 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2269) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1173) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2269) (vaultCreation_block_1173_stack (mem := mem) (R := R)) (vaultCreation_block_1173_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2269) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2269) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2269)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1173_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2269) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1173) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2269) (vaultCreation_block_1173_stack (mem := mem) (R := R)) (vaultCreation_block_1173_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1173 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1196`. -/
def vaultCreation_block_1196_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1196. -/
theorem vaultCreation_block_1196 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains x2 = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1196) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 x2 (vaultCreation_block_1196_stack (R := R)) mem aw rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 255)))) (k + 13) (C + ((32) + (Ctload) + (Ctstore))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.tload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.tstore hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail x2 hvalid) (by evm_ov)
  exact RD.normalizeCounters r13 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1196_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains x2 = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1196) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 x2 (vaultCreation_block_1196_stack (R := R)) mem aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat 255)))) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1196 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1210. -/
theorem vaultCreation_block_1210_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 987) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1210) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 987) R mem aw rdata σ (k + 8) (C + ((25) + (Ctload))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.tload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 987) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 987) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 987)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1210_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 987) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1210) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 987) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1210_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1210. -/
theorem vaultCreation_block_1210_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1210) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1221) R mem aw rdata σ (k + 8) (C + ((25) + (Ctload))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.tload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 987) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1221)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1210_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) (UInt256.ofNat 255))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1210) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1221) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1210_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1221`. -/
def vaultCreation_block_1221_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 535) :: R)

/-- Final memory for bytecode block summary `vaultCreation_block_1221`. -/
def vaultCreation_block_1221_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1221. -/
theorem vaultCreation_block_1221 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2135) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1221) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2135) (vaultCreation_block_1221_stack (mem := mem) (R := R)) (vaultCreation_block_1221_memory (mem := mem)) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 2135) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2135) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2135)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1221_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2135) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1221) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2135) (vaultCreation_block_1221_stack (mem := mem) (R := R)) (vaultCreation_block_1221_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1221 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vaultCreation_block_1244_taken`. -/
def vaultCreation_block_1244_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1244. -/
theorem vaultCreation_block_1244_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.gt x0 ((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 1078) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1244) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1078) (x0 :: R) (vaultCreation_block_1244_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.tload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.tstore hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := RD.genMstore r20 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 1078) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1078) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1078)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1244_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.gt x0 ((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 1078) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1244) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1078) (x0 :: R) (vaultCreation_block_1244_taken_memory (ee := ee) (mem := mem)) aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vaultCreation_block_1244_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vaultCreation_block_1244_fallthrough`. -/
def vaultCreation_block_1244_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1244. -/
theorem vaultCreation_block_1244_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.gt x0 ((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1244) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1281) (x0 :: R) (vaultCreation_block_1244_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.tload (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 255) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.tstore hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := RD.genMstore r20 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 1078) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1281)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1244_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.gt x0 ((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1244) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1281) (x0 :: R) (vaultCreation_block_1244_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.lor (UInt256.ofNat 1) (UInt256.land (UInt256.lnot (UInt256.ofNat 255)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vaultCreation_block_1244_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1281`. -/
def vaultCreation_block_1281_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 100) + (memLoad (UInt256.ofNat 64) mem)) :: R)

/-- Final memory for bytecode block summary `vaultCreation_block_1281`. -/
def vaultCreation_block_1281_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 8157363277298032243430218653) (UInt256.ofNat 162)).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4594637) (UInt256.ofNat 229)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1281. -/
theorem vaultCreation_block_1281 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1281) R mem aw rdata σ k C)
    : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (vaultCreation_block_1281_stack (mem := mem) (R := R)) (vaultCreation_block_1281_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) rdata σ (k + 28) (C + ((89) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 229) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genMstore r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 12) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := RD.genMstore r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 8157363277298032243430218653) (width := 12) (op := .PUSH12) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 162) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := RD.genMstore r23 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 100) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 535) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 535) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 535)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1281_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 535) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1281) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 535) (vaultCreation_block_1281_stack (mem := mem) (R := R)) (vaultCreation_block_1281_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vaultCreation_block_1281 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vaultCreation_block_1335`. -/
def vaultCreation_block_1335_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) :: x0 :: (UInt256.ofNat 1108) :: (⟨0⟩ : UInt256) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) :: x0 :: x0 :: R)

/-- Final memory for bytecode block summary `vaultCreation_block_1335`. -/
def vaultCreation_block_1335_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1335. -/
theorem vaultCreation_block_1335 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1335) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2213) (vaultCreation_block_1335_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vaultCreation_block_1335_memory (ee := ee) (mem := mem)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.Vault.vaultCreationBytecode.size = 2673 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1108) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 2213) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 2213) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2213)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vaultCreation_block_1335_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.Vault.vaultCreationBytecode 0).contains (UInt256.ofNat 2213) = true)
    (h : RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1335) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Tests.Pipeline.Vault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 2213) (vaultCreation_block_1335_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vaultCreation_block_1335_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vaultCreation_block_1335 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end vaultCreationBlocks
