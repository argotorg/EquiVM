import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vyperVaultCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Tests.Pipeline.VyperVault.vyperVaultCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Tests.Pipeline.VyperVault.vyperVaultCreationBytecode

/-- Final stack for bytecode block summary `vyperVaultCreation_block_366_fallthrough`. -/
def vyperVaultCreation_block_366_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) :: (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vyperVaultCreation_block_366_fallthrough`. -/
def vyperVaultCreation_block_366_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 366. -/
theorem vyperVaultCreation_block_366_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 366) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 398) (vyperVaultCreation_block_366_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vyperVaultCreation_block_366_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMstore r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMstore r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := RD.genMload r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 398)) r25 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_366_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 366) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 398) (vyperVaultCreation_block_366_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (vyperVaultCreation_block_366_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_366_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_398_taken`. -/
def vyperVaultCreation_block_398_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) :: (memLoad (UInt256.ofNat 96) mem) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 398. -/
theorem vyperVaultCreation_block_398_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 398) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_398_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
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
  have r10 := r9.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMload r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_398_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 398) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_398_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_398_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_398_fallthrough`. -/
def vyperVaultCreation_block_398_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) :: (memLoad (UInt256.ofNat 96) mem) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 398. -/
theorem vyperVaultCreation_block_398_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 398) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 421) (vyperVaultCreation_block_398_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
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
  have r10 := r9.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genMload r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 421)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_398_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 398) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 421) (vyperVaultCreation_block_398_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_398_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_421_taken`. -/
def vyperVaultCreation_block_421_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 421. -/
theorem vyperVaultCreation_block_421_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 421) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_421_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMload r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_421_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 421) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_421_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_421_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_421_fallthrough`. -/
def vyperVaultCreation_block_421_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) :: (memLoad (UInt256.ofNat 64) mem) :: ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 421. -/
theorem vyperVaultCreation_block_421_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 421) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 444) (vyperVaultCreation_block_421_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMload r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 444)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_421_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 64) mem)) ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 421) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 444) (vyperVaultCreation_block_421_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_421_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 444. -/
theorem vyperVaultCreation_block_444 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 444) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) x0) ByteArray.empty := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 20644549604082266639320257001935285394590065917650136896563126397825491550916) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMload r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genMstore r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genLog2 r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hperm (by evm_ov)
  exact r15.stop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 497. -/
theorem vyperVaultCreation_block_497_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 497) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3363399026) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1399) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1399)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_497_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1399) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 497) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1399) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_497_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 497. -/
theorem vyperVaultCreation_block_497_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 497) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 509) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3363399026) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1399) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 509)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_497_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3363399026)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 497) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 509) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_497_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 509. -/
theorem vyperVaultCreation_block_509_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 509) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_509_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 509) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_509_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 509. -/
theorem vyperVaultCreation_block_509_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 509) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 514) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 514)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_509_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 509) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 514) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_509_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 514. -/
theorem vyperVaultCreation_block_514_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 514) R mem aw rdata σ k C)
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
theorem vyperVaultCreation_block_514_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 514) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_514_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 514. -/
theorem vyperVaultCreation_block_514_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 514) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 523) R mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.eq (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 523)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_514_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 2) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 514) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 523) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_514_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vyperVaultCreation_block_523_taken`. -/
def vyperVaultCreation_block_523_taken_memory {tail : ByteArray} {mem : ByteArray} : ByteArray :=
  ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 523. -/
theorem vyperVaultCreation_block_523_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 628) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 523) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 628) R (vyperVaultCreation_block_523_taken_memory (tail := tail) (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1429) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 628) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 628) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 628)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_523_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 628) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 523) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 628) R (vyperVaultCreation_block_523_taken_memory (tail := tail) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_523_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vyperVaultCreation_block_523_fallthrough`. -/
def vyperVaultCreation_block_523_fallthrough_memory {tail : ByteArray} {mem : ByteArray} : ByteArray :=
  ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 523. -/
theorem vyperVaultCreation_block_523_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 523) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 543) R (vyperVaultCreation_block_523_fallthrough_memory (tail := tail) (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1429) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genCodecopy r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMload r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.caller (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 628) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 543)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_523_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.xor (UInt256.ofNat ee.source.val) (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 523) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 543) R (vyperVaultCreation_block_523_fallthrough_memory (tail := tail) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 2)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_523_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_543`. -/
def vyperVaultCreation_block_543_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  (((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: ((UInt256.ofNat 32) + (UInt256.land (((UInt256.ofNat 32) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat))) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))) :: R)

/-- Final memory for bytecode block summary `vyperVaultCreation_block_543`. -/
def vyperVaultCreation_block_543_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 147028384).toByteArray.write 0 (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))).toNat (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat) (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 543. -/
theorem vyperVaultCreation_block_543 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 543) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 658) (vyperVaultCreation_block_543_stack (ee := ee) (mem := mem) (R := R)) (vyperVaultCreation_block_543_memory (ee := ee) (mem := mem)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 64) (C + ((182) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) + (3 + 3 * (((UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31)).toNat + 31) / 32)) + (memExpansionCost (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 64) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)) + (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.land (UInt256.sub (⟨0⟩ : UInt256) (memLoad ((UInt256.ofNat 160) + (UInt256.ofNat 32)) ((memLoad ((UInt256.ofNat 64) + (UInt256.ofNat 32)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384).toByteArray.write 0 ((UInt256.ofNat 9).toByteArray.write 0 ((UInt256.ofNat 32).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32) ((UInt256.ofNat 160) + (UInt256.ofNat 32)).toNat 32) (((UInt256.ofNat 160) + (UInt256.ofNat 32)) + (UInt256.ofNat 32)).toNat 32))) (UInt256.ofNat 31))) ((UInt256.ofNat 160) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 9) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
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
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 658)) r64 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_543_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 543) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 658) (vyperVaultCreation_block_543_stack (ee := ee) (mem := mem) (R := R)) (vyperVaultCreation_block_543_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_543 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 658. -/
theorem vyperVaultCreation_block_658 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 658) (x0 :: R) mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 156) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `vyperVaultCreation_block_664`. -/
def vyperVaultCreation_block_664_stack {tail : ByteArray} {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: (memLoad (UInt256.ofNat 64) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: R)

/-- Final memory for bytecode block summary `vyperVaultCreation_block_664`. -/
def vyperVaultCreation_block_664_memory {tail : ByteArray} {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail).write (UInt256.ofNat 1429).toNat ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 664. -/
theorem vyperVaultCreation_block_664 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 664) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 692) (vyperVaultCreation_block_664_stack (tail := tail) (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVaultCreation_block_664_memory (tail := tail) (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (⟨0⟩ : UInt256)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMstore r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sstore r7 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMload r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1429) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genCodecopy r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := RD.genMload r19 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 692)) r21 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_664_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 664) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 692) (vyperVaultCreation_block_664_stack (tail := tail) (ee := ee) (mem := mem) (σ := σ) (R := R)) (vyperVaultCreation_block_664_memory (tail := tail) (ee := ee) (mem := mem) (σ := σ)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3) (⟨0⟩ : UInt256)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vyperVaultCreation_block_664 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 692: call (0xf1). No RD transition is asserted. Summaries resume at pc 693 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `vyperVaultCreation_block_693_taken`. -/
def vyperVaultCreation_block_693_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 693. -/
theorem vyperVaultCreation_block_693_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 693) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_693_taken_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1403) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1403)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_693_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperVault.vyperVaultCreationBytecode 0).contains (UInt256.ofNat 1403) = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 693) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1403) (vyperVaultCreation_block_693_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_693_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vyperVaultCreation_block_693_fallthrough`. -/
def vyperVaultCreation_block_693_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 693. -/
theorem vyperVaultCreation_block_693_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 693) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 698) (vyperVaultCreation_block_693_fallthrough_stack (R := R)) mem aw rdata σ (k + 3) (C + ((16))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1403) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 698)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vyperVaultCreation_block_693_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 693) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 698) (vyperVaultCreation_block_693_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vyperVaultCreation_block_693_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 698. -/
theorem vyperVaultCreation_block_698 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 698) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperVault.vyperVaultCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 3)) (mem.readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperVault.vyperVaultCreationBytecode.size = 1465 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sstore r4 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end vyperVaultCreationBlocks
