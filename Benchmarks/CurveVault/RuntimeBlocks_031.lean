import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final stack for bytecode block summary `vault_block_8190_taken`. -/
def vault_block_8190_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) :: (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_8190_taken`. -/
def vault_block_8190_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8190. -/
theorem vault_block_8190_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8190) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_8190_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) (vault_block_8190_taken_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 13) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.push0 (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  have r18 := r17.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have r22 := r21.dup1 (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  have r26 := r25.dup2 (by native_decide) (by evm_ov)
  have r27 := r26.lt (by native_decide) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r29 := r28.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r29 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_8190_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8190) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_8190_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) (vault_block_8190_taken_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_8190_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_8190_fallthrough`. -/
def vault_block_8190_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) :: (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_8190_fallthrough`. -/
def vault_block_8190_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8190. -/
theorem vault_block_8190_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8190) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8226) (vault_block_8190_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) (vault_block_8190_fallthrough_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 13) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.push0 (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  have r18 := r17.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have r22 := r21.dup1 (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  have r26 := r25.dup2 (by native_decide) (by evm_ov)
  have r27 := r26.lt (by native_decide) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r29 := r28.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8226)) r29 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_8190_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 128) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 13).toByteArray.write 0 ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8190) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8226) (vault_block_8190_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) (vault_block_8190_fallthrough_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_8190_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_8226`. -/
def vault_block_8226_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_8226`. -/
def vault_block_8226_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8226. -/
theorem vault_block_8226 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains x4 = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8226) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 x4 (vault_block_8226_stack (R := R)) (vault_block_8226_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (UInt256.ofNat 32)) rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r19 := RD.genLog3 r18 (by native_decide) hperm (by evm_ov)
  have r20 := r19.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r20⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_8226_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains x4 = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8226) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 x4 (vault_block_8226_stack (R := R)) (vault_block_8226_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_8226 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8284. -/
theorem vault_block_8284 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.CurveVault.vaultBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  exact RD.genRev r3 (by native_decide) (by evm_ov)

end vaultBlocks
