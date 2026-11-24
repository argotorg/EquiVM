import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Automatically generated RD summary for bytecode block at pc 2816. -/
theorem vault_block_2816 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2816) (x0 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)) (((memLoad (UInt256.ofNat 672) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32)).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 704).toNat 32) (UInt256.ofNat 736).toNat 32).readWithPadding (UInt256.ofNat 672).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.caller (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 99841187323991878651857463966695491112958443285409756881630392772141504727511) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r8 := r7.calldataload (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r17 := RD.genLog3 r16 (by native_decide) hperm (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r20 := r19.push0 (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := r21.tstore hperm (by native_decide) (by evm_ov)
  exact RD.genRet r22 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_2886_taken`. -/
def vault_block_2886_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2886. -/
theorem vault_block_2886_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2886) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_2886_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
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
theorem vault_block_2886_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2886) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_2886_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2886_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2886_fallthrough`. -/
def vault_block_2886_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2886. -/
theorem vault_block_2886_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2886) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2898) (vault_block_2886_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2898)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2886_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2886) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2898) (vault_block_2886_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2886_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2898_taken`. -/
def vault_block_2898_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_2898_taken`. -/
def vault_block_2898_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2898. -/
theorem vault_block_2898_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2898) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_2898_taken_stack (R := R)) (vault_block_2898_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
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
theorem vault_block_2898_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2898) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_2898_taken_stack (R := R)) (vault_block_2898_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2898_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2898_fallthrough`. -/
def vault_block_2898_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_2898_fallthrough`. -/
def vault_block_2898_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2898. -/
theorem vault_block_2898_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2898) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2911) (vault_block_2898_fallthrough_stack (R := R)) (vault_block_2898_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.tload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2911)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2898_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2898) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2911) (vault_block_2898_fallthrough_stack (R := R)) (vault_block_2898_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2898_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_2911_taken`. -/
def vault_block_2911_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2911. -/
theorem vault_block_2911_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 608) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 2936) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2911) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2936) R (vault_block_2911_taken_memory (ee := ee) (mem := mem) (σ := σ)) (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.not (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 2936) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2936)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2911_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 608) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 2936) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2911) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2936) R (vault_block_2911_taken_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_2911_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_2911_fallthrough`. -/
def vault_block_2911_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2911. -/
theorem vault_block_2911_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 608) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2911) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2927) R (vault_block_2911_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.not (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 2936) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2927)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2911_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lnot (memLoad (UInt256.ofNat 608) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 5) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2911) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2927) R (vault_block_2911_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_2911_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2927`. -/
def vault_block_2927_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 608) :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2927. -/
theorem vault_block_2927 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 3058) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2927) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3058) (vault_block_2927_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 3058) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3058)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2927_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 3058) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2927) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3058) (vault_block_2927_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2927 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2936`. -/
def vault_block_2936_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 672) :: (UInt256.ofNat 2947) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2936. -/
theorem vault_block_2936 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2936) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_2936_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2947) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6772) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6772)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2936_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2936) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_2936_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2936 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2947_taken`. -/
def vault_block_2947_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) :: (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) :: (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_2947_taken`. -/
def vault_block_2947_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2947. -/
theorem vault_block_2947_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2947) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_2947_taken_stack (mem := mem) (R := R)) (vault_block_2947_taken_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ (k + 33) (C + ((104) + (memExpansionCost aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.xor (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.dup5 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.mul (by native_decide) (by evm_ov)
  have r19 := r18.xor (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.pop (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r25 := RD.genMload r24 (by native_decide) (by evm_ov)
  have r26 := r25.dup1 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.sub (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  have r31 := r30.gt (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r33 := r32.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r33 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2947_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2947) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_2947_taken_stack (mem := mem) (R := R)) (vault_block_2947_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2947_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2947_fallthrough`. -/
def vault_block_2947_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) :: (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) :: (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_2947_fallthrough`. -/
def vault_block_2947_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2947. -/
theorem vault_block_2947_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2947) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2993) (vault_block_2947_fallthrough_stack (mem := mem) (R := R)) (vault_block_2947_fallthrough_memory (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ (k + 33) (C + ((104) + (memExpansionCost aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.xor (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.dup5 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.mul (by native_decide) (by evm_ov)
  have r19 := r18.xor (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.pop (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r25 := RD.genMload r24 (by native_decide) (by evm_ov)
  have r26 := r25.dup1 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.sub (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  have r31 := r30.gt (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r33 := r32.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2993)) r33 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2947_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32))) (UInt256.xor (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)) (memLoad (UInt256.ofNat 608) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) (memLoad (UInt256.ofNat 640) ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2947) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2993) (vault_block_2947_fallthrough_stack (mem := mem) (R := R)) (vault_block_2947_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2947_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_2993`. -/
def vault_block_2993_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 672) :: (UInt256.ofNat 3054) :: R)

/-- Final memory for bytecode block summary `vault_block_2993`. -/
def vault_block_2993_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32) (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2993. -/
theorem vault_block_2993 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7108) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2993) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7108) (vault_block_2993_stack (R := R)) (vault_block_2993_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((51) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3054) (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 7108) (by native_decide) (by evm_ov)
  have r16 := r15.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7108)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_2993_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7108) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 2993) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7108) (vault_block_2993_stack (R := R)) (vault_block_2993_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_2993 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_3054`. -/
def vault_block_3054_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 672) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3054. -/
theorem vault_block_3054 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3054) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3058) (vault_block_3054_stack (R := R)) mem aw rdata σ (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3058)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_3054_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3054) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3058) (vault_block_3054_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_3054 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3058. -/
theorem vault_block_3058 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3058) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (mem.readWithPadding x0.toNat x1.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  exact RD.genRet r1 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 3060. -/
theorem vault_block_3060_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3060) R mem aw rdata σ k C)
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
theorem vault_block_3060_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3060) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_3060_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3060. -/
theorem vault_block_3060_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3060) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3070) R mem aw rdata σ (k + 7) (C + ((22) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3070)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_3060_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3060) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3070) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_3060_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_3070`. -/
def vault_block_3070_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 576) :: (UInt256.ofNat 3131) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_3070`. -/
def vault_block_3070_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32) (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3070. -/
theorem vault_block_3070 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7332) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3070) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7332) (vault_block_3070_stack (R := R)) (vault_block_3070_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 15) (C + ((49) + (memExpansionCost aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 3131) (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 7332) (by native_decide) (by evm_ov)
  have r15 := r14.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7332)) r15 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_3070_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7332) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3070) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7332) (vault_block_3070_stack (R := R)) (vault_block_3070_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_3070 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3131. -/
theorem vault_block_3131 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3131) (x0 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 σ (mem.readWithPadding (UInt256.ofNat 576).toNat x0.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  exact RD.genRet r2 (by native_decide) (by evm_ov)

/-- Final memory for bytecode block summary `vault_block_3136`. -/
def vault_block_3136_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3136. -/
theorem vault_block_3136 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 3162) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3136) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3162) R (vault_block_3136_memory (ee := ee) (mem := mem)) (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) rdata σ (k + 6) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 3162) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3162)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_3136_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 3162) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3136) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3162) R (vault_block_3136_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_3136 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_3146_taken`. -/
def vault_block_3146_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3146. -/
theorem vault_block_3146_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3146) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_3146_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_3146_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 3146) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_3146_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_3146_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end vaultBlocks
