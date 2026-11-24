import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final memory for bytecode block summary `vault_block_5009`. -/
def vault_block_5009_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32) (UInt256.ofNat 608).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5009. -/
theorem vault_block_5009 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5080) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5009) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) R (vault_block_5009_memory (ee := ee) (mem := mem)) (M (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((28) + (memExpansionCost aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.caller (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 5080) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5080)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5009_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5080) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5009) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) R (vault_block_5009_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5009 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5024_taken`. -/
def vault_block_5024_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5024. -/
theorem vault_block_5024_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5024) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5024_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
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
theorem vault_block_5024_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5024) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5024_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5024_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5024_fallthrough`. -/
def vault_block_5024_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5024. -/
theorem vault_block_5024_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5024) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5036) (vault_block_5024_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5036)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5024_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5024) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5036) (vault_block_5024_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5024_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5036`. -/
def vault_block_5036_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_5036`. -/
def vault_block_5036_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32) (UInt256.ofNat 608).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5036. -/
theorem vault_block_5036 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5080) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5036) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) (vault_block_5036_stack (R := R)) (vault_block_5036_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((25) + (memExpansionCost aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) (UInt256.ofNat 608) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.caller (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5080) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5080)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5036_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5080) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5036) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) (vault_block_5036_stack (R := R)) (vault_block_5036_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5036 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5049_taken`. -/
def vault_block_5049_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5049. -/
theorem vault_block_5049_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5049) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5049_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
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
theorem vault_block_5049_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5049) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5049_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5049_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5049_fallthrough`. -/
def vault_block_5049_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5049. -/
theorem vault_block_5049_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5049) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5061) (vault_block_5049_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5061)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5049_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5049) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5061) (vault_block_5049_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5049_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5061_taken`. -/
def vault_block_5061_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5061_taken`. -/
def vault_block_5061_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5061. -/
theorem vault_block_5061_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5061) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5061_taken_stack (ee := ee) (R := R)) (vault_block_5061_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5061_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5061) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5061_taken_stack (ee := ee) (R := R)) (vault_block_5061_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5061_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5061_fallthrough`. -/
def vault_block_5061_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5061_fallthrough`. -/
def vault_block_5061_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 576).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5061. -/
theorem vault_block_5061_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5061) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5076) (vault_block_5061_fallthrough_stack (ee := ee) (R := R)) (vault_block_5061_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 576) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5076)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5061_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5061) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5076) (vault_block_5061_fallthrough_stack (ee := ee) (R := R)) (vault_block_5061_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5061_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5076`. -/
def vault_block_5076_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_5076`. -/
def vault_block_5076_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 608).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5076. -/
theorem vault_block_5076 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5076) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) (vault_block_5076_stack (R := R)) (vault_block_5076_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata σ (k + 2) (C + ((6) + (memExpansionCost aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5080)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5076_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5076) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) (vault_block_5076_stack (R := R)) (vault_block_5076_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5076 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5080. -/
theorem vault_block_5080_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) R mem aw rdata σ k C)
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
theorem vault_block_5080_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5080_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5080. -/
theorem vault_block_5080_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5090) R mem aw rdata σ (k + 7) (C + ((22) + (Ctload))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tload (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5090)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5080_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5080) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5090) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5080_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5090. -/
theorem vault_block_5090_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 608) mem) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5221) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5090) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5221) R mem (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) (k + 9) (C + ((29) + (Ctstore) + (memExpansionCost aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tstore hperm (by native_decide) (by evm_ov)
  have r4 := r3.caller (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 5221) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5221)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5090_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 608) mem) (UInt256.ofNat ee.source.val)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5221) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5090) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5221) R mem aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5090_taken hstack hperm hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5090. -/
theorem vault_block_5090_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 608) mem) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5090) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5104) R mem (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) (k + 9) (C + ((29) + (Ctstore) + (memExpansionCost aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tstore hperm (by native_decide) (by evm_ov)
  have r4 := r3.caller (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.eq (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 5221) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5104)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5090_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 608) mem) (UInt256.ofNat ee.source.val)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5090) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5104) R mem aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5090_fallthrough hstack hperm hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_5104_taken`. -/
def vault_block_5104_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 640).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5104. -/
theorem vault_block_5104_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 640) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 640).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5221) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5104) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5221) R (vault_block_5104_taken_memory (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.caller (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have r28 := r27.eq (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 5221) (by native_decide) (by evm_ov)
  have r30 := r29.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5221)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5104_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 640) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 640).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5221) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5104) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5221) R (vault_block_5104_taken_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5104_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_5104_fallthrough`. -/
def vault_block_5104_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 640).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5104. -/
theorem vault_block_5104_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 640) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 640).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5104) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5179) R (vault_block_5104_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.caller (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := r20.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have r28 := r27.eq (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 5221) (by native_decide) (by evm_ov)
  have r30 := r29.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5179)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5104_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 640) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 640).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5104) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5179) R (vault_block_5104_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5104_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5179_taken`. -/
def vault_block_5179_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5179_taken`. -/
def vault_block_5179_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5179. -/
theorem vault_block_5179_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5179) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5179_taken_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5179_taken_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((63) + (memExpansionCost aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.caller (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.calldataload (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5179_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5179) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5179_taken_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5179_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5179_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5179_fallthrough`. -/
def vault_block_5179_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5179_fallthrough`. -/
def vault_block_5179_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5179. -/
theorem vault_block_5179_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5179) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5207) (vault_block_5179_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5179_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((63) + (memExpansionCost aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.caller (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.calldataload (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5207)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5179_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 640) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 608) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5179) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5207) (vault_block_5179_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5179_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5179_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5207`. -/
def vault_block_5207_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5221) :: R)

/-- Final memory for bytecode block summary `vault_block_5207`. -/
def vault_block_5207_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5207. -/
theorem vault_block_5207 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7939) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5207) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7939) (vault_block_5207_stack (R := R)) (vault_block_5207_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 5221) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7939) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7939)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5207_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7939) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5207) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7939) (vault_block_5207_stack (R := R)) (vault_block_5207_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5207 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5221`. -/
def vault_block_5221_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 672) :: (UInt256.ofNat 5232) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5221. -/
theorem vault_block_5221 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5221) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_5221_stack (R := R)) mem aw rdata σ (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 5232) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6772) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6772)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5221_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5221) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_5221_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5221 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5232`. -/
def vault_block_5232_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 704) :: (UInt256.ofNat 5272) :: R)

/-- Final memory for bytecode block summary `vault_block_5232`. -/
def vault_block_5232_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 640) ((UInt256.ofNat 1).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 640).toNat 32) (UInt256.ofNat 320).toNat 32) (UInt256.ofNat 352).toNat 32) (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5232. -/
theorem vault_block_5232 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7332) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5232) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7332) (vault_block_5232_stack (R := R)) (vault_block_5232_memory (ee := ee) (mem := mem)) (M (M (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 20) (C + ((63) + (memExpansionCost aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) (UInt256.ofNat 640) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 5272) (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 704) (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 7332) (by native_decide) (by evm_ov)
  have r20 := r19.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7332)) r20 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5232_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7332) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5232) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7332) (vault_block_5232_stack (R := R)) (vault_block_5232_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5232 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

end vaultBlocks
