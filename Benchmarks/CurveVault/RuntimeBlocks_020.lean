import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final stack for bytecode block summary `vault_block_5603_taken`. -/
def vault_block_5603_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5603. -/
theorem vault_block_5603_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5614) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5603) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5614) (vault_block_5603_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5614) (by native_decide) (by evm_ov)
  have r2 := r1.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5614)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5603_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5614) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5603) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5614) (vault_block_5603_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5603_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5603_fallthrough`. -/
def vault_block_5603_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5603. -/
theorem vault_block_5603_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5603) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5607) (vault_block_5603_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 5614) (by native_decide) (by evm_ov)
  have r2 := r1.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5607)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5603_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5603) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5607) (vault_block_5603_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5603_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5607. -/
theorem vault_block_5607 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5607) R mem aw rdata σ k C)
    : RDrev fork Benchmarks.CurveVault.vaultBytecode g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by native_decide) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  exact RD.genRev r6 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 5614. -/
theorem vault_block_5614 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5614) (x0 :: R) mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)) (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 ((memLoad (UInt256.ofNat 672) mem).toByteArray.write 0 mem (UInt256.ofNat 736).toNat 32) (UInt256.ofNat 768).toNat 32).readWithPadding (UInt256.ofNat 672).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 576) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.caller (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 113923603527463639014809444807069482138736635533632932454551718384408456251611) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r14 := r13.calldataload (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 736) (by native_decide) (by evm_ov)
  have r19 := RD.genLog4 r18 (by native_decide) hperm (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r22 := r21.push0 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := r23.tstore hperm (by native_decide) (by evm_ov)
  exact RD.genRet r24 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_5688_taken`. -/
def vault_block_5688_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5688. -/
theorem vault_block_5688_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5688) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5688_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
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
theorem vault_block_5688_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5688) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5688_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5688_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5688_fallthrough`. -/
def vault_block_5688_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5688. -/
theorem vault_block_5688_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5688) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5700) (vault_block_5688_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5700)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5688_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5688) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5700) (vault_block_5688_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5688_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5700_taken`. -/
def vault_block_5700_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5700_taken`. -/
def vault_block_5700_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5700. -/
theorem vault_block_5700_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5700) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5700_taken_stack (ee := ee) (R := R)) (vault_block_5700_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5700_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5700) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5700_taken_stack (ee := ee) (R := R)) (vault_block_5700_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5700_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5700_fallthrough`. -/
def vault_block_5700_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5700_fallthrough`. -/
def vault_block_5700_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5700. -/
theorem vault_block_5700_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5700) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5714) (vault_block_5700_fallthrough_stack (ee := ee) (R := R)) (vault_block_5700_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((34) + (memExpansionCost aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5714)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5700_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5700) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5714) (vault_block_5700_fallthrough_stack (ee := ee) (R := R)) (vault_block_5700_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5700_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5714_taken`. -/
def vault_block_5714_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_5714_taken`. -/
def vault_block_5714_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5714. -/
theorem vault_block_5714_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5714) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5714_taken_stack (R := R)) (vault_block_5714_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
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
theorem vault_block_5714_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5714) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5714_taken_stack (R := R)) (vault_block_5714_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5714_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5714_fallthrough`. -/
def vault_block_5714_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_5714_fallthrough`. -/
def vault_block_5714_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5714. -/
theorem vault_block_5714_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5714) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5726) (vault_block_5714_fallthrough_stack (R := R)) (vault_block_5714_fallthrough_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.tload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5726)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5714_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5714) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5726) (vault_block_5714_fallthrough_stack (R := R)) (vault_block_5714_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5714_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_5726_taken`. -/
def vault_block_5726_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  (((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5726. -/
theorem vault_block_5726_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 256) (((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 256).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5845) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5726) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5845) R (vault_block_5726_taken_memory (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tstore hperm (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.caller (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have r31 := r30.eq (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 5845) (by native_decide) (by evm_ov)
  have r33 := r32.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5845)) r33 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5726_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 256) (((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 256).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 5845) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5726) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5845) R (vault_block_5726_taken_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5726_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_5726_fallthrough`. -/
def vault_block_5726_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  (((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5726. -/
theorem vault_block_5726_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 256) (((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 256).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5726) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5804) R (vault_block_5726_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.tstore hperm (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by native_decide) (by evm_ov)
  have r14 := r13.dup1 (by native_decide) (by evm_ov)
  have r15 := r14.caller (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.pop (by native_decide) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have r31 := r30.eq (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 5845) (by native_decide) (by evm_ov)
  have r33 := r32.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5804)) r33 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5726_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (memLoad (UInt256.ofNat 256) (((tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 12).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 256).toNat 32)) (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5726) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5804) R (vault_block_5726_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (UInt256.ofNat 1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_5726_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5804_taken`. -/
def vault_block_5804_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5804_taken`. -/
def vault_block_5804_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5804. -/
theorem vault_block_5804_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5804) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5804_taken_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5804_taken_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((63) + (memExpansionCost aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.caller (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
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
theorem vault_block_5804_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5804) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5804_taken_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5804_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5804_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5804_fallthrough`. -/
def vault_block_5804_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)) :: (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_5804_fallthrough`. -/
def vault_block_5804_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5804. -/
theorem vault_block_5804_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5804) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5831) (vault_block_5804_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5804_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((63) + (memExpansionCost aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.caller (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r11 := r10.calldataload (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.gt (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5831)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5804_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32)) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32))) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((memLoad (UInt256.ofNat 192) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 96).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5804) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5831) (vault_block_5804_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (vault_block_5804_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5804_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5831`. -/
def vault_block_5831_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5845) :: R)

/-- Final memory for bytecode block summary `vault_block_5831`. -/
def vault_block_5831_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5831. -/
theorem vault_block_5831 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7939) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5831) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7939) (vault_block_5831_stack (R := R)) (vault_block_5831_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 5845) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 7939) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7939)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5831_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 7939) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5831) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 7939) (vault_block_5831_stack (R := R)) (vault_block_5831_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5831 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5845`. -/
def vault_block_5845_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 5866) :: R)

/-- Final memory for bytecode block summary `vault_block_5845`. -/
def vault_block_5845_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 68).toNat 32)).toByteArray.write 0 (mem.write (UInt256.ofNat 192).toNat mem (UInt256.ofNat 64).toNat (UInt256.ofNat 64).toNat) (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5845. -/
theorem vault_block_5845 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8133) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5845) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8133) (vault_block_5845_stack (R := R)) (vault_block_5845_memory (ee := ee) (mem := mem)) (M (Mmcopy aw (UInt256.ofNat 64) (UInt256.ofNat 192) (UInt256.ofNat 64)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 12) (C + ((36) + (mcopyExpansionCost aw (UInt256.ofNat 64) (UInt256.ofNat 192) (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)) + (memExpansionCost (Mmcopy aw (UInt256.ofNat 64) (UInt256.ofNat 192) (UInt256.ofNat 64)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.genMcopy r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r7 := r6.calldataload (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 5866) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8133) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8133)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5845_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8133) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5845) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8133) (vault_block_5845_stack (R := R)) (vault_block_5845_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5845 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5866. -/
theorem vault_block_5866 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5866) R mem aw rdata σ k C)
    : RDret fork Benchmarks.CurveVault.vaultBytecode g s0 (tstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)) (((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32).readWithPadding (UInt256.ofNat 288).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := r8.tstore hperm (by native_decide) (by evm_ov)
  exact RD.genRet r9 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `vault_block_5882_taken`. -/
def vault_block_5882_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5882. -/
theorem vault_block_5882_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5882) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5882_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
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
theorem vault_block_5882_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5882) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5882_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5882_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5882_fallthrough`. -/
def vault_block_5882_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5882. -/
theorem vault_block_5882_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5882) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5894) (vault_block_5882_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5894)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_5882_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5882) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5894) (vault_block_5882_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5882_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_5894_taken`. -/
def vault_block_5894_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_5894_taken`. -/
def vault_block_5894_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 192).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5894. -/
theorem vault_block_5894_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5894) (x0 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5894_taken_stack (R := R)) (vault_block_5894_taken_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 192) (⟨32⟩ : UInt256)) + (Ctload))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
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
theorem vault_block_5894_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.tstorage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 5894) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_5894_taken_stack (R := R)) (vault_block_5894_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_5894_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end vaultBlocks
