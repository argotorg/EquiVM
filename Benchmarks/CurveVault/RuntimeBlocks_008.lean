import Reasoning.Reach
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultBlocks

/-- Final stack for bytecode block summary `vault_block_1558`. -/
def vault_block_1558_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 384) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `vault_block_1558`. -/
def vault_block_1558_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1000000000000000).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1558. -/
theorem vault_block_1558 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1780) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1558) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1780) (vault_block_1558_stack (R := R)) (vault_block_1558_memory (mem := mem)) (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.pushConst (UInt256.ofNat 1000000000000000) (width := 7) (op := .PUSH7) (by decide) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1780) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1780)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1558_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1780) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1558) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1780) (vault_block_1558_stack (R := R)) (vault_block_1558_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1558 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1579`. -/
def vault_block_1579_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 448) :: (UInt256.ofNat 1597) :: R)

/-- Final memory for bytecode block summary `vault_block_1579`. -/
def vault_block_1579_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 15) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 384).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1579. -/
theorem vault_block_1579 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1579) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_1579_stack (R := R)) (vault_block_1579_memory (ee := ee) (mem := mem) (σ := σ)) (M aw (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 15) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1597) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 6772) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6772)) r9 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1579_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6772) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1579) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6772) (vault_block_1579_stack (R := R)) (vault_block_1579_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := vault_block_1579 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1597_taken`. -/
def vault_block_1597_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (memLoad (UInt256.ofNat 448) mem) (memLoad (UInt256.ofNat 384) mem)) :: (memLoad (UInt256.ofNat 384) mem) :: (memLoad (UInt256.ofNat 448) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1597. -/
theorem vault_block_1597_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (memLoad (UInt256.ofNat 448) mem) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 448) mem)) (UInt256.isZero (memLoad (UInt256.ofNat 384) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1597) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1597_taken_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((66) + (memExpansionCost aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.mul (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.dup4 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.or (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1597_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (memLoad (UInt256.ofNat 448) mem) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 448) mem)) (UInt256.isZero (memLoad (UInt256.ofNat 384) mem)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1597) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1597_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1597_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1597_fallthrough`. -/
def vault_block_1597_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (memLoad (UInt256.ofNat 448) mem) (memLoad (UInt256.ofNat 384) mem)) :: (memLoad (UInt256.ofNat 384) mem) :: (memLoad (UInt256.ofNat 448) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1597. -/
theorem vault_block_1597_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (memLoad (UInt256.ofNat 448) mem) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 448) mem)) (UInt256.isZero (memLoad (UInt256.ofNat 384) mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1597) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1622) (vault_block_1597_fallthrough_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((66) + (memExpansionCost aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 384) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.mul (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.dup4 (by native_decide) (by evm_ov)
  have r12 := r11.dup4 (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.eq (by native_decide) (by evm_ov)
  have r16 := r15.or (by native_decide) (by evm_ov)
  have r17 := r16.iszero (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r19 := r18.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1622)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1597_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (memLoad (UInt256.ofNat 448) mem) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 384) mem)) (memLoad (UInt256.ofNat 448) mem)) (UInt256.isZero (memLoad (UInt256.ofNat 384) mem)))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1597) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1622) (vault_block_1597_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1597_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1622_taken`. -/
def vault_block_1622_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 1)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1622. -/
theorem vault_block_1622_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 1)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1622) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1622_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.lt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1622_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 1)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1622) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1622_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1622_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1622_fallthrough`. -/
def vault_block_1622_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((x0 + (UInt256.ofNat 1)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1622. -/
theorem vault_block_1622_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 1)) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1622) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1637) (vault_block_1622_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((41))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.lt (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1637)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1622_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt (x0 + (UInt256.ofNat 1)) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1622) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1637) (vault_block_1622_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1622_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1637_taken`. -/
def vault_block_1637_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1637. -/
theorem vault_block_1637_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.xor (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) (UInt256.ofNat 1000000000000000000)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1637_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((46))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.mul (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.xor (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1637_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.xor (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) (UInt256.ofNat 1000000000000000000)) x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1637_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1637_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1637_fallthrough`. -/
def vault_block_1637_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1637. -/
theorem vault_block_1637_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.xor (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) (UInt256.ofNat 1000000000000000000)) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1667) (vault_block_1637_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 12) (C + ((46))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.mul (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.div (by native_decide) (by evm_ov)
  have r10 := r9.xor (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1667)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1637_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.xor (UInt256.div (UInt256.mul x0 (UInt256.ofNat 1000000000000000000)) (UInt256.ofNat 1000000000000000000)) x0) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1667) (vault_block_1637_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1637_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1667_taken`. -/
def vault_block_1667_taken_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) + (UInt256.ofNat 1000)) :: (memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_1667_taken`. -/
def vault_block_1667_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1667. -/
theorem vault_block_1667_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) + (UInt256.ofNat 1000)) (memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1667) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1667_taken_stack (mem := mem) (x0 := x0) (R := R)) (vault_block_1667_taken_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((48) + (memExpansionCost aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1000) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.lt (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1667_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) + (UInt256.ofNat 1000)) (memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1667) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1667_taken_stack (mem := mem) (x0 := x0) (R := R)) (vault_block_1667_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1667_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1667_fallthrough`. -/
def vault_block_1667_fallthrough_stack {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) + (UInt256.ofNat 1000)) :: (memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) :: R)

/-- Final memory for bytecode block summary `vault_block_1667_fallthrough`. -/
def vault_block_1667_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1667. -/
theorem vault_block_1667_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) + (UInt256.ofNat 1000)) (memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1667) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1689) (vault_block_1667_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (vault_block_1667_fallthrough_memory (mem := mem) (x0 := x0)) (M (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)) rdata σ (k + 14) (C + ((48) + (memExpansionCost aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 352) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r6 := RD.genMload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1000) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.lt (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1689)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1667_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32)) + (UInt256.ofNat 1000)) (memLoad (UInt256.ofNat 352) (x0.toByteArray.write 0 mem (UInt256.ofNat 416).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1667) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1689) (vault_block_1667_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (vault_block_1667_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1667_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1689_taken`. -/
def vault_block_1689_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1689_taken`. -/
def vault_block_1689_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 448).toNat 32) (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1689. -/
theorem vault_block_1689_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 320) ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 448).toNat 32) (UInt256.ofNat 480).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1739) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1739) (vault_block_1689_taken_stack (R := R)) (vault_block_1689_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((38) + (memExpansionCost aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 1739) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1739)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1689_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 320) ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 448).toNat 32) (UInt256.ofNat 480).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1739) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1739) (vault_block_1689_taken_stack (R := R)) (vault_block_1689_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1689_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1689_fallthrough`. -/
def vault_block_1689_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1689_fallthrough`. -/
def vault_block_1689_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 448).toNat 32) (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1689. -/
theorem vault_block_1689_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 320) ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 448).toNat 32) (UInt256.ofNat 480).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1708) (vault_block_1689_fallthrough_stack (R := R)) (vault_block_1689_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((38) + (memExpansionCost aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 448) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push0 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 1739) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1708)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1689_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 320) ((⟨0⟩ : UInt256).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 448).toNat 32) (UInt256.ofNat 480).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1689) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1708) (vault_block_1689_fallthrough_stack (R := R)) (vault_block_1689_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1689_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1708`. -/
def vault_block_1708_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 512) :: (UInt256.ofNat 1726) :: R)

/-- Final memory for bytecode block summary `vault_block_1708`. -/
def vault_block_1708_memory {mem : ByteArray} : ByteArray :=
  (mem.write (UInt256.ofNat 416).toNat mem (UInt256.ofNat 64).toNat (UInt256.ofNat 64).toNat)

/-- Automatically generated RD summary for bytecode block at pc 1708. -/
theorem vault_block_1708 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6946) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1708) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6946) (vault_block_1708_stack (R := R)) (vault_block_1708_memory (mem := mem)) (Mmcopy aw (UInt256.ofNat 64) (UInt256.ofNat 416) (UInt256.ofNat 64)) rdata σ (k + 8) (C + ((26) + (mcopyExpansionCost aw (UInt256.ofNat 64) (UInt256.ofNat 416) (UInt256.ofNat 64)) + (3 + 3 * (((UInt256.ofNat 64).toNat + 31) / 32)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.genMcopy r3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1726) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 6946) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6946)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1708_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 6946) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1708) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 6946) (vault_block_1708_stack (R := R)) (vault_block_1708_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1708 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `vault_block_1726`. -/
def vault_block_1726_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 512) mem).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1726. -/
theorem vault_block_1726 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1765) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1726) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) R (vault_block_1726_memory (mem := mem)) (M (M aw (UInt256.ofNat 512) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((24) + (memExpansionCost aw (UInt256.ofNat 512) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 512) (⟨32⟩ : UInt256)) (UInt256.ofNat 480) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1765) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1765)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1726_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 1765) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1726) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) R (vault_block_1726_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1726 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1739_taken`. -/
def vault_block_1739_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 448) mem) :: (memLoad (UInt256.ofNat 416) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1739. -/
theorem vault_block_1739_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 448) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1739) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1739_taken_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1739_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 448) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1739) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) (vault_block_1739_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1739_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1739_fallthrough`. -/
def vault_block_1739_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 448) mem) :: (memLoad (UInt256.ofNat 416) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1739. -/
theorem vault_block_1739_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 448) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1739) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1754) (vault_block_1739_fallthrough_stack (mem := mem) (R := R)) mem (M (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((32) + (memExpansionCost aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 416) (⟨32⟩ : UInt256)) (UInt256.ofNat 448) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := r5.dup1 (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1754)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1739_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 448) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1739) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1754) (vault_block_1739_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1739_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1754`. -/
def vault_block_1754_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `vault_block_1754`. -/
def vault_block_1754_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1754. -/
theorem vault_block_1754 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1754) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) (vault_block_1754_stack (R := R)) (vault_block_1754_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.div (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1765)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1754_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1754) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) (vault_block_1754_stack (R := R)) (vault_block_1754_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1754 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1765. -/
theorem vault_block_1765_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 480) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) rdata σ (k + 6) (C + ((23) + (memExpansionCost aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8284)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1765_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 480) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.CurveVault.vaultBytecode 0).contains (UInt256.ofNat 8284) = true)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 8284) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1765_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1765. -/
theorem vault_block_1765_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 480) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1775) R mem (M aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)) rdata σ (k + 6) (C + ((23) + (memExpansionCost aw (UInt256.ofNat 480) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8284) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1775)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1765_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (UInt256.ofNat 480) mem)) = (UInt256.ofNat 0))
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1765) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1775) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1765_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `vault_block_1775`. -/
def vault_block_1775_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 480) :: (UInt256.ofNat 32) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1775. -/
theorem vault_block_1775 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1775) R mem aw rdata σ k C)
    : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1780) (vault_block_1775_stack (R := R)) mem aw rdata σ (k + 2) (C + ((6))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1780)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem vault_block_1775_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1775) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Benchmarks.CurveVault.vaultBytecode ee g s0 (UInt256.ofNat 1780) (vault_block_1775_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (vault_block_1775 hstack h)
  exact ⟨_, k', C', h'⟩

end vaultBlocks
