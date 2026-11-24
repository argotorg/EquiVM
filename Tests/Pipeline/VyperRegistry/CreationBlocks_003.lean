import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperRegistry.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace registryCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Tests.Pipeline.VyperRegistry.registryCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Tests.Pipeline.VyperRegistry.registryCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 462. -/
theorem registryCreation_block_462_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4026400085)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 462) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4026400085) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1533) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1533)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_462_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4026400085)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 462) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_462_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 462. -/
theorem registryCreation_block_462_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4026400085)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 462) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 474) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4026400085) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 474)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_462_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4026400085)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 462) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 474) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_462_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 474. -/
theorem registryCreation_block_474_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 474) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1661) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_474_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 474) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_474_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 474. -/
theorem registryCreation_block_474_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 474) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 479) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 479)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_474_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 474) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 479) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_474_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registryCreation_block_479`. -/
def registryCreation_block_479_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 442) :: R)

/-- Automatically generated RD summary for bytecode block at pc 479. -/
theorem registryCreation_block_479 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1537) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 479) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1537) (registryCreation_block_479_stack (R := R)) mem aw rdata σ (k + 3) (C + ((14))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 442) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1537) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.jump (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (j tail (UInt256.ofNat 1537) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1537)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_479_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1537) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 479) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1537) (registryCreation_block_479_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_479 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 486. -/
theorem registryCreation_block_486_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 569) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 486) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 569) R mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 569) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 569) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 569)) r5 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_486_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 569) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 486) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 569) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_486_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 486. -/
theorem registryCreation_block_486_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 486) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 494) R mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 569) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 494)) r5 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_486_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 486) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 494) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_486_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 494. -/
theorem registryCreation_block_494 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 494) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 352) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMstore r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 45876960172658190342144148071268285734312574359075388889094533489066355195904) (width := 32) (op := .PUSH32) (by decide) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 288) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genMstore r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 352) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 37) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMcopy r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := RD.genMload r19 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r28 := r27.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r32 := r31.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r34 := r33.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r35 := r34.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r37 := r36.not (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r39 := r38.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r40 := RD.genMload r39 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r42 := r41.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r43 := r42.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r44 := r43.and (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r45 := r44.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r46 := r45.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r47 := r46.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r48 := r47.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r49 := r48.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r50 := r49.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r51 := r50.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r52 := r51.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r54 := r53.push2 (UInt256.ofNat 320) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r55 := RD.genMstore r54 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r56 := r55.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r58 := r57.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 348) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r59 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Final stack for bytecode block summary `registryCreation_block_613_taken`. -/
def registryCreation_block_613_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 613. -/
theorem registryCreation_block_613_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 613) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) (registryCreation_block_613_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1661) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r8 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_613_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 613) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) (registryCreation_block_613_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_613_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registryCreation_block_613_fallthrough`. -/
def registryCreation_block_613_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (UInt256.ofNat 1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 613. -/
theorem registryCreation_block_613_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 613) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 625) (registryCreation_block_613_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 625)) r8 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_613_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 613) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 625) (registryCreation_block_613_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_613_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registryCreation_block_625_taken`. -/
def registryCreation_block_625_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `registryCreation_block_625_taken`. -/
def registryCreation_block_625_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 625. -/
theorem registryCreation_block_625_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 666) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 625) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 666) (registryCreation_block_625_taken_stack (R := R)) (registryCreation_block_625_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genMstore r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := RD.genMstore r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := RD.genMstore r18 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sload r27 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 666) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 666) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 666)) r31 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_625_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 666) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 625) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 666) (registryCreation_block_625_taken_stack (R := R)) (registryCreation_block_625_taken_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_625_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registryCreation_block_625_fallthrough`. -/
def registryCreation_block_625_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `registryCreation_block_625_fallthrough`. -/
def registryCreation_block_625_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 625. -/
theorem registryCreation_block_625_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 625) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 668) (registryCreation_block_625_fallthrough_stack (R := R)) (registryCreation_block_625_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) (M (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r10⟩ := RD.sload r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genMstore r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := RD.genMload r14 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := RD.genMstore r16 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := RD.genMstore r18 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := RD.genKeccak256 r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r28⟩ := RD.sload r27 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r29 := r28.iszero (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r30 := r29.push2 (UInt256.ofNat 666) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r31 := r30.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 668)) r31 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_625_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((UInt256.ofNat 3) + (UInt256.sub x0 x1)) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 625) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 668) (registryCreation_block_625_fallthrough_stack (R := R)) (registryCreation_block_625_fallthrough_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) (UInt256.sub x0 x1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_625_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registryCreation_block_668_taken`. -/
def registryCreation_block_668_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `registryCreation_block_668_taken`. -/
def registryCreation_block_668_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 668. -/
theorem registryCreation_block_668_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) (registryCreation_block_668_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registryCreation_block_668_taken_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 20) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1661) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_668_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) (registryCreation_block_668_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registryCreation_block_668_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_668_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registryCreation_block_668_fallthrough`. -/
def registryCreation_block_668_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `registryCreation_block_668_fallthrough`. -/
def registryCreation_block_668_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 668. -/
theorem registryCreation_block_668_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 703) (registryCreation_block_668_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registryCreation_block_668_fallthrough_memory (mem := mem)) (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 20) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := RD.genMload r4 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := RD.genMstore r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := RD.genMstore r8 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := r13.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.sub (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.gt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 703)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_668_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 703) (registryCreation_block_668_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registryCreation_block_668_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_668_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registryCreation_block_703`. -/
def registryCreation_block_703_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 703. -/
theorem registryCreation_block_703 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 703) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 710) (registryCreation_block_703_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 20) x0) k' C' := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.swap1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 20) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 710)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_703_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 703) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 710) (registryCreation_block_703_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 20) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registryCreation_block_703 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 710. -/
theorem registryCreation_block_710 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 710) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) g s0 (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256)) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256)) (((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 256) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32).readWithPadding (UInt256.ofNat 256).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMstore r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sstore r13 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := r17.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sstore r18 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 2) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := r21.dup3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.add (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  obtain ⟨_, _, r24⟩ := RD.sstore r23 hperm (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r25 := r24.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 256) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r27 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 748. -/
theorem registryCreation_block_748_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 736) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 748) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1143006342) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 736) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 736) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 736)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_748_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 736) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 748) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 736) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_748_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 748. -/
theorem registryCreation_block_748_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 748) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 760) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1143006342) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup2 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.xor (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 736) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 760)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_748_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1143006342)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 748) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 760) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_748_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 760. -/
theorem registryCreation_block_760_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 760) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 1661) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_760_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryCreationBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 760) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 1661) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_760_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 760. -/
theorem registryCreation_block_760_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 760) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 770) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have hcreationCodeSize : Tests.Pipeline.VyperRegistry.registryCreationBytecode.size = 1729 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 36) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.calldatasize (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.lt (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.or (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 770)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registryCreation_block_760_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 760) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperRegistry.registryCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 770) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registryCreation_block_760_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end registryCreationBlocks
