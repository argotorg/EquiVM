import Reasoning.Reach
import Tests.Pipeline.VyperRegistry.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace registryBlocks

/-- Automatically generated RD summary for bytecode block at pc 764. -/
theorem registry_block_764_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1836080827)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 764) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1836080827) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1533)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_764_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1836080827)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 764) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_764_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 764. -/
theorem registry_block_764_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1836080827)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 764) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 776) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1836080827) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 776)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_764_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1836080827)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 764) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 776) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_764_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 776. -/
theorem registry_block_776_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 68))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 776) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.callvalue (by native_decide) (by evm_ov)
  have r5 := r4.or (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_776_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 68))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 776) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_776_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 776. -/
theorem registry_block_776_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 68))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 776) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 786) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.callvalue (by native_decide) (by evm_ov)
  have r5 := r4.or (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 786)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_776_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 68))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 776) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 786) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_776_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `registry_block_786`. -/
def registry_block_786_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 786. -/
theorem registry_block_786 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 786) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R (registry_block_786_memory (ee := ee) (mem := mem)) (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata σ (k + 4) (C + ((12) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 793)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_786_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 786) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R (registry_block_786_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_786 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_793_taken`. -/
def registry_block_793_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 793. -/
theorem registry_block_793_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_793_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_793_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_793_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_793_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_793_fallthrough`. -/
def registry_block_793_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 793. -/
theorem registry_block_793_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 805) (registry_block_793_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shr (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 805)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_793_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 793) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 805) (registry_block_793_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_793_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_805`. -/
def registry_block_805_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 816) :: R)

/-- Final memory for bytecode block summary `registry_block_805`. -/
def registry_block_805_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 805. -/
theorem registry_block_805 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1537) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 805) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1537) (registry_block_805_stack (R := R)) (registry_block_805_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 816) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1537) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1537)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_805_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1537) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 805) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1537) (registry_block_805_stack (R := R)) (registry_block_805_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_805 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 816. -/
theorem registry_block_816_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 288) mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 944) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 816) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 944) R mem (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 944) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 944)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_816_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 288) mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 944) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 816) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 944) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_816_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 816. -/
theorem registry_block_816_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 288) mem) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 816) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 825) R mem (M aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 288) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 944) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 825)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_816_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 288) mem) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 816) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 825) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_816_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 825. -/
theorem registry_block_825 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 825) R mem aw rdata σ k C)
    : RDrev fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 11) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 55361408875757840433174090861806872551137832179950313906002740907462033932288) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 43) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := RD.genMcopy r17 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r23 := r22.dup4 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.push0 (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.calldatasize (by native_decide) (by evm_ov)
  have r32 := r31.dup3 (by native_decide) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by native_decide) (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.pop (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r37 := r36.not (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r39 := r38.dup3 (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := r43.and (by native_decide) (by evm_ov)
  have r45 := r44.swap1 (by native_decide) (by evm_ov)
  have r46 := r45.pop (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.pop (by native_decide) (by evm_ov)
  have r49 := r48.dup2 (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := r50.swap1 (by native_decide) (by evm_ov)
  have r52 := r51.pop (by native_decide) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by native_decide) (by evm_ov)
  have r54 := r53.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r55 := RD.genMstore r54 (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r58 := r57.add (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 412) (by native_decide) (by evm_ov)
  exact RD.genRev r59 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `registry_block_944_taken`. -/
def registry_block_944_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) + (UInt256.ofNat 1)) :: (memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) :: R)

/-- Final memory for bytecode block summary `registry_block_944_taken`. -/
def registry_block_944_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 944. -/
theorem registry_block_944_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 944) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_944_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_944_taken_memory (ee := ee) (mem := mem) (σ := σ)) (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 19) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.lt (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_944_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 944) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_944_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_944_taken_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_944_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_944_fallthrough`. -/
def registry_block_944_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  (((memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) + (UInt256.ofNat 1)) :: (memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) :: R)

/-- Final memory for bytecode block summary `registry_block_944_fallthrough`. -/
def registry_block_944_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} : ByteArray :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 944. -/
theorem registry_block_944_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 944) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 967) (registry_block_944_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_944_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 320) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 19) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.lt (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 967)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_944_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.lt ((memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 320) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 19) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 944) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 967) (registry_block_944_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (registry_block_944_fallthrough_memory (ee := ee) (mem := mem) (σ := σ)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_944_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_967_taken`. -/
def registry_block_967_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `registry_block_967_taken`. -/
def registry_block_967_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 967. -/
theorem registry_block_967_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 15)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 967) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_967_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (registry_block_967_taken_memory (mem := mem)) (M (M (M (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 19) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sstore r17 hperm (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r24⟩ := RD.sstore r23 hperm (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sstore r28 hperm (by native_decide) (by evm_ov)
  have r30 := r29.pop (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r32⟩ := RD.sload r31 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 15) (by native_decide) (by evm_ov)
  have r34 := r33.dup2 (by native_decide) (by evm_ov)
  have r35 := r34.gt (by native_decide) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r37 := r36.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r37 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_967_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 15)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 967) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_967_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (registry_block_967_taken_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_967_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_967_fallthrough`. -/
def registry_block_967_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `registry_block_967_fallthrough`. -/
def registry_block_967_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 967. -/
theorem registry_block_967_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 15)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 967) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1021) (registry_block_967_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (registry_block_967_fallthrough_memory (mem := mem)) (M (M (M (M (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 19) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.push0 (by native_decide) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sstore r17 hperm (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r24⟩ := RD.sstore r23 hperm (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sstore r28 hperm (by native_decide) (by evm_ov)
  have r30 := r29.pop (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r32⟩ := RD.sload r31 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 15) (by native_decide) (by evm_ov)
  have r34 := r33.dup2 (by native_decide) (by evm_ov)
  have r35 := r34.gt (by native_decide) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r37 := r36.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1021)) r37 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_967_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 15)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 967) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1021) (registry_block_967_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (registry_block_967_fallthrough_memory (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 19) x0) (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (memLoad (UInt256.ofNat 256) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 1)) (memLoad (UInt256.ofNat 288) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 320) mem).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) + (UInt256.ofNat 2)) (UInt256.ofNat 1)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_967_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_1021_taken`. -/
def registry_block_1021_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 288) mem)) :: (memLoad (UInt256.ofNat 288) mem) :: ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1021. -/
theorem registry_block_1021_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 288) mem)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1021) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_1021_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))) k' C' := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by native_decide) (by evm_ov)
  have r12 := r11.pop (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 20) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.lt (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r24 := r23.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_1021_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 288) mem)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1021) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_1021_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_1021_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_1021_fallthrough`. -/
def registry_block_1021_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 288) mem)) :: (memLoad (UInt256.ofNat 288) mem) :: ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1021. -/
theorem registry_block_1021_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 288) mem)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1021) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1055) (registry_block_1021_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M (M aw (UInt256.ofNat 320) (⟨32⟩ : UInt256)) (UInt256.ofNat 288) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))) k' C' := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sstore r10 hperm (by native_decide) (by evm_ov)
  have r12 := r11.pop (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 20) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.lt (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r24 := r23.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1055)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_1021_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 288) mem)) ((sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 20) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1021) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1055) (registry_block_1021_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ ((UInt256.ofNat 3) + x0) (memLoad (UInt256.ofNat 320) mem)) (UInt256.ofNat 2) (x0 + (UInt256.ofNat 1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_1021_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1055. -/
theorem registry_block_1055 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1055) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDret fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 20) x0) (((memLoad (UInt256.ofNat 288) mem).toByteArray.write 0 mem (UInt256.ofNat 352).toNat 32).readWithPadding (UInt256.ofNat 320).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 20) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.pushConst (UInt256.ofNat 26172348187559504066660147035819207163357294089524509884755932214346360910719) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r18 := RD.genLog3 r17 (by native_decide) hperm (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  exact RD.genRet r20 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1123. -/
theorem registry_block_1123_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2439748591)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1123) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2439748591) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1533)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_1123_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2439748591)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1123) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_1123_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1123. -/
theorem registry_block_1123_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2439748591)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1123) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1135) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2439748591) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1135)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_1123_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2439748591)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1123) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1135) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_1123_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end registryBlocks
