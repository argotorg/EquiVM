import Reasoning.Reach
import Tests.Pipeline.VyperRegistry.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace registryBlocks

/-- Final stack for bytecode block summary `registry_block_0`. -/
def registry_block_0_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Final memory for bytecode block summary `registry_block_0`. -/
def registry_block_0_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  (Tests.Pipeline.VyperRegistry.registryBytecode.write ((UInt256.ofNat 1665) + (UInt256.shiftLeft (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 10)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem registry_block_0 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (memLoad (⟨0⟩ : UInt256) (Tests.Pipeline.VyperRegistry.registryBytecode.write ((UInt256.ofNat 1665) + (UInt256.shiftLeft (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 10)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (memLoad (⟨0⟩ : UInt256) (Tests.Pipeline.VyperRegistry.registryBytecode.write ((UInt256.ofNat 1665) + (UInt256.shiftLeft (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 10)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) (registry_block_0_stack (ee := ee) (R := R)) (registry_block_0_memory (ee := ee) (mem := mem)) (M (M aw (UInt256.ofNat 30) (UInt256.ofNat 2)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((53) + (memExpansionCost aw (UInt256.ofNat 30) (UInt256.ofNat 2)) + (3 + 3 * (((UInt256.ofNat 2).toNat + 31) / 32)) + (memExpansionCost (M aw (UInt256.ofNat 30) (UInt256.ofNat 2)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r4 := r3.shr (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 10) (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := r7.mod (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 1665) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 30) (by native_decide) (by evm_ov)
  have r14 := RD.genCodecopy r13 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_0_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (memLoad (⟨0⟩ : UInt256) (Tests.Pipeline.VyperRegistry.registryBytecode.write ((UInt256.ofNat 1665) + (UInt256.shiftLeft (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 10)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (memLoad (⟨0⟩ : UInt256) (Tests.Pipeline.VyperRegistry.registryBytecode.write ((UInt256.ofNat 1665) + (UInt256.shiftLeft (UInt256.mod (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 10)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) (registry_block_0_stack (ee := ee) (R := R)) (registry_block_0_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_0 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem registry_block_24_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4030008324)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 256) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 256) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4030008324) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 256)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_24_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4030008324)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 256) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 256) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_24_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem registry_block_24_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4030008324)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 36) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4030008324) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 36)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_24_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4030008324)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 36) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_24_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 36. -/
theorem registry_block_36_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.callvalue (by native_decide) (by evm_ov)
  have r5 := r4.or (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_36_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_36_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 36. -/
theorem registry_block_36_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 46) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r2 := r1.calldatasize (by native_decide) (by evm_ov)
  have r3 := r2.lt (by native_decide) (by evm_ov)
  have r4 := r3.callvalue (by native_decide) (by evm_ov)
  have r5 := r4.or (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 46)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_36_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 46) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_36_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_46_taken`. -/
def registry_block_46_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 46. -/
theorem registry_block_46_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 46) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_46_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_46_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 46) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_46_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_46_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_46_fallthrough`. -/
def registry_block_46_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 46. -/
theorem registry_block_46_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 46) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 57) (registry_block_46_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.calldataload (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shr (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 57)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_46_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 46) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 57) (registry_block_46_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_46_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_57`. -/
def registry_block_57_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 68) :: R)

/-- Final memory for bytecode block summary `registry_block_57`. -/
def registry_block_57_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 57. -/
theorem registry_block_57 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1537) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 57) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1537) (registry_block_57_stack (R := R)) (registry_block_57_memory (mem := mem) (x0 := x0)) (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1537) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1537)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_57_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1537) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 57) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1537) (registry_block_57_stack (R := R)) (registry_block_57_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_57 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 68. -/
theorem registry_block_68_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 256) mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 196) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 68) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 196) R mem (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 196)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_68_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 256) mem) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 196) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 68) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 196) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_68_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 68. -/
theorem registry_block_68_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 256) mem) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 68) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 77) R mem (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) rdata σ (k + 5) (C + ((20) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 77)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_68_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 256) mem) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 68) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 77) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_68_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 77. -/
theorem registry_block_77 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 77) R mem aw rdata σ k C)
    : RDrev fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 10) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 55361408875754578380281628340133636745845274621303892621060549417795237969920) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 42) (by native_decide) (by evm_ov)
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
  have r54 := r53.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r55 := RD.genMstore r54 (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r58 := r57.add (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 380) (by native_decide) (by evm_ov)
  exact RD.genRev r59 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 196. -/
theorem registry_block_196 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 196) R mem aw rdata σ k C)
    : RDret fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 (sstoreAccountMap ee.codeOwner σ (⟨0⟩ : UInt256) (memLoad (UInt256.ofNat 256) ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 288).toNat 32))) ByteArray.empty := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sstore r8 hperm (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 63267312222310607310220992301550539520881909915348243260808268974908359596000) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r17 := RD.genLog3 r16 (by native_decide) hperm (by evm_ov)
  exact r17.stop (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 256. -/
theorem registry_block_256_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 665025254)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 256) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 665025254) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1533)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_256_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 665025254)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1533) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 256) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1533) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_256_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 256. -/
theorem registry_block_256_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 665025254)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 256) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 268) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 665025254) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.xor (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1533) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 268)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_256_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 665025254)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 256) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 268) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_256_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 268. -/
theorem registry_block_268_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 268) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_268_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 268) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_268_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 268. -/
theorem registry_block_268_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 268) R mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 273) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 273)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_268_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 268) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 273) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_268_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_273_taken`. -/
def registry_block_273_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (⟨0⟩ : UInt256) :: R)

/-- Final memory for bytecode block summary `registry_block_273_taken`. -/
def registry_block_273_taken_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 273. -/
theorem registry_block_273_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 16)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 273) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_273_taken_stack (ee := ee) (σ := σ) (R := R)) (registry_block_273_taken_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.gt (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1661)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_273_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 16)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 1661) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 273) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1661) (registry_block_273_taken_stack (ee := ee) (σ := σ) (R := R)) (registry_block_273_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_273_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `registry_block_273_fallthrough`. -/
def registry_block_273_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (⟨0⟩ : UInt256) :: R)

/-- Final memory for bytecode block summary `registry_block_273_fallthrough`. -/
def registry_block_273_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 273. -/
theorem registry_block_273_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 16)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 273) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 289) (registry_block_273_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (registry_block_273_fallthrough_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.gt (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 1661) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 289)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_273_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (UInt256.ofNat 16)) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 273) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 289) (registry_block_273_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (registry_block_273_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := registry_block_273_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 289. -/
theorem registry_block_289_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 383) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 289) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 383) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 383) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 383)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_289_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Tests.Pipeline.VyperRegistry.registryBytecode 0).contains (UInt256.ofNat 383) = true)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 289) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 383) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_289_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 289. -/
theorem registry_block_289_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 289) (x0 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  have r2 := r1.iszero (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 383) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 295)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_289_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 289) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 295) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_289_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end registryBlocks
