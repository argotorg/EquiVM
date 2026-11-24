import Reasoning.Reach
import Reasoning.Initcode
import Tests.Pipeline.VyperWrapper.Bytecode
import Tests.Pipeline.VyperWrapper.Immutables
import Tests.Pipeline.VyperWrapper.ImmutableCode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace wrapperBlocks

set_option maxRecDepth 10000

/-- Automatically generated RD summary for bytecode block at pc 1508. -/
theorem wrapper_block_1508_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1527) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1508) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1527) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1508⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1510⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1527) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1511⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1527), 2))) (by evm_ov)
  have r4 := r3.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1514⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1527)) r4 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1508_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1527) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1508) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1527) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1508_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1508. -/
theorem wrapper_block_1508_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1508) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1515) R mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1508⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1510⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1527) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1511⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1527), 2))) (by evm_ov)
  have r4 := r3.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1514⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1515)) r4 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1508_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1508) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1515) R mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1508_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1515`. -/
def wrapper_block_1515_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 64) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1515`. -/
def wrapper_block_1515_memory {mem : ByteArray} : ByteArray :=
  ((⟨0⟩ : UInt256).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1515. -/
theorem wrapper_block_1515 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1637) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1515) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1637) (wrapper_block_1515_stack (R := R)) (wrapper_block_1515_memory (mem := mem)) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((25) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1515⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1516⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r3 := RD.genMstore r2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1518⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1519⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1521⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1637) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1523⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1637), 2))) (by evm_ov)
  have r7 := r6.jump (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1526⟩ : UInt256), .JUMP, none)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1637)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1515_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1637) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1515) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1637) (wrapper_block_1515_stack (R := R)) (wrapper_block_1515_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1515 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1527`. -/
def wrapper_block_1527_stack {immWords : String → UInt256} {g : Sat256} {aw : UInt256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((46) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (immWords "TOKEN") :: (UInt256.ofNat 124) :: (UInt256.ofNat 36) :: (UInt256.ofNat 96) :: (UInt256.ofNat 32) :: (immWords "TOKEN") :: R)

/-- Final memory for bytecode block summary `wrapper_block_1527`. -/
def wrapper_block_1527_memory {immWords : String → UInt256} {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat 1889567281).toByteArray.write 0 ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32)

/-- Vyper scalar immutable summary for block at pc 1527. -/
theorem wrapper_block_1527 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1527) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1559) (wrapper_block_1527_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_1527_memory (immWords := immWords) (ee := ee) (mem := mem)) (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  have hcode : Tests.Pipeline.VyperWrapper.wrapperBytecode.size = 1780 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableCopyWord_TOKEN immWords (mem) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "TOKEN" := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableLoad_TOKEN immWords (mem) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1527⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1528⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1780) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1530⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1780), 2))) (by evm_ov)
  have r4 := r3.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1533⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r5 := RD.genCodecopy r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1534⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1535⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := RD.genMload r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1536⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r8 := r7.push4 (UInt256.ofNat 1889567281) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1537⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1889567281), 4))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1542⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1544⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.address (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1545⟩ : UInt256), .ADDRESS, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1546⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r13 := RD.genMstore r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1548⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1549⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1551⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1553⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 124) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1555⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 124), 1))) (by evm_ov)
  have r18 := r17.dup5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1557⟩ : UInt256), .DUP5, none)) (by evm_ov)
  have r19 := RD.genGas (RD.normalizeCounters (k' := k + 18) (C' := C + ((46) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) r18 (by omega) (by omega)) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1558⟩ : UInt256), .GAS, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1559)) r19 (by native_decide)
  have hraw : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1559) (((g.subNat (C + ((46) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: (UInt256.ofNat 124) :: (UInt256.ofNat 36) :: (UInt256.ofNat 96) :: (UInt256.ofNat 32) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R) ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat 1889567281).toByteArray.write 0 ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 19) (C + ((48) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
    exact RD.normalizeCounters rFinal (by omega) (by omega)
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [wrapper_block_1527_stack, wrapper_block_1527_memory]
  exact hraw

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1527_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1527) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1559) (wrapper_block_1527_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_1527_memory (immWords := immWords) (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1527 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1559: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 1560 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapper_block_1560_taken`. -/
def wrapper_block_1560_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1560. -/
theorem wrapper_block_1560_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1571) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1560) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1571) (wrapper_block_1560_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1571) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1560⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1571), 2))) (by evm_ov)
  have r2 := r1.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1563⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1571)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1560_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1571) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1560) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1571) (wrapper_block_1560_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1560_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1560_fallthrough`. -/
def wrapper_block_1560_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1560. -/
theorem wrapper_block_1560_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1560) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1564) (wrapper_block_1560_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1571) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1560⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1571), 2))) (by evm_ov)
  have r2 := r1.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1563⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1564)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1560_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1560) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1564) (wrapper_block_1560_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1560_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1564. -/
theorem wrapper_block_1564 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1564) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1564⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1565⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1566⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1567⟩ : UInt256), .RETURNDATACOPY, none)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1568⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1569⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1570⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1571. -/
theorem wrapper_block_1571_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1571) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1571⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1572⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1574⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1575⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1576⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1579⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1571_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1571) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1571_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1571. -/
theorem wrapper_block_1571_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1571) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1580) R mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1571⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1572⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1574⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1575⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1576⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1579⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1580)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1571_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1571) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1580) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1571_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1580_taken`. -/
def wrapper_block_1580_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1580_taken`. -/
def wrapper_block_1580_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1580. -/
theorem wrapper_block_1580_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1580) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1580_taken_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1580_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((82) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1580⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r2 := r1.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1582⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1583⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := RD.genMload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1584⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1585⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1587⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1588⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1590⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1591⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1593⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1594⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1595⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r13 := r12.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1596⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r14 := r13.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1597⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r15 := r14.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1598⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r16 := r15.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1599⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r17 := r16.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1600⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r18 := r17.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1601⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r19 := r18.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1602⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r20 := r19.eq (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1603⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r21 := r20.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1604⟩ : UInt256), .OR, none)) (by evm_ov)
  have r22 := r21.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1605⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1606⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r24 := r23.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1609⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1580_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1580) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1580_taken_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1580_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1580_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1580_fallthrough`. -/
def wrapper_block_1580_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1580_fallthrough`. -/
def wrapper_block_1580_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1580. -/
theorem wrapper_block_1580_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1580) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1610) (wrapper_block_1580_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1580_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 24) (C + ((82) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1580⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r2 := r1.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1582⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1583⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := RD.genMload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1584⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1585⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1587⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1588⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1590⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1591⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1593⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1594⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1595⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r13 := r12.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1596⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r14 := r13.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1597⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r15 := r14.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1598⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r16 := r15.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1599⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r17 := r16.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1600⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r18 := r17.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1601⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r19 := r18.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1602⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r20 := r19.eq (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1603⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r21 := r20.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1604⟩ : UInt256), .OR, none)) (by evm_ov)
  have r22 := r21.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1605⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1606⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r24 := r23.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1609⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1610)) r24 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1580_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1580) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1610) (wrapper_block_1580_fallthrough_stack (ee := ee) (mem := mem) (R := R)) (wrapper_block_1580_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1580_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1610_taken`. -/
def wrapper_block_1610_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1610. -/
theorem wrapper_block_1610_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1610) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1610_taken_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1610⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1611⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1612⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1613⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1614⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1616⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r7 := r6.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1617⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r8 := r7.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1618⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1619⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r10 := r9.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1622⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1610_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1610) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1610_taken_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1610_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1610_fallthrough`. -/
def wrapper_block_1610_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1610. -/
theorem wrapper_block_1610_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1610) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1623) (wrapper_block_1610_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1610⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1611⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1612⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1613⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1614⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1616⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r7 := r6.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1617⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r8 := r7.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1618⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1619⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r10 := r9.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1622⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1623)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1610_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1610) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1623) (wrapper_block_1610_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1610_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1623`. -/
def wrapper_block_1623_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 96) :: (UInt256.ofNat 32) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1623`. -/
def wrapper_block_1623_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1623. -/
theorem wrapper_block_1623 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1623) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1637) (wrapper_block_1623_stack (R := R)) (wrapper_block_1623_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((33) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1623⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r2 := r1.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1624⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r3 := r2.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1625⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r4 := r3.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1626⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r5 := r4.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1627⟩ : UInt256), .POP, none)) (by evm_ov)
  have r6 := r5.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1628⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1629⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1630⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1632⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1633⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1635⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1637)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1623_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1623) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1637) (wrapper_block_1623_stack (R := R)) (wrapper_block_1623_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1623 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1637. -/
theorem wrapper_block_1637 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1637) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 σ (mem.readWithPadding x0.toNat x1.toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1637⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  exact RD.genRet r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1638⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1639. -/
theorem wrapper_block_1639_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4228666474)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1669) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1639⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4228666474) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1640⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 4228666474), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1645⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1646⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1669) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1647⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1669), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1650⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1669)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1639_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4228666474)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1669) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1639_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1639. -/
theorem wrapper_block_1639_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4228666474)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1651) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1639⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 4228666474) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1640⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 4228666474), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1645⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1646⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1669) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1647⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1669), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1650⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1651)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1639_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 4228666474)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1639) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1651) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1639_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1651. -/
theorem wrapper_block_1651_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1651) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1651⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1652⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1655⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1651_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1651) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1651_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1651. -/
theorem wrapper_block_1651_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1651) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1656) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1651⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1652⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1655⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1656)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1651_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1651) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1656) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1651_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Return the complete Vyper immutable suffix. -/
theorem wrapper_block_1656 {immWords : String → UInt256}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1656) R mem aw rdata σ k C) :
    RDret fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) g s0 σ (Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) := by
  have hcode : Tests.Pipeline.VyperWrapper.wrapperBytecode.size = 1780 := by native_decide
  have hsize : (Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).size = Tests.Pipeline.VyperWrapper.immutableLayout.size :=
    Reasoning.VyperImmutables.Layout.suffixWords_size Tests.Pipeline.VyperWrapper.immutableLayout immWords
  have hread : (((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) = (Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) := by
    simpa [Tests.Pipeline.VyperWrapper.immutableLayout, hcode] using
      Reasoning.VyperImmutables.Layout.codecopy_read_suffix (layout := Tests.Pipeline.VyperWrapper.immutableLayout) (template := Tests.Pipeline.VyperWrapper.wrapperBytecode)
      (mem := mem) (suffix := Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) hsize (by decide) (UInt256.ofNat 64).toNat
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1656⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1780) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1658⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1780), 2))) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1661⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1663⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1664⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1666⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r7 := RD.genRet r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1668⟩ : UInt256), .RETURN, none)) (by evm_ov)
  have hraw := r7
  rw [hread] at hraw
  exact hraw

/-- Automatically generated RD summary for bytecode block at pc 1669. -/
theorem wrapper_block_1669_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3464243906)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1756) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1756) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1669⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3464243906) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1670⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 3464243906), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1675⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1676⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1756) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1677⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1756), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1680⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1756)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1669_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3464243906)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1756) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1756) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1669_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1669. -/
theorem wrapper_block_1669_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3464243906)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1681) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1669⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 3464243906) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1670⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 3464243906), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1675⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1676⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1756) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1677⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1756), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1680⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1681)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1669_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 3464243906)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1669) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1681) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1669_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end wrapperBlocks
