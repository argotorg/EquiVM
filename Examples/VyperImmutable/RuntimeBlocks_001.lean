import Reasoning.Reach
import Reasoning.Initcode
import Examples.VyperImmutable.Bytecode
import Examples.VyperImmutable.Immutables
import Examples.VyperImmutable.ImmutableCode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace immutableBlocks

set_option maxRecDepth 10000

/-- Final stack for bytecode block summary `immutable_block_0`. -/
def immutable_block_0_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R)

/-- Final memory for bytecode block summary `immutable_block_0`. -/
def immutable_block_0_memory {suffix : ByteArray} {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((Examples.VyperImmutable.immutableBytecode ++ suffix).write ((UInt256.ofNat 135) + (UInt256.shiftLeft (UInt256.land (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 3)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem immutable_block_0 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableBytecode ++ suffix).write ((UInt256.ofNat 135) + (UInt256.shiftLeft (UInt256.land (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 3)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableBytecode ++ suffix).write ((UInt256.ofNat 135) + (UInt256.shiftLeft (UInt256.land (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 3)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) (immutable_block_0_stack (ee := ee) (R := R)) (immutable_block_0_memory (suffix := suffix) (ee := ee) (mem := mem)) (M (M aw (UInt256.ofNat 30) (UInt256.ofNat 2)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 17) (C + ((51) + (memExpansionCost aw (UInt256.ofNat 30) (UInt256.ofNat 2)) + (3 + 3 * (((UInt256.ofNat 2).toNat + 31) / 32)) + (memExpansionCost (M aw (UInt256.ofNat 30) (UInt256.ofNat 2)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨0⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨1⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 224) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨2⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r4 := r3.shr (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨4⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨5⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨7⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 3), 1))) (by evm_ov)
  have r7 := r6.dup3 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨9⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r8 := r7.and (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨10⟩ : UInt256), .AND, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨11⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r10 := r9.shl (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨13⟩ : UInt256), .SHL, none)) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 135) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨14⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 135), 2))) (by evm_ov)
  have r12 := r11.add (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨17⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 30) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨18⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 30), 1))) (by evm_ov)
  have r14 := RD.genCodecopy r13 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨20⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r15 := r14.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨21⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r16 := RD.genMload r15 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨22⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r17 := r16.jump (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨23⟩ : UInt256), .JUMP, none)) hvalid (by evm_ov)
  exact RD.normalizeCounters r17 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_0_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableBytecode ++ suffix).write ((UInt256.ofNat 135) + (UInt256.shiftLeft (UInt256.land (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 3)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableBytecode ++ suffix).write ((UInt256.ofNat 135) + (UInt256.shiftLeft (UInt256.land (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) (UInt256.ofNat 3)) (UInt256.ofNat 1))).toNat mem (UInt256.ofNat 30).toNat (UInt256.ofNat 2).toNat)) (immutable_block_0_stack (ee := ee) (R := R)) (immutable_block_0_memory (suffix := suffix) (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_0 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem immutable_block_24_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1474176676)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 127) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 127) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨24⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1474176676) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨25⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1474176676), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨30⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨31⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 127) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨32⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 127), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨35⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 127)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_24_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1474176676)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 127) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 127) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_24_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 24. -/
theorem immutable_block_24_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1474176676)) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨24⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1474176676) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨25⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1474176676), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨30⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨31⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 127) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨32⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 127), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨35⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 36)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_24_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1474176676)) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 24) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_24_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 36. -/
theorem immutable_block_36_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 131) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨36⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 131) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨37⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 131), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨40⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 131)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_36_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 131) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_36_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 36. -/
theorem immutable_block_36_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 41) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨36⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 131) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨37⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 131), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨40⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 41)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_36_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 36) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 41) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_36_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Return the complete Vyper immutable suffix. -/
theorem immutable_block_41 {immWords : String → UInt256}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 41) R mem aw rdata σ k C) :
    RDret fork (Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords) g s0 σ (Examples.VyperImmutable.immutableLayout.suffixWords immWords) := by
  have hcode : Examples.VyperImmutable.immutableBytecode.size = 143 := by native_decide
  have hsize : (Examples.VyperImmutable.immutableLayout.suffixWords immWords).size = Examples.VyperImmutable.immutableLayout.size :=
    Reasoning.VyperImmutables.Layout.suffixWords_size Examples.VyperImmutable.immutableLayout immWords
  have hread : (((Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords).write (UInt256.ofNat 143).toNat mem (UInt256.ofNat 64).toNat (UInt256.ofNat 96).toNat).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 96).toNat) = (Examples.VyperImmutable.immutableLayout.suffixWords immWords) := by
    simpa [Examples.VyperImmutable.immutableLayout, hcode] using
      Reasoning.VyperImmutables.Layout.codecopy_read_suffix (layout := Examples.VyperImmutable.immutableLayout) (template := Examples.VyperImmutable.immutableBytecode)
      (mem := mem) (suffix := Examples.VyperImmutable.immutableLayout.suffixWords immWords) hsize (by decide) (UInt256.ofNat 64).toNat
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨41⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 143) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨43⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 143), 2))) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨46⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨48⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 96) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨49⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨51⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r7 := RD.genRet r6 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨53⟩ : UInt256), .RETURN, none)) (by evm_ov)
  have hraw := r7
  rw [hread] at hraw
  exact hraw

/-- Automatically generated RD summary for bytecode block at pc 54. -/
theorem immutable_block_54_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 127) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 127) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨54⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨55⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨60⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨61⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 127) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨62⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 127), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨65⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 127)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_54_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 127) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 127) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_54_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 54. -/
theorem immutable_block_54_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 66) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨54⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2376452955) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨55⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2376452955), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨60⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨61⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 127) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨62⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 127), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨65⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 66)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_54_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2376452955)) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 54) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 66) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_54_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 66. -/
theorem immutable_block_66_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 131) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 66) R mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨66⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 131) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨67⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 131), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨70⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 131)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_66_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 131) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 66) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_66_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 66. -/
theorem immutable_block_66_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 66) R mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 71) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨66⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 131) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨67⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 131), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨70⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 71)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_66_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 66) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 71) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_66_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Return the Vyper scalar immutable `OWNER`. -/
theorem immutable_block_71 {immWords : String → UInt256}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 71) R mem aw rdata σ k C) :
    RDret fork (Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords) g s0 σ (immWords "OWNER").toByteArray := by
  have hcode : Examples.VyperImmutable.immutableBytecode.size = 143 := by native_decide
  have hcopy : ((Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords).write (UInt256.ofNat 143).toNat mem (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) = ((immWords "OWNER").toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) := by
    simpa [hcode] using Examples.VyperImmutable.immutableCopyWord_OWNER immWords mem (UInt256.ofNat 64).toNat
  have hread : (((immWords "OWNER").toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) =
      (immWords "OWNER").toByteArray := by
    simpa using Reasoning.VyperImmutables.copy_word_read (immWords "OWNER") mem (UInt256.ofNat 64).toNat
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨71⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 143) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨73⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 143), 2))) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨76⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨78⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨79⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨81⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r7 := RD.genRet r6 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨83⟩ : UInt256), .RETURN, none)) (by evm_ov)
  have hraw := r7
  rw [hcopy] at hraw
  rw [hread] at hraw
  exact hraw

/-- Automatically generated RD summary for bytecode block at pc 84. -/
theorem immutable_block_84_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1597203657)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 127) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 84) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 127) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨84⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1597203657) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨85⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1597203657), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨90⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨91⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 127) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨92⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 127), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨95⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 127)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_84_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1597203657)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 127) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 84) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 127) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_84_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 84. -/
theorem immutable_block_84_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1597203657)) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 84) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨84⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 1597203657) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨85⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1597203657), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨90⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨91⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 127) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨92⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 127), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨95⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 96)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_84_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 1597203657)) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 84) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 96) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_84_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 96. -/
theorem immutable_block_96_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 131) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 96) R mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 131) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨96⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨98⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨99⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨100⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨101⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 131) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨102⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 131), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨105⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 131)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_96_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Examples.VyperImmutable.immutableBytecode ++ suffix) 0).contains (UInt256.ofNat 131) = true)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 96) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 131) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_96_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 96. -/
theorem immutable_block_96_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 96) R mem aw rdata σ k C)
    : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 106) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨96⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨98⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨99⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨100⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨101⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 131) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨102⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 131), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨105⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 106)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutable_block_96_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 96) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 106) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutable_block_96_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Vyper scalar immutable summary for block at pc 106. -/
theorem immutable_block_106 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 106) R mem aw rdata σ k C)
    : RDret fork (Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords) g s0 σ ((UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (immWords "LIMIT"))).toByteArray := by
  have hcode : Examples.VyperImmutable.immutableBytecode.size = 143 := by native_decide
  have hcopy0 : ((Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords).write (UInt256.ofNat 175).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "LIMIT").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Examples.VyperImmutable.immutableCopyWord_LIMIT immWords (mem) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableBytecode ++ Examples.VyperImmutable.immutableLayout.suffixWords immWords).write (UInt256.ofNat 175).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "LIMIT" := by
    simpa [hcode] using Examples.VyperImmutable.immutableLoad_LIMIT immWords (mem) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨106⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 175) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨108⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 175), 2))) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨111⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨112⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r5 := r4.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨113⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r6 := RD.genMload r5 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨114⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨115⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨117⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.eq (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨118⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨119⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r11 := RD.genMstore r10 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨121⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨122⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨124⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r14 := RD.genRet r13 (by append_decode(Examples.VyperImmutable.immutableBytecode, Examples.VyperImmutable.immutableLayout.suffixWords immWords, (⟨126⟩ : UInt256), .RETURN, none)) (by evm_ov)
  have hraw := r14
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  have hread : (((UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (immWords "LIMIT")).toByteArray.write 0 ((immWords "LIMIT").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) = ((UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (immWords "LIMIT"))).toByteArray := by
    simpa using Reasoning.VyperImmutables.copy_word_read ((UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (immWords "LIMIT"))) (((immWords "LIMIT").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 64).toNat
  rw [hread] at hraw
  exact hraw

/-- Automatically generated RD summary for bytecode block at pc 127. -/
theorem immutable_block_127 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 127) R mem aw rdata σ k C)
    : RDrev fork (Examples.VyperImmutable.immutableBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨127⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨128⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨129⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r3 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨130⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 131. -/
theorem immutable_block_131 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 131) R mem aw rdata σ k C)
    : RDrev fork (Examples.VyperImmutable.immutableBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨131⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨132⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨133⟩ : UInt256), .DUP1, none)) (by evm_ov)
  exact RD.genRev r3 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨134⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 135. -/
theorem immutable_block_135 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 135) R mem aw rdata σ k C)
    : RDret fork (Examples.VyperImmutable.immutableBytecode ++ suffix) g s0 σ ByteArray.empty := by
  let r0 := h
  exact r0.stop (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨135⟩ : UInt256), .STOP, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 136. -/
theorem immutable_block_136 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 136) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDret fork (Examples.VyperImmutable.immutableBytecode ++ suffix) g s0 σ ByteArray.empty := by
  let r0 := h
  have r1 := r0.xor (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨136⟩ : UInt256), .XOR, none)) (by evm_ov)
  exact r1.stop (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨137⟩ : UInt256), .STOP, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 138. -/
theorem immutable_block_138 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 138) (x0 :: R) mem aw rdata σ k C)
    : RDret fork (Examples.VyperImmutable.immutableBytecode ++ suffix) g s0 σ ByteArray.empty := by
  let r0 := h
  obtain ⟨_, _, r1⟩ := RD.sload r0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨138⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  exact r1.stop (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨139⟩ : UInt256), .STOP, none)) (by evm_ov)

/- Unsupported instruction boundary at pc 140: push32 (0x7f). No RD transition is asserted. -/

end immutableBlocks
