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

/-- Final stack for bytecode block summary `wrapper_block_649`. -/
def wrapper_block_649_stack {ee : ExecutionEnv} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.gt (memLoad (UInt256.ofNat 128) mem) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 649. -/
theorem wrapper_block_649 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 662) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 649) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (wrapper_block_649_stack (ee := ee) (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((26) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨649⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨651⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨652⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r4 := RD.genMload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨654⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r5 := r4.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨655⟩ : UInt256), .GT, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 662) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨656⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 662), 2))) (by evm_ov)
  have r7 := r6.jump (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨659⟩ : UInt256), .JUMP, none)) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 662)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_649_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 662) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 649) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (wrapper_block_649_stack (ee := ee) (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_649 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_660`. -/
def wrapper_block_660_stack {R : List UInt256} : List UInt256 :=
  ((⟨0⟩ : UInt256) :: R)

/-- Automatically generated RD summary for bytecode block at pc 660. -/
theorem wrapper_block_660 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 660) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (wrapper_block_660_stack (R := R)) mem aw rdata σ (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨660⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨661⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 662)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_660_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 660) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (wrapper_block_660_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_660 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_662_taken`. -/
def wrapper_block_662_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 662. -/
theorem wrapper_block_662_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 730) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) (wrapper_block_662_taken_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨662⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨663⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 730) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨664⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 730), 2))) (by evm_ov)
  have r4 := r3.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨667⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 730)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_662_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 730) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) (wrapper_block_662_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_662_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_662_fallthrough`. -/
def wrapper_block_662_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 662. -/
theorem wrapper_block_662_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 668) (wrapper_block_662_fallthrough_stack (R := R)) mem aw rdata σ (k + 4) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨662⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨663⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 730) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨664⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 730), 2))) (by evm_ov)
  have r4 := r3.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨667⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 668)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_662_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 662) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 668) (wrapper_block_662_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_662_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_668_taken`. -/
def wrapper_block_668_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 668. -/
theorem wrapper_block_668_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_668_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨668⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨670⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨671⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨673⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r5 := r4.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨674⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r6 := r5.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨675⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r7 := r6.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨676⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r8 := r7.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨677⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r9 := r8.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨678⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r10 := r9.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨679⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r11 := r10.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨680⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r12 := r11.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨681⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r13 := r12.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨682⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r14 := r13.eq (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨683⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r15 := r14.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨684⟩ : UInt256), .OR, none)) (by evm_ov)
  have r16 := r15.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨685⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨686⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r18 := r17.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨689⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_668_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_668_taken_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_668_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_668_fallthrough`. -/
def wrapper_block_668_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 668. -/
theorem wrapper_block_668_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 690) (wrapper_block_668_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨668⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨670⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨671⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨673⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r5 := r4.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨674⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r6 := r5.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨675⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r7 := r6.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨676⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r8 := r7.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨677⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r9 := r8.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨678⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r10 := r9.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨679⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r11 := r10.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨680⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r12 := r11.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨681⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r13 := r12.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨682⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r14 := r13.eq (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨683⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r15 := r14.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨684⟩ : UInt256), .OR, none)) (by evm_ov)
  have r16 := r15.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨685⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨686⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r18 := r17.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨689⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 690)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_668_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 668) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 690) (wrapper_block_668_fallthrough_stack (ee := ee) (σ := σ) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_668_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_690_taken`. -/
def wrapper_block_690_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 128) mem) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (memLoad (UInt256.ofNat 128) mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 690. -/
theorem wrapper_block_690_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 128) mem) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 128) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 690) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_690_taken_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((53) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨690⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨691⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨692⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨693⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨694⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r6 := RD.genMload r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨696⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨697⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨699⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨700⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r10 := r9.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨701⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r11 := r10.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨702⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r12 := r11.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨703⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r13 := r12.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨704⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r14 := r13.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨705⟩ : UInt256), .GT, none)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨706⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r16 := r15.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨709⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_690_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 128) mem) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 128) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 690) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_690_taken_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_690_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_690_fallthrough`. -/
def wrapper_block_690_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (memLoad (UInt256.ofNat 128) mem) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (memLoad (UInt256.ofNat 128) mem) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 690. -/
theorem wrapper_block_690_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 128) mem) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 128) mem)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 690) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 710) (wrapper_block_690_fallthrough_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 16) (C + ((53) + (memExpansionCost aw (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨690⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨691⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨692⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨693⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨694⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r6 := RD.genMload r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨696⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨697⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨699⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨700⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r10 := r9.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨701⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r11 := r10.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨702⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r12 := r11.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨703⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r13 := r12.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨704⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r14 := r13.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨705⟩ : UInt256), .GT, none)) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨706⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r16 := r15.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨709⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 710)) r16 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_690_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 128) mem) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (memLoad (UInt256.ofNat 128) mem)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 690) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 710) (wrapper_block_690_fallthrough_stack (ee := ee) (mem := mem) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_690_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_710_taken`. -/
def wrapper_block_710_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 710. -/
theorem wrapper_block_710_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 710) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_710_taken_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨710⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨711⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨712⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨713⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨714⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r6 := r5.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨715⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨716⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r8 := r7.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨719⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_710_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 710) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_710_taken_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_710_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_710_fallthrough`. -/
def wrapper_block_710_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 710. -/
theorem wrapper_block_710_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 710) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 720) (wrapper_block_710_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata σ (k + 8) (C + ((29))) := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨710⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨711⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨712⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨713⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨714⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r6 := r5.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨715⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨716⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r8 := r7.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨719⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 720)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_710_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero x0) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 710) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 720) (wrapper_block_710_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_710_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_720`. -/
def wrapper_block_720_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `wrapper_block_720`. -/
def wrapper_block_720_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 720. -/
theorem wrapper_block_720 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 720) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) (wrapper_block_720_stack (R := R)) (wrapper_block_720_memory (mem := mem) (x0 := x0) (x1 := x1)) (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ (k + 9) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨720⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r2 := r1.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨721⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r3 := r2.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨722⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r4 := r3.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨723⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r5 := r4.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨724⟩ : UInt256), .POP, none)) (by evm_ov)
  have r6 := r5.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨725⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨726⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨727⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨729⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 730)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_720_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 720) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) (wrapper_block_720_stack (R := R)) (wrapper_block_720_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_720 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_730_taken`. -/
def wrapper_block_730_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) :: (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_730_taken`. -/
def wrapper_block_730_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 730. -/
theorem wrapper_block_730_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_730_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (wrapper_block_730_taken_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨730⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨731⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r3 := r2.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨733⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨734⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r5 := RD.genMstore r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨736⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨737⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨738⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨739⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r9 := r8.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨741⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨742⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨743⟩ : UInt256), .DUP1, none)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨744⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨745⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r14 := RD.genMload r13 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨747⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r15 := r14.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨748⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r16 := r15.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨749⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r17 := r16.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨750⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r18 := r17.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨751⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r19 := r18.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨752⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r20 := r19.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨753⟩ : UInt256), .LT, none)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨754⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r22 := r21.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨757⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_730_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_730_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (wrapper_block_730_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_730_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_730_fallthrough`. -/
def wrapper_block_730_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) :: (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_730_fallthrough`. -/
def wrapper_block_730_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 730. -/
theorem wrapper_block_730_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 758) (wrapper_block_730_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (wrapper_block_730_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨730⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨731⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r3 := r2.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨733⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨734⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r5 := RD.genMstore r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨736⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨737⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨738⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨739⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r9 := r8.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨741⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨742⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨743⟩ : UInt256), .DUP1, none)) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨744⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨745⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r14 := RD.genMload r13 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨747⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r15 := r14.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨748⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r16 := r15.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨749⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r17 := r16.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨750⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r18 := r17.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨751⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r19 := r18.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨752⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r20 := r19.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨753⟩ : UInt256), .LT, none)) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨754⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r22 := r21.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨757⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 758)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_730_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.lt ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 730) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 758) (wrapper_block_730_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (wrapper_block_730_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_730_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_758_taken`. -/
def wrapper_block_758_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) :: (memLoad (UInt256.ofNat 96) mem) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 758. -/
theorem wrapper_block_758_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 758) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_758_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨758⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨759⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨760⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨761⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨762⟩ : UInt256), .DUP2, none)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨763⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨764⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨765⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨767⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨768⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨770⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨771⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r13 := r12.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨772⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r14 := r13.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨773⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r15 := r14.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨774⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r16 := r15.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨775⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r17 := r16.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨776⟩ : UInt256), .LT, none)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨777⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r19 := r18.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨780⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_758_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 758) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_758_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_758_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_758_fallthrough`. -/
def wrapper_block_758_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) :: (memLoad (UInt256.ofNat 96) mem) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 758. -/
theorem wrapper_block_758_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 758) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 781) (wrapper_block_758_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨758⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨759⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨760⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨761⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨762⟩ : UInt256), .DUP2, none)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨763⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨764⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨765⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨767⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨768⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨770⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨771⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r13 := r12.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨772⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r14 := r13.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨773⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r15 := r14.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨774⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r16 := r15.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨775⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r17 := r16.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨776⟩ : UInt256), .LT, none)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨777⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r19 := r18.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨780⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 781)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_758_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.lt (((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) + (memLoad (UInt256.ofNat 96) mem)) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 758) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 781) (wrapper_block_758_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_758_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_781_taken`. -/
def wrapper_block_781_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 781. -/
theorem wrapper_block_781_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 846) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 781) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 846) (wrapper_block_781_taken_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨781⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨782⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨783⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨784⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨785⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨787⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨788⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨789⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r9 := r8.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨790⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 846) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨791⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 846), 2))) (by evm_ov)
  have r11 := r10.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨794⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 846)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_781_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 846) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 781) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 846) (wrapper_block_781_taken_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_781_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_781_fallthrough`. -/
def wrapper_block_781_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 781. -/
theorem wrapper_block_781_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 781) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 795) (wrapper_block_781_fallthrough_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨781⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨782⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨783⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨784⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨785⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨787⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨788⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨789⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r9 := r8.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨790⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 846) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨791⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 846), 2))) (by evm_ov)
  have r11 := r10.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨794⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 795)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_781_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero ((sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 781) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 795) (wrapper_block_781_fallthrough_stack (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_781_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_795_taken`. -/
def wrapper_block_795_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `wrapper_block_795_taken`. -/
def wrapper_block_795_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 2721273594).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 2721273594).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 224).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 795. -/
theorem wrapper_block_795_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 795) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_795_taken_stack (ee := ee) (σ := σ) (R := R)) (wrapper_block_795_taken_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨795⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨796⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 2721273594) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨797⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2721273594), 4))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨802⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := RD.genMstore r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨804⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r6 := r5.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨805⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨806⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r8 := RD.genMstore r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨808⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨809⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨811⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨812⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r12 := RD.genMstore r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨814⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r13 := r12.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨815⟩ : UInt256), .DUP1, none)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := r13.extcodesize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨816⟩ : UInt256), .EXTCODESIZE, none)) (by evm_ov)
  have r15 := r14.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨817⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨818⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r17 := r16.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨821⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_795_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 795) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_795_taken_stack (ee := ee) (σ := σ) (R := R)) (wrapper_block_795_taken_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_795_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_795_fallthrough`. -/
def wrapper_block_795_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))) :: R)

/-- Final memory for bytecode block summary `wrapper_block_795_fallthrough`. -/
def wrapper_block_795_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 2721273594).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 2721273594).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 224).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 795. -/
theorem wrapper_block_795_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 795) R mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 822) (wrapper_block_795_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (wrapper_block_795_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨795⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨796⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 2721273594) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨797⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2721273594), 4))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨802⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := RD.genMstore r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨804⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r6 := r5.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨805⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨806⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r8 := RD.genMstore r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨808⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨809⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMload r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨811⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨812⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r12 := RD.genMstore r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨814⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r13 := r12.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨815⟩ : UInt256), .DUP1, none)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := r13.extcodesize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨816⟩ : UInt256), .EXTCODESIZE, none)) (by evm_ov)
  have r15 := r14.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨817⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨818⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r17 := r16.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨821⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 822)) r17 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_795_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (extCodeSizeWord σ (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (⟨0⟩ : UInt256) (⟨0⟩ : UInt256))))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 795) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 822) (wrapper_block_795_fallthrough_stack (ee := ee) (σ := σ) (R := R)) (wrapper_block_795_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_795_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_822`. -/
def wrapper_block_822_stack {g : Sat256} {C : ℕ} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((16)) + 2)).toUInt256) :: x0 :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 188) :: (UInt256.ofNat 68) :: (UInt256.ofNat 160) :: (⟨0⟩ : UInt256) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 822. -/
theorem wrapper_block_822 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 822) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 832) (wrapper_block_822_stack (g := g) (C := C) (x0 := x0) (R := R)) mem aw rdata σ (k + 7) (C + ((18))) := by
  let r0 := h
  have r1 := r0.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨822⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨823⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 68) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨825⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 68), 1))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 188) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨827⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 188), 1))) (by evm_ov)
  have r5 := r4.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨829⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r6 := r5.dup6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨830⟩ : UInt256), .DUP6, none)) (by evm_ov)
  have r7 := RD.genGas (RD.normalizeCounters (k' := k + 6) (C' := C + ((16))) r6 (by omega) (by omega)) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨831⟩ : UInt256), .GAS, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 832)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_822_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 822) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 832) (wrapper_block_822_stack (g := g) (C := C) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_822 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 832: call (0xf1). No RD transition is asserted. Summaries resume at pc 833 from a fresh symbolic RD state. -/

end wrapperBlocks
