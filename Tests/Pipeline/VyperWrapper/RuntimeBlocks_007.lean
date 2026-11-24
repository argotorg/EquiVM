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

/-- Automatically generated RD summary for bytecode block at pc 1681. -/
theorem wrapper_block_1681_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1681) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1681⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1683⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1684⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1685⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1686⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1687⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1690⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1681_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1681) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1681_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1681. -/
theorem wrapper_block_1681_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1681) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1691) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1681⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1683⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1684⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1685⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1686⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1687⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1690⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1691)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1681_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1681) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1691) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1681_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1691_taken`. -/
def wrapper_block_1691_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1691. -/
theorem wrapper_block_1691_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1691) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1691_taken_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1691⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1693⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1694⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1695⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1697⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1698⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1701⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1691_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1691) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1691_taken_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1691_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1691_fallthrough`. -/
def wrapper_block_1691_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1691. -/
theorem wrapper_block_1691_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1691) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1702) (wrapper_block_1691_fallthrough_stack (ee := ee) (R := R)) mem aw rdata σ (k + 7) (C + ((28))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1691⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1693⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1694⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1695⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1697⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1698⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1701⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1702)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1691_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1691) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1702) (wrapper_block_1691_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1691_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1702. -/
theorem wrapper_block_1702 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1702) (x0 :: R) mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 96).toNat 32).readWithPadding (UInt256.ofNat 96).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1702⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r2 := RD.genMstore r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1704⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1705⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1707⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r5 := RD.genMload r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1709⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1710⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1712⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1713⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1714⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1715⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r11 := r10.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1717⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1718⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1719⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1720⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r15 := RD.genMstore r14 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1722⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1723⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1725⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  exact RD.genRet r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1727⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1728. -/
theorem wrapper_block_1728_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 983101241)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1756) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1728) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1756) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1728⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 983101241) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1729⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 983101241), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1734⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1735⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1756) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1736⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1756), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1739⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1756)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1728_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 983101241)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1756) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1728) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1756) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1728_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1728. -/
theorem wrapper_block_1728_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 983101241)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1728) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1740) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1728⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 983101241) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1729⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 983101241), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1734⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1735⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1756) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1736⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1756), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1739⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1740)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1728_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 983101241)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1728) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1740) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1728_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1740. -/
theorem wrapper_block_1740_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1740) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1740⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1741⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r3 := r2.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1744⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1740_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1740) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1740_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1740. -/
theorem wrapper_block_1740_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1740) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1745) R mem aw rdata σ (k + 3) (C + ((15))) := by
  let r0 := h
  have r1 := r0.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1740⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1741⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r3 := r2.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1744⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1745)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1740_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1740) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1745) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1740_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1745. -/
theorem wrapper_block_1745 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1745) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 σ (((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1745⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1747⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1748⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1750⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1751⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1753⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  exact RD.genRet r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1755⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1756. -/
theorem wrapper_block_1756 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1756) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1756⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1757⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1758⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1759⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1760. -/
theorem wrapper_block_1760 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1760⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1761⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1762⟩ : UInt256), .DUP1, none)) (by evm_ov)
  exact RD.genRev r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1763⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1764. -/
theorem wrapper_block_1764 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1764) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 σ ByteArray.empty := by
  let r0 := h
  exact r0.stop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1764⟩ : UInt256), .STOP, none)) (by evm_ov)

/- Unsupported instruction boundary at pc 1765: unsupported_d5 (0xd5). No RD transition is asserted. Summaries resume at pc 1766 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapper_block_1766`. -/
def wrapper_block_1766_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mod x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1766. -/
theorem wrapper_block_1766 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1766) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1767) (wrapper_block_1766_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((5))) := by
  let r0 := h
  have r1 := r0.mod (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1766⟩ : UInt256), .MOD, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1767)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1766_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1766) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1767) (wrapper_block_1766_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1766 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1767: unsupported_c0 (0xc0). No RD transition is asserted. Summaries resume at pc 1768 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapper_block_1768`. -/
def wrapper_block_1768_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.mod (UInt256.ofNat 6762941518709633) (UInt256.mod x0 x1)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1768. -/
theorem wrapper_block_1768 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1768) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1779) (wrapper_block_1768_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 3) (C + ((13))) := by
  let r0 := h
  have r1 := r0.mod (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1768⟩ : UInt256), .MOD, none)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 6762941518709633) (width := 8) (op := .PUSH8) (by decide) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1769⟩ : UInt256), .Push .PUSH8, some ((UInt256.ofNat 6762941518709633), 8))) (by evm_ov)
  have r3 := r2.mod (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1778⟩ : UInt256), .MOD, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1779)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1768_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1768) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1779) (wrapper_block_1768_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1768 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1779: unsupported_dc (0xdc). No RD transition is asserted. -/

end wrapperBlocks
