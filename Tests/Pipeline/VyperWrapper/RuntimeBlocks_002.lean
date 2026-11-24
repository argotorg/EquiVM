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

/-- Automatically generated RD summary for bytecode block at pc 235. -/
theorem wrapper_block_235_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 354) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 235) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 354) R mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨235⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨237⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 354) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨238⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 354), 2))) (by evm_ov)
  have r4 := r3.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨241⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 354)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_235_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 354) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 235) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 354) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_235_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 235. -/
theorem wrapper_block_235_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 235) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 242) R mem aw rdata σ (k + 4) (C + ((19))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨235⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r2 := r1.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨237⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 354) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨238⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 354), 2))) (by evm_ov)
  have r4 := r3.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨241⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 242)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_235_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 235) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 242) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_235_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 242. -/
theorem wrapper_block_242 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 242) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨242⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨244⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨245⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨247⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨248⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨250⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨252⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 55361408872338730376826245360984840096503137140949627140895121035363906224128) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨253⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 55361408872338730376826245360984840096503137140949627140895121035363906224128), 32))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨286⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨288⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨289⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r12 := r11.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨291⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨292⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r14 := r13.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨294⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨295⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r16 := r15.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨297⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r17 := r16.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨298⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r18 := RD.genMcopy r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨299⟩ : UInt256), .MCOPY, none)) (by evm_ov)
  have r19 := r18.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨300⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r20 := RD.genMload r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨301⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r21 := r20.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨302⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨303⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r23 := r22.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨305⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r24 := r23.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨306⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r25 := r24.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨307⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨308⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r27 := r26.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨310⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r28 := r27.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨311⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r29 := r28.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨312⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r30 := r29.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨313⟩ : UInt256), .AND, none)) (by evm_ov)
  have r31 := r30.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨314⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r32 := r31.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨315⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨316⟩ : UInt256), .CALLDATACOPY, none)) (by evm_ov)
  have r34 := r33.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨317⟩ : UInt256), .POP, none)) (by evm_ov)
  have r35 := r34.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨318⟩ : UInt256), .POP, none)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨319⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r37 := r36.not (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨321⟩ : UInt256), .NOT, none)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨322⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r39 := r38.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨324⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r40 := RD.genMload r39 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨325⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨326⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r42 := r41.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨328⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r43 := r42.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨329⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r44 := r43.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨330⟩ : UInt256), .AND, none)) (by evm_ov)
  have r45 := r44.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨331⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r46 := r45.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨332⟩ : UInt256), .POP, none)) (by evm_ov)
  have r47 := r46.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨333⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r48 := r47.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨334⟩ : UInt256), .POP, none)) (by evm_ov)
  have r49 := r48.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨335⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r50 := r49.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨336⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r51 := r50.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨337⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r52 := r51.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨338⟩ : UInt256), .POP, none)) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨339⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 147028384), 4))) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨344⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r55 := RD.genMstore r54 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨346⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r56 := r55.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨347⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨348⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r58 := r57.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨350⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 156) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨351⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 156), 1))) (by evm_ov)
  exact RD.genRev r59 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨353⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `wrapper_block_354`. -/
def wrapper_block_354_stack {immWords : String → UInt256} {g : Sat256} {aw : UInt256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((68) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (immWords "TOKEN") :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 124) :: (UInt256.ofNat 100) :: (UInt256.ofNat 96) :: (UInt256.ofNat 32) :: (immWords "TOKEN") :: R)

/-- Final memory for bytecode block summary `wrapper_block_354`. -/
def wrapper_block_354_memory {immWords : String → UInt256} {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 599290589).toByteArray.write 0 ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)

/-- Vyper scalar immutable summary for block at pc 354. -/
theorem wrapper_block_354 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 354) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 397) (wrapper_block_354_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_354_memory (immWords := immWords) (ee := ee) (mem := mem)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 27) (C + ((70) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) := by
  have hcode : Tests.Pipeline.VyperWrapper.wrapperBytecode.size = 1780 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableCopyWord_TOKEN immWords (mem) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "TOKEN" := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableLoad_TOKEN immWords (mem) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨354⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨355⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1780) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨357⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1780), 2))) (by evm_ov)
  have r4 := r3.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨360⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r5 := RD.genCodecopy r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨361⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨362⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r7 := RD.genMload r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨363⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r8 := r7.push4 (UInt256.ofNat 599290589) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨364⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 599290589), 4))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨369⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨371⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨372⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨373⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r13 := RD.genMstore r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨375⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r14 := r13.address (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨376⟩ : UInt256), .ADDRESS, none)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨377⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r16 := RD.genMstore r15 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨379⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨380⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r18 := r17.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨382⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨383⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r20 := RD.genMstore r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨385⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨386⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨388⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 100) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨390⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 100), 1))) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 124) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨392⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 124), 1))) (by evm_ov)
  have r25 := r24.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨394⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r26 := r25.dup6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨395⟩ : UInt256), .DUP6, none)) (by evm_ov)
  have r27 := RD.genGas (RD.normalizeCounters (k' := k + 26) (C' := C + ((68) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) r26 (by omega) (by omega)) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨396⟩ : UInt256), .GAS, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 397)) r27 (by native_decide)
  have hraw : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 397) (((g.subNat (C + ((68) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 124) :: (UInt256.ofNat 100) :: (UInt256.ofNat 96) :: (UInt256.ofNat 32) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R) ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 599290589).toByteArray.write 0 ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 128).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 27) (C + ((70) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) := by
    exact RD.normalizeCounters rFinal (by omega) (by omega)
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [wrapper_block_354_stack, wrapper_block_354_memory]
  exact hraw

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_354_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 354) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 397) (wrapper_block_354_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_354_memory (immWords := immWords) (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_354 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 397: call (0xf1). No RD transition is asserted. Summaries resume at pc 398 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapper_block_398_taken`. -/
def wrapper_block_398_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 398. -/
theorem wrapper_block_398_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 409) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 398) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 409) (wrapper_block_398_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 409) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨398⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 409), 2))) (by evm_ov)
  have r2 := r1.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨401⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 409)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_398_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 409) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 398) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 409) (wrapper_block_398_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_398_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_398_fallthrough`. -/
def wrapper_block_398_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 398. -/
theorem wrapper_block_398_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 398) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 402) (wrapper_block_398_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 409) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨398⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 409), 2))) (by evm_ov)
  have r2 := r1.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨401⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 402)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_398_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 398) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 402) (wrapper_block_398_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_398_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 402. -/
theorem wrapper_block_402 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 402) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨402⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨403⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨404⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨405⟩ : UInt256), .RETURNDATACOPY, none)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨406⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨407⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨408⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `wrapper_block_409_taken`. -/
def wrapper_block_409_taken_stack {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 409. -/
theorem wrapper_block_409_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 128) ((UInt256.ofNat 96) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 409) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_409_taken_stack (rdata := rdata) (R := R)) mem aw rdata σ (k + 17) (C + ((56))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨409⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨410⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨411⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r4 := r3.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨413⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r5 := r4.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨414⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r6 := r5.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨415⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨416⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r8 := r7.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨418⟩ : UInt256), .LT, none)) (by evm_ov)
  have r9 := r8.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨419⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r10 := r9.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨420⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨421⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨422⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r13 := r12.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨424⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨425⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r15 := r14.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨427⟩ : UInt256), .GT, none)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨428⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r17 := r16.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨431⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_409_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 128) ((UInt256.ofNat 96) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 409) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_409_taken_stack (rdata := rdata) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_409_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_409_fallthrough`. -/
def wrapper_block_409_fallthrough_stack {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 409. -/
theorem wrapper_block_409_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 128) ((UInt256.ofNat 96) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 409) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 432) (wrapper_block_409_fallthrough_stack (rdata := rdata) (R := R)) mem aw rdata σ (k + 17) (C + ((56))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨409⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨410⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨411⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r4 := r3.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨413⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r5 := r4.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨414⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r6 := r5.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨415⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨416⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r8 := r7.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨418⟩ : UInt256), .LT, none)) (by evm_ov)
  have r9 := r8.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨419⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r10 := r9.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨420⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨421⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨422⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r13 := r12.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨424⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨425⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r15 := r14.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨427⟩ : UInt256), .GT, none)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨428⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r17 := r16.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨431⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 432)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_409_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 128) ((UInt256.ofNat 96) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 409) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 432) (wrapper_block_409_fallthrough_stack (rdata := rdata) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_409_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_432_taken`. -/
def wrapper_block_432_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 96) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 432. -/
theorem wrapper_block_432_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 96) mem) (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 432) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_432_taken_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨432⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r2 := RD.genMload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨434⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨435⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨436⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨438⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨439⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨442⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_432_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 96) mem) (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 432) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_432_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_432_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_432_fallthrough`. -/
def wrapper_block_432_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 96) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 432. -/
theorem wrapper_block_432_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 96) mem) (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 432) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 443) (wrapper_block_432_fallthrough_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨432⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r2 := RD.genMload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨434⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨435⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨436⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨438⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨439⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨442⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 443)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_432_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 96) mem) (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 432) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 443) (wrapper_block_432_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_432_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_443_taken`. -/
def wrapper_block_443_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `wrapper_block_443_taken`. -/
def wrapper_block_443_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 224) (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 443. -/
theorem wrapper_block_443_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 224) (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32) (UInt256.ofNat 64).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 574) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 574) (wrapper_block_443_taken_stack (R := R)) (wrapper_block_443_taken_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨443⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r2 := RD.genMstore r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨445⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨446⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨447⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r5 := r4.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨449⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r6 := r5.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨450⟩ : UInt256), .POP, none)) (by evm_ov)
  have r7 := RD.genMload r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨451⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨452⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨454⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨455⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨457⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 574) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨458⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 574), 2))) (by evm_ov)
  have r13 := r12.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨461⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 574)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_443_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 224) (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32) (UInt256.ofNat 64).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 574) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 574) (wrapper_block_443_taken_stack (R := R)) (wrapper_block_443_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_443_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_443_fallthrough`. -/
def wrapper_block_443_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `wrapper_block_443_fallthrough`. -/
def wrapper_block_443_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 224) (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32) (UInt256.ofNat 64).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 443. -/
theorem wrapper_block_443_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 224) (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32) (UInt256.ofNat 64).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 462) (wrapper_block_443_fallthrough_stack (R := R)) (wrapper_block_443_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨443⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r2 := RD.genMstore r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨445⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨446⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨447⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r5 := r4.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨449⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r6 := r5.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨450⟩ : UInt256), .POP, none)) (by evm_ov)
  have r7 := RD.genMload r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨451⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨452⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨454⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨455⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨457⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 574) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨458⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 574), 2))) (by evm_ov)
  have r13 := r12.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨461⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 462)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_443_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 64) ((memLoad (UInt256.ofNat 224) (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 224).toNat 32) (UInt256.ofNat 64).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 443) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 462) (wrapper_block_443_fallthrough_stack (R := R)) (wrapper_block_443_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_443_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 462. -/
theorem wrapper_block_462 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 462) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨462⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨464⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨465⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨467⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 15) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨468⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 15), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨470⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨472⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 52670383448186445861358136120353180461094388504232064340117296047664696131584) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨473⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 52670383448186445861358136120353180461094388504232064340117296047664696131584), 32))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨506⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨508⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨509⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r12 := r11.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨511⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨512⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r14 := r13.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨514⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 47) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨515⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 47), 1))) (by evm_ov)
  have r16 := r15.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨517⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r17 := r16.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨518⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r18 := RD.genMcopy r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨519⟩ : UInt256), .MCOPY, none)) (by evm_ov)
  have r19 := r18.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨520⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r20 := RD.genMload r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨521⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r21 := r20.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨522⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨523⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r23 := r22.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨525⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r24 := r23.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨526⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r25 := r24.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨527⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨528⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r27 := r26.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨530⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r28 := r27.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨531⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r29 := r28.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨532⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r30 := r29.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨533⟩ : UInt256), .AND, none)) (by evm_ov)
  have r31 := r30.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨534⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r32 := r31.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨535⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨536⟩ : UInt256), .CALLDATACOPY, none)) (by evm_ov)
  have r34 := r33.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨537⟩ : UInt256), .POP, none)) (by evm_ov)
  have r35 := r34.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨538⟩ : UInt256), .POP, none)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨539⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r37 := r36.not (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨541⟩ : UInt256), .NOT, none)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨542⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r39 := r38.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨544⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r40 := RD.genMload r39 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨545⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨546⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r42 := r41.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨548⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r43 := r42.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨549⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r44 := r43.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨550⟩ : UInt256), .AND, none)) (by evm_ov)
  have r45 := r44.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨551⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r46 := r45.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨552⟩ : UInt256), .POP, none)) (by evm_ov)
  have r47 := r46.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨553⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r48 := r47.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨554⟩ : UInt256), .POP, none)) (by evm_ov)
  have r49 := r48.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨555⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r50 := r49.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨556⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r51 := r50.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨557⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r52 := r51.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨558⟩ : UInt256), .POP, none)) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨559⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 147028384), 4))) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨564⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r55 := RD.genMstore r54 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨566⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r56 := r55.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨567⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨568⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r58 := r57.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨570⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 188) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨571⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 188), 1))) (by evm_ov)
  exact RD.genRev r59 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨573⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `wrapper_block_574`. -/
def wrapper_block_574_stack {immWords : String → UInt256} {g : Sat256} {aw : UInt256} {C : ℕ} {R : List UInt256} : List UInt256 :=
  (((g.subNat (C + ((58) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (immWords "TOKEN") :: (UInt256.ofNat 188) :: (UInt256.ofNat 36) :: (UInt256.ofNat 160) :: (UInt256.ofNat 32) :: (immWords "TOKEN") :: R)

/-- Final memory for bytecode block summary `wrapper_block_574`. -/
def wrapper_block_574_memory {immWords : String → UInt256} {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat 1889567281).toByteArray.write 0 ((immWords "TOKEN").toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)

/-- Vyper scalar immutable summary for block at pc 574. -/
theorem wrapper_block_574 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 574) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 612) (wrapper_block_574_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_574_memory (immWords := immWords) (ee := ee) (mem := mem)) (M (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((60) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) := by
  have hcode : Tests.Pipeline.VyperWrapper.wrapperBytecode.size = 1780 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "TOKEN").toByteArray.write 0 ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableCopyWord_TOKEN immWords (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "TOKEN" := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableLoad_TOKEN immWords (((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨574⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨575⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r3 := r2.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨577⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨578⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r5 := RD.genMstore r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨580⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨581⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 1780) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨583⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1780), 2))) (by evm_ov)
  have r8 := r7.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨586⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r9 := RD.genCodecopy r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨587⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r10 := r9.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨588⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨589⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.push4 (UInt256.ofNat 1889567281) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨590⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 1889567281), 4))) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨595⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r14 := RD.genMstore r13 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨597⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r15 := r14.address (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨598⟩ : UInt256), .ADDRESS, none)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨599⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r17 := RD.genMstore r16 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨601⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨602⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨604⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨606⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 188) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨608⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 188), 1))) (by evm_ov)
  have r22 := r21.dup5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨610⟩ : UInt256), .DUP5, none)) (by evm_ov)
  have r23 := RD.genGas (RD.normalizeCounters (k' := k + 22) (C' := C + ((58) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) r22 (by omega) (by omega)) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨611⟩ : UInt256), .GAS, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 612)) r23 (by native_decide)
  have hraw : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 612) (((g.subNat (C + ((58) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256))) + 2)).toUInt256) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: (UInt256.ofNat 188) :: (UInt256.ofNat 36) :: (UInt256.ofNat 160) :: (UInt256.ofNat 32) :: (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R) ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat 1889567281).toByteArray.write 0 ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat ((uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (M (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) rdata σ (k + 23) (C + ((60) + (memExpansionCost aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)))) := by
    exact RD.normalizeCounters rFinal (by omega) (by omega)
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [wrapper_block_574_stack, wrapper_block_574_memory]
  exact hraw

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_574_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 574) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 612) (wrapper_block_574_stack (immWords := immWords) (g := g) (aw := aw) (C := C) (R := R)) (wrapper_block_574_memory (immWords := immWords) (ee := ee) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_574 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 612: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 613 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapper_block_613_taken`. -/
def wrapper_block_613_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 613. -/
theorem wrapper_block_613_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 624) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 613) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 624) (wrapper_block_613_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 624) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨613⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 624), 2))) (by evm_ov)
  have r2 := r1.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨616⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 624)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_613_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 624) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 613) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 624) (wrapper_block_613_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_613_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_613_fallthrough`. -/
def wrapper_block_613_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 613. -/
theorem wrapper_block_613_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 613) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 617) (wrapper_block_613_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 624) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨613⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 624), 2))) (by evm_ov)
  have r2 := r1.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨616⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 617)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_613_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 613) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 617) (wrapper_block_613_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_613_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 617. -/
theorem wrapper_block_617 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 617) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨617⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨618⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨619⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨620⟩ : UInt256), .RETURNDATACOPY, none)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨621⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨622⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨623⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 624. -/
theorem wrapper_block_624_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨624⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨625⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨627⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨628⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨629⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨632⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_624_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_624_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 624. -/
theorem wrapper_block_624_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 633) R mem aw rdata σ (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨624⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨625⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r3 := r2.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨627⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r4 := r3.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨628⟩ : UInt256), .LT, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨629⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨632⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 633)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_624_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 624) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 633) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_624_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_633_taken`. -/
def wrapper_block_633_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `wrapper_block_633_taken`. -/
def wrapper_block_633_taken_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 160) mem).toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 633. -/
theorem wrapper_block_633_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 660) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 633) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 660) (wrapper_block_633_taken_stack (R := R)) (wrapper_block_633_taken_memory (mem := mem)) (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨633⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r2 := r1.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨635⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨636⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := RD.genMload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨637⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨638⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨640⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨641⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨643⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r9 := r8.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨644⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 660) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨645⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 660), 2))) (by evm_ov)
  have r11 := r10.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨648⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 660)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_633_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 660) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 633) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 660) (wrapper_block_633_taken_stack (R := R)) (wrapper_block_633_taken_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_633_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_633_fallthrough`. -/
def wrapper_block_633_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `wrapper_block_633_fallthrough`. -/
def wrapper_block_633_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 160) mem).toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 633. -/
theorem wrapper_block_633_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 633) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 649) (wrapper_block_633_fallthrough_stack (R := R)) (wrapper_block_633_fallthrough_memory (mem := mem)) (M (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨633⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r2 := r1.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨635⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨636⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := RD.genMload r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨637⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨638⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r6 := RD.genMstore r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨640⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨641⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨643⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r9 := r8.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨644⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 660) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨645⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 660), 2))) (by evm_ov)
  have r11 := r10.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨648⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 649)) r11 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_633_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 633) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 649) (wrapper_block_633_fallthrough_stack (R := R)) (wrapper_block_633_fallthrough_memory (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_633_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end wrapperBlocks
