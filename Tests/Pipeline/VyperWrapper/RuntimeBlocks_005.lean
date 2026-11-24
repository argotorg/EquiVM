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

/-- Final stack for bytecode block summary `wrapper_block_1136_fallthrough`. -/
def wrapper_block_1136_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1136. -/
theorem wrapper_block_1136_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1136) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1149) (wrapper_block_1136_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1136⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1137⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1138⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1139⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1140⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1142⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r7 := r6.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1143⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r8 := r7.iszero (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1144⟩ : UInt256), .ISZERO, none)) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1145⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r10 := r9.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1148⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1149)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1136_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1136) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1149) (wrapper_block_1136_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1136_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1149_taken`. -/
def wrapper_block_1149_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1149_taken`. -/
def wrapper_block_1149_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1149. -/
theorem wrapper_block_1149_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1149) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1149_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (wrapper_block_1149_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1149⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r2 := r1.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1150⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r3 := r2.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1151⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r4 := r3.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1152⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r5 := r4.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1153⟩ : UInt256), .POP, none)) (by evm_ov)
  have r6 := r5.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1154⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1155⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1156⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1158⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1159⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r11 := r10.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1161⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1162⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r13 := RD.genMstore r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1164⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r14 := r13.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1165⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r15 := RD.genMstore r14 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1166⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1167⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r17 := r16.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1169⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1170⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  have r19 := r18.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1171⟩ : UInt256), .DUP1, none)) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1172⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1173⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r22 := r21.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1175⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r23 := r22.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1176⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r24 := r23.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1177⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r25 := r24.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1178⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r26 := r25.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1179⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r27 := r26.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1180⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r28 := r27.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1181⟩ : UInt256), .GT, none)) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1182⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r30 := r29.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1185⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1149_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1149) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1149_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (wrapper_block_1149_taken_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1149_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1149_fallthrough`. -/
def wrapper_block_1149_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) :: (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) :: R)

/-- Final memory for bytecode block summary `wrapper_block_1149_fallthrough`. -/
def wrapper_block_1149_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1149. -/
theorem wrapper_block_1149_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1149) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1186) (wrapper_block_1149_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (wrapper_block_1149_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M aw (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1149⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r2 := r1.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1150⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r3 := r2.div (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1151⟩ : UInt256), .DIV, none)) (by evm_ov)
  have r4 := r3.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1152⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r5 := r4.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1153⟩ : UInt256), .POP, none)) (by evm_ov)
  have r6 := r5.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1154⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1155⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1156⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1158⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1159⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r11 := r10.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1161⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1162⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r13 := RD.genMstore r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1164⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r14 := r13.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1165⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r15 := RD.genMstore r14 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1166⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1167⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r17 := r16.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1169⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1170⟩ : UInt256), .KECCAK256, none)) (by evm_ov)
  have r19 := r18.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1171⟩ : UInt256), .DUP1, none)) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1172⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1173⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r22 := r21.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1175⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r23 := r22.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1176⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r24 := r23.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1177⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r25 := r24.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1178⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r26 := r25.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1179⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r27 := r26.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1180⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r28 := r27.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1181⟩ : UInt256), .GT, none)) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1182⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r30 := r29.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1185⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1186)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1149_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.div x1 x0).toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1149) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1186) (wrapper_block_1149_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (wrapper_block_1149_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata σ k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1149_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1186_taken`. -/
def wrapper_block_1186_taken_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1186. -/
theorem wrapper_block_1186_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1186) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1186_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1186⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1187⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1188⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1189⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1190⟩ : UInt256), .DUP2, none)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1191⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1192⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1193⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1195⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1196⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r11 := r10.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1198⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r12 := r11.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1199⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r13 := r12.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1200⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r14 := r13.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1201⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r15 := r14.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1202⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r16 := r15.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1203⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r17 := r16.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1204⟩ : UInt256), .GT, none)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1205⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r19 := r18.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1208⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1186_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1186) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1186_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1186_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1186_fallthrough`. -/
def wrapper_block_1186_fallthrough_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) :: (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) :: ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1186. -/
theorem wrapper_block_1186_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1186) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1209) (wrapper_block_1186_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1186⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1187⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1188⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1189⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1190⟩ : UInt256), .DUP2, none)) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1191⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1192⟩ : UInt256), .POP, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1193⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1195⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1196⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r11 := r10.calldataload (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1198⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r12 := r11.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1199⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r13 := r12.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1200⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r14 := r13.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1201⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r15 := r14.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1202⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r16 := r15.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1203⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r17 := r16.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1204⟩ : UInt256), .GT, none)) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1205⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r19 := r18.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1208⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1209)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1186_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.gt (UInt256.sub ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256))) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))) ((sstoreAccountMap ee.codeOwner σ x3 x0).get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 2) (⟨0⟩ : UInt256)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1186) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1209) (wrapper_block_1186_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x3 := x3) (R := R)) mem aw' rdata (sstoreAccountMap ee.codeOwner σ x3 x0) k' C' := by
  obtain ⟨k0, C0, h0⟩ := wrapper_block_1186_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1209`. -/
def wrapper_block_1209_stack {immWords : String → UInt256} {R : List UInt256} {gasWord0 : UInt256} : List UInt256 :=
  (gasWord0 :: (immWords "TOKEN") :: (⟨0⟩ : UInt256) :: (UInt256.ofNat 188) :: (UInt256.ofNat 68) :: (UInt256.ofNat 160) :: (UInt256.ofNat 32) :: (immWords "TOKEN") :: R)

/-- Final memory for bytecode block summary `wrapper_block_1209`. -/
def wrapper_block_1209_memory {immWords : String → UInt256} {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((memLoad (UInt256.ofNat 96) ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 2835717307).toByteArray.write 0 ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32)).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat 2835717307).toByteArray.write 0 ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 160).toNat 32) (UInt256.ofNat 192).toNat 32) (UInt256.ofNat 224).toNat 32)

/-- Vyper scalar immutable summary for block at pc 1209. -/
theorem wrapper_block_1209 {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1209) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1254) (wrapper_block_1209_stack (immWords := immWords) (R := R) (gasWord0 := gasWord0)) (wrapper_block_1209_memory (immWords := immWords) (ee := ee) (mem := mem)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 160) (⟨32⟩ : UInt256)) (UInt256.ofNat 192) (⟨32⟩ : UInt256)) (UInt256.ofNat 96) (⟨32⟩ : UInt256)) (UInt256.ofNat 224) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  have hcode : Tests.Pipeline.VyperWrapper.wrapperBytecode.size = 1780 := by native_decide
  have hcopy0 : ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) = ((immWords "TOKEN").toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableCopyWord_TOKEN immWords (mem) (⟨0⟩ : UInt256).toNat
  have hload0 : (memLoad (⟨0⟩ : UInt256) ((Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords).write (UInt256.ofNat 1780).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) = immWords "TOKEN" := by
    simpa [hcode] using Tests.Pipeline.VyperWrapper.immutableLoad_TOKEN immWords (mem) (⟨0⟩ : UInt256)
  try simp only [hcopy0] at hload0
  let r0 := h
  have r1 := r0.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1209⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r2 := r1.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1210⟩ : UInt256), .POP, none)) (by evm_ov)
  have r3 := r2.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1211⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r4 := r3.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1212⟩ : UInt256), .POP, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1213⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1))) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1215⟩ : UInt256), .SSTORE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1216⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1780) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1218⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1780), 2))) (by evm_ov)
  have r9 := r8.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1221⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r10 := RD.genCodecopy r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1222⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r11 := r10.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1223⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r12 := RD.genMload r11 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1224⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 2835717307) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1225⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2835717307), 4))) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1230⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r15 := RD.genMstore r14 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1232⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r16 := r15.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1233⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1234⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r18 := RD.genMstore r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1236⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1237⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r20 := RD.genMload r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1239⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1240⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r22 := RD.genMstore r21 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1242⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1243⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1245⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 68) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1247⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 68), 1))) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 188) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1249⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 188), 1))) (by evm_ov)
  have r27 := r26.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1251⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r28 := r27.dup6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1252⟩ : UInt256), .DUP6, none)) (by evm_ov)
  have r29 := RD.genGas r28 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords, (⟨1253⟩ : UInt256), .GAS, none)) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1254)) r29 (by native_decide)
  have hraw := rFinal
  try simp only [hcopy0] at hraw
  try simp only [hload0] at hraw
  simp only [wrapper_block_1209_stack, wrapper_block_1209_memory]
  exact ⟨_, _, _, hraw⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1209_packed {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1209) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (gasWord0 : UInt256) (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ Tests.Pipeline.VyperWrapper.immutableLayout.suffixWords immWords) ee g s0 (UInt256.ofNat 1254) (wrapper_block_1209_stack (immWords := immWords) (R := R) (gasWord0 := gasWord0)) (wrapper_block_1209_memory (immWords := immWords) (ee := ee) (mem := mem)) aw' rdata (sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 2) x0) k' C' := by
  obtain ⟨gasWord0, k0, C0, h0⟩ := wrapper_block_1209 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨gasWord0, _, k', C', h'⟩

/- Unsupported instruction boundary at pc 1254: call (0xf1). No RD transition is asserted. Summaries resume at pc 1255 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `wrapper_block_1255_taken`. -/
def wrapper_block_1255_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1255. -/
theorem wrapper_block_1255_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1266) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1255) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1266) (wrapper_block_1255_taken_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1266) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1255⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1266), 2))) (by evm_ov)
  have r2 := r1.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1258⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1266)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1255_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1266) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1255) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1266) (wrapper_block_1255_taken_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1255_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1255_fallthrough`. -/
def wrapper_block_1255_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1255. -/
theorem wrapper_block_1255_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1255) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1259) (wrapper_block_1255_fallthrough_stack (R := R)) mem aw rdata σ (k + 2) (C + ((13))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 1266) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1255⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1266), 2))) (by evm_ov)
  have r2 := r1.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1258⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1259)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1255_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1255) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1259) (wrapper_block_1255_fallthrough_stack (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1255_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1259. -/
theorem wrapper_block_1259 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1259) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1259⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r2 := r1.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1260⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1261⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genReturndatacopy r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1262⟩ : UInt256), .RETURNDATACOPY, none)) (by
    have hz : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by decide
    simpa only [hz] using returnDataCopyFullGuard rdata) (by evm_ov)
  have r5 := r4.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1263⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r6 := r5.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1264⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  exact RD.genRev r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1265⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Final stack for bytecode block summary `wrapper_block_1266_taken`. -/
def wrapper_block_1266_taken_stack {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1266. -/
theorem wrapper_block_1266_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) ((UInt256.ofNat 160) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1266) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1266_taken_stack (rdata := rdata) (R := R)) mem aw rdata σ (k + 17) (C + ((56))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1266⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1267⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1268⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r4 := r3.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1270⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r5 := r4.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1271⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r6 := r5.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1272⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1273⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r8 := r7.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1275⟩ : UInt256), .LT, none)) (by evm_ov)
  have r9 := r8.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1276⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r10 := r9.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1277⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1278⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1279⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r13 := r12.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1281⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1282⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r15 := r14.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1284⟩ : UInt256), .GT, none)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1285⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r17 := r16.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1288⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1266_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) ((UInt256.ofNat 160) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1266) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1266_taken_stack (rdata := rdata) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1266_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1266_fallthrough`. -/
def wrapper_block_1266_fallthrough_stack {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1266. -/
theorem wrapper_block_1266_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) ((UInt256.ofNat 160) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1266) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1289) (wrapper_block_1266_fallthrough_stack (rdata := rdata) (R := R)) mem aw rdata σ (k + 17) (C + ((56))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1266⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1267⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1268⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r4 := r3.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1270⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r5 := r4.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1271⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r6 := r5.returndatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1272⟩ : UInt256), .RETURNDATASIZE, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1273⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r8 := r7.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1275⟩ : UInt256), .LT, none)) (by evm_ov)
  have r9 := r8.mul (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1276⟩ : UInt256), .MUL, none)) (by evm_ov)
  have r10 := r9.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1277⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r11 := r10.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1278⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1279⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r13 := r12.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1281⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1282⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r15 := r14.gt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1284⟩ : UInt256), .GT, none)) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1285⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r17 := r16.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1288⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1289)) r17 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1266_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.ofNat 192) ((UInt256.ofNat 160) + (UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat 32) (UInt256.ofNat rdata.size)) (UInt256.xor (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) (UInt256.ofNat rdata.size)))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1266) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1289) (wrapper_block_1266_fallthrough_stack (rdata := rdata) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1266_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1289_taken`. -/
def wrapper_block_1289_taken_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 160) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1289. -/
theorem wrapper_block_1289_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 160) mem) (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1289) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1289_taken_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1289⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r2 := RD.genMload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1291⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1292⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1293⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1295⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1296⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1299⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1289_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 160) mem) (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1289) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) (wrapper_block_1289_taken_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1289_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1289_fallthrough`. -/
def wrapper_block_1289_fallthrough_stack {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 160) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1289. -/
theorem wrapper_block_1289_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 160) mem) (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1289) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1300) (wrapper_block_1289_fallthrough_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)) rdata σ (k + 7) (C + ((28) + (memExpansionCost aw (UInt256.ofNat 160) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1289⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r2 := RD.genMload r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1291⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r3 := r2.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1292⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1293⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 1), 1))) (by evm_ov)
  have r5 := r4.shr (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1295⟩ : UInt256), .SHR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1296⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1299⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1300)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1289_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (UInt256.ofNat 160) mem) (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1289) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1300) (wrapper_block_1289_fallthrough_stack (mem := mem) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1289_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1300_taken`. -/
def wrapper_block_1300_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `wrapper_block_1300_taken`. -/
def wrapper_block_1300_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 256) (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1300. -/
theorem wrapper_block_1300_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 128) ((memLoad (UInt256.ofNat 256) (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 128).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1435) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1300) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1435) (wrapper_block_1300_taken_stack (R := R)) (wrapper_block_1300_taken_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1300⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 256), 2))) (by evm_ov)
  have r2 := RD.genMstore r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1303⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1304⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 256) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1305⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 256), 2))) (by evm_ov)
  have r5 := r4.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1308⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r6 := r5.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1309⟩ : UInt256), .POP, none)) (by evm_ov)
  have r7 := RD.genMload r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1310⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1311⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1313⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1314⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1316⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1435) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1317⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1435), 2))) (by evm_ov)
  have r13 := r12.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1320⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1435)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1300_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 128) ((memLoad (UInt256.ofNat 256) (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 128).toNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1435) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1300) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1435) (wrapper_block_1300_taken_stack (R := R)) (wrapper_block_1300_taken_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1300_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `wrapper_block_1300_fallthrough`. -/
def wrapper_block_1300_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `wrapper_block_1300_fallthrough`. -/
def wrapper_block_1300_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((memLoad (UInt256.ofNat 256) (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 128).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1300. -/
theorem wrapper_block_1300_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 128) ((memLoad (UInt256.ofNat 256) (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 128).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1300) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1321) (wrapper_block_1300_fallthrough_stack (R := R)) (wrapper_block_1300_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((44) + (memExpansionCost aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 256) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)) (UInt256.ofNat 128) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 256) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1300⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 256), 2))) (by evm_ov)
  have r2 := RD.genMstore r1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1303⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r3 := r2.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1304⟩ : UInt256), .POP, none)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 256) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1305⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 256), 2))) (by evm_ov)
  have r5 := r4.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1308⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r6 := r5.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1309⟩ : UInt256), .POP, none)) (by evm_ov)
  have r7 := RD.genMload r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1310⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1311⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r9 := RD.genMstore r8 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1313⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 128) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1314⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 128), 1))) (by evm_ov)
  have r11 := RD.genMload r10 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1316⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 1435) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1317⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1435), 2))) (by evm_ov)
  have r13 := r12.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1320⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1321)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1300_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (memLoad (UInt256.ofNat 128) ((memLoad (UInt256.ofNat 256) (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 128).toNat 32)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1300) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1321) (wrapper_block_1300_fallthrough_stack (R := R)) (wrapper_block_1300_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1300_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1321. -/
theorem wrapper_block_1321 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1321) R mem aw rdata σ k C)
    : RDrev fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1321⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1323⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 256) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1324⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 256), 2))) (by evm_ov)
  have r4 := RD.genMstore r3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1327⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 15) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1328⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 15), 1))) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1330⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1332⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.pushConst (UInt256.ofNat 52670383448186445861358136120353180461094388504232064340117296047664696131584) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1333⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 52670383448186445861358136120353180461094388504232064340117296047664696131584), 32))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 192) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1366⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 192), 1))) (by evm_ov)
  have r10 := RD.genMstore r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1368⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1369⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r12 := r11.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1371⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 256) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1372⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 256), 2))) (by evm_ov)
  have r14 := r13.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1375⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 47) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1376⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 47), 1))) (by evm_ov)
  have r16 := r15.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1378⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r17 := r16.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1379⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r18 := RD.genMcopy r17 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1380⟩ : UInt256), .MCOPY, none)) (by evm_ov)
  have r19 := r18.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1381⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r20 := RD.genMload r19 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1382⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r21 := r20.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1383⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1384⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r23 := r22.dup4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1386⟩ : UInt256), .DUP4, none)) (by evm_ov)
  have r24 := r23.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1387⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r25 := r24.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1388⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1389⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r27 := r26.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1391⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r28 := r27.push0 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1392⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r29 := r28.sub (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1393⟩ : UInt256), .SUB, none)) (by evm_ov)
  have r30 := r29.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1394⟩ : UInt256), .AND, none)) (by evm_ov)
  have r31 := r30.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1395⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r32 := r31.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1396⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r33 := RD.genCalldatacopy r32 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1397⟩ : UInt256), .CALLDATACOPY, none)) (by evm_ov)
  have r34 := r33.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1398⟩ : UInt256), .POP, none)) (by evm_ov)
  have r35 := r34.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1399⟩ : UInt256), .POP, none)) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1400⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r37 := r36.not (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1402⟩ : UInt256), .NOT, none)) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 31) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1403⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 31), 1))) (by evm_ov)
  have r39 := r38.dup3 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1405⟩ : UInt256), .DUP3, none)) (by evm_ov)
  have r40 := RD.genMload r39 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1406⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1407⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r42 := r41.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1409⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r43 := r42.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1410⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r44 := r43.and (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1411⟩ : UInt256), .AND, none)) (by evm_ov)
  have r45 := r44.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1412⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r46 := r45.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1413⟩ : UInt256), .POP, none)) (by evm_ov)
  have r47 := r46.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1414⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r48 := r47.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1415⟩ : UInt256), .POP, none)) (by evm_ov)
  have r49 := r48.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1416⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r50 := r49.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1417⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r51 := r50.swap1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1418⟩ : UInt256), .SWAP1, none)) (by evm_ov)
  have r52 := r51.pop (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1419⟩ : UInt256), .POP, none)) (by evm_ov)
  have r53 := r52.push4 (UInt256.ofNat 147028384) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1420⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 147028384), 4))) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 224) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1425⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 224), 1))) (by evm_ov)
  have r55 := RD.genMstore r54 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1427⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r56 := r55.dup1 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1428⟩ : UInt256), .DUP1, none)) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 4) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1429⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r58 := r57.add (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1431⟩ : UInt256), .ADD, none)) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 252) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1432⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 252), 1))) (by evm_ov)
  exact RD.genRev r59 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1434⟩ : UInt256), .REVERT, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1435. -/
theorem wrapper_block_1435 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1435) R mem aw rdata σ k C)
    : RDret fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) g s0 σ (((memLoad (UInt256.ofNat 96) mem).toByteArray.write 0 mem (UInt256.ofNat 160).toNat 32).readWithPadding (UInt256.ofNat 96).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1435⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.caller (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1436⟩ : UInt256), .CALLER, none)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 67702740208004597098190646505210970707668317710481605226116601562998497336499) (width := 32) (op := .PUSH32) (by decide) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1437⟩ : UInt256), .Push .PUSH32, some ((UInt256.ofNat 67702740208004597098190646505210970707668317710481605226116601562998497336499), 32))) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1470⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  have r5 := RD.genMload r4 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1472⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1473⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r7 := RD.genMstore r6 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1475⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1476⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1478⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 160), 1))) (by evm_ov)
  have r10 := RD.genLog2 r9 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1480⟩ : UInt256), .LOG2, none)) hperm (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1481⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 96) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1483⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 96), 1))) (by evm_ov)
  exact RD.genRet r12 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1485⟩ : UInt256), .RETURN, none)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 1486. -/
theorem wrapper_block_1486_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2862286670)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1756) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1486) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1756) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1486⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2862286670) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1487⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2862286670), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1492⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1493⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1756) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1494⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1756), 2))) (by evm_ov)
  have r6 := r5.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1497⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1756)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1486_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2862286670)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1756) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1486) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1756) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1486_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1486. -/
theorem wrapper_block_1486_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2862286670)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1486) (x0 :: R) mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1498) (x0 :: R) mem aw rdata σ (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1486⟩ : UInt256), .JUMPDEST, none)) (by evm_ov)
  have r2 := r1.push4 (UInt256.ofNat 2862286670) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1487⟩ : UInt256), .Push .PUSH4, some ((UInt256.ofNat 2862286670), 4))) (by evm_ov)
  have r3 := r2.dup2 (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1492⟩ : UInt256), .DUP2, none)) (by evm_ov)
  have r4 := r3.xor (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1493⟩ : UInt256), .XOR, none)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1756) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1494⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1756), 2))) (by evm_ov)
  have r6 := r5.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1497⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1498)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1486_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.xor x0 (UInt256.ofNat 2862286670)) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1486) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1498) (x0 :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1486_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1498. -/
theorem wrapper_block_1498_taken {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1498) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1498⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1500⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1501⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1502⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1503⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1504⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1507⟩ : UInt256), .JUMPI, none)) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1760)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1498_taken_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) 0).contains (UInt256.ofNat 1760) = true)
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1498) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1760) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1498_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1498. -/
theorem wrapper_block_1498_fallthrough {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1498) R mem aw rdata σ k C)
    : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1508) R mem aw rdata σ (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 36) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1498⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 36), 1))) (by evm_ov)
  have r2 := r1.calldatasize (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1500⟩ : UInt256), .CALLDATASIZE, none)) (by evm_ov)
  have r3 := r2.lt (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1501⟩ : UInt256), .LT, none)) (by evm_ov)
  have r4 := r3.callvalue (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1502⟩ : UInt256), .CALLVALUE, none)) (by evm_ov)
  have r5 := r4.or (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1503⟩ : UInt256), .OR, none)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1760) (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1504⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 1760), 2))) (by evm_ov)
  have r7 := r6.jumpiNT (by append_decode(Tests.Pipeline.VyperWrapper.wrapperBytecode, suffix, (⟨1507⟩ : UInt256), .JUMPI, none)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1508)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem wrapper_block_1498_fallthrough_packed {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.lor ee.weiValue (UInt256.lt (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 36))) = (UInt256.ofNat 0))
    (h : RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1498) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork (Tests.Pipeline.VyperWrapper.wrapperBytecode ++ suffix) ee g s0 (UInt256.ofNat 1508) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (wrapper_block_1498_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end wrapperBlocks
