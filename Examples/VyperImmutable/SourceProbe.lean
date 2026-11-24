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

/-- Automatically generated RD summary for bytecode block at pc 106. -/
theorem immutable_block_106 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 106) R mem aw rdata σ k C)
    : RDret fork (Examples.VyperImmutable.immutableBytecode ++ suffix) g s0 σ (((UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32)) (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableBytecode ++ suffix).write (UInt256.ofNat 175).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat))).toByteArray.write 0 ((Examples.VyperImmutable.immutableBytecode ++ suffix).write (UInt256.ofNat 175).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 64).toNat 32).readWithPadding (UInt256.ofNat 64).toNat (UInt256.ofNat 32).toNat) := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 32) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨106⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 175) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨108⟩ : UInt256), .Push .PUSH2, some ((UInt256.ofNat 175), 2))) (by evm_ov)
  have r3 := r2.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨111⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨112⟩ : UInt256), .CODECOPY, none)) (by evm_ov)
  have r5 := r4.push0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨113⟩ : UInt256), .PUSH0, none)) (by evm_ov)
  have r6 := RD.genMload r5 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨114⟩ : UInt256), .MLOAD, none)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 4) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨115⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1))) (by evm_ov)
  have r8 := r7.calldataload (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨117⟩ : UInt256), .CALLDATALOAD, none)) (by evm_ov)
  have r9 := r8.eq (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨118⟩ : UInt256), .EQ, none)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨119⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  have r11 := RD.genMstore r10 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨121⟩ : UInt256), .MSTORE, none)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨122⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 32), 1))) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64) (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨124⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1))) (by evm_ov)
  exact RD.genRet r13 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨126⟩ : UInt256), .RETURN, none)) (by evm_ov)

end immutableBlocks
