import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_075
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Static execution stops at the approval storage write. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem approvalStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {value owner spender ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨16725⟩
      (value :: owner :: spender :: ret :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.push1 (UInt256.ofNat 32)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16725⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst
    (UInt256.ofNat 63486140976153616755203102783360879283472101686154884697241723088393386309925)
    (width := 32) (op := .PUSH32) (by decide)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16727⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32,
      some ((UInt256.ofNat
        63486140976153616755203102783360879283472101686154884697241723088393386309925), 32),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16760⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup4
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16761⟩ : UInt256), UInt8.ofNat 131, .DUP4, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16762⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := RD.genMstore r5
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16763⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16764⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16766⟩ : UInt256), UInt8.ofNat 130, .DUP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := RD.genMstore r8
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16767⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16768⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16770⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genKeccak256 r11
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16771⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup6
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16772⟩ : UInt256), UInt8.ofNat 133, .DUP6, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16773⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16774⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup3
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16775⟩ : UInt256), UInt8.ofNat 130, .DUP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16776⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup1
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16777⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16778⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16780⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genKeccak256 r20
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16781⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r21.sstoreStatic hperm
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨16782⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
