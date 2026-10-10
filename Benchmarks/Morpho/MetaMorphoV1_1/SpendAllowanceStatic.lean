import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_063
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! A finite allowance debit stops at SSTORE in static mode. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem spendAllowanceStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender value allowed ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨12614⟩
      (owner :: spender :: value :: allowed :: ret :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12614⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := RD.genMstore r1
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12615⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12616⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12618⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12620⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12621⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12623⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genKeccak256 r7
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12624⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.swap1
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12625⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12626⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup1
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12628⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12629⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12631⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.sub
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12632⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.and
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12633⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12634⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12635⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 32)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12636⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMstore r18
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12638⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 64)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12639⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12641⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := RD.genKeccak256 r21
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12642⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap2
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12643⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.sub
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12644⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap1
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12645⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r25.sstoreStatic hperm
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12646⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
