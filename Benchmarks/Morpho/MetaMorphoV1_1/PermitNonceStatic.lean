import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_012
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Static permit execution halts at the first nonce storage write. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem permitNonceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sigV owner spender value deadline : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨1648⟩
      (sigV :: owner :: spender :: value :: deadline :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.push2 (UInt256.ofNat 1831) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1648⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1831), 2),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1840) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1651⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 1840), 2),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1654⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1655⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1657⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1658⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1660⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1661⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1662⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1663⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap7 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1664⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup8 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1665⟩ : UInt256), UInt8.ofNat 135, .DUP8, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push0 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1666⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genMstore r13 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1667⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 7) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1668⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 7), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1670⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1672⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1673⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push0 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1675⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genKeccak256 r19 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1676⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1677⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1678⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sload r22 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1679⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1680⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1681⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.dup4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1683⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.add (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1684⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1685⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  exact r28.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1686⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
