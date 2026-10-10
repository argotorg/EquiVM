import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_063
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! A static transfer stops at the first balance write. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem transferStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {balance value sender recipient ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨12780⟩
      (balance :: value :: sender :: recipient :: ret :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.dup2
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12780⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst
    (UInt256.ofNat 100389287136786176327247604509743168900146139575972864366142685224231313322991)
    (width := 32) (op := .PUSH32) (by decide)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12781⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32,
      some ((UInt256.ofNat
        100389287136786176327247604509743168900146139575972864366142685224231313322991), 32),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12814⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12815⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap3
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12817⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup6
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12818⟩ : UInt256), UInt8.ofNat 133, .DUP6, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12819⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12820⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12821⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup5
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12822⟩ : UInt256), UInt8.ofNat 132, .DUP5, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12823⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.sub
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12824⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 64)
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12825⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push0
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12827⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genKeccak256 r14
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12828⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r15.sstoreStatic hperm
    (by immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨12829⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
