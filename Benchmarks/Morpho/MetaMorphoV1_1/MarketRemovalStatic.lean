import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_029
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Static-mode failure at the market-removal path's first SSTORE. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem marketRemovalStoreStatic {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 ⟨5365⟩ (x0 :: x1 :: x2 :: x3 :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5365⟩ :
      UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push0 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5366⟩ :
      UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r3 := r2.dup5 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5367⟩ :
      UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r4 := r3.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5368⟩ :
      UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r5 := RD.genMstore r4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5369⟩ :
      UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 13) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5370⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 13), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5372⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5374⟩ :
      UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5375⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5377⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5378⟩ :
      UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5379⟩ :
      UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  obtain ⟨_, _, r13⟩ := RD.sload r12 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5380⟩ :
      UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5381⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5383⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 192) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5385⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5387⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r18 := r17.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5388⟩ :
      UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r19 := r18.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5389⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r20 := r19.swap3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5390⟩ :
      UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r21 := r20.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5391⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r22 := r21.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5392⟩ :
      UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r23 := r22.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5393⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 192) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5394⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5396⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5397⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5399⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 192) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5401⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5403⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r30 := r29.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5404⟩ :
      UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r31 := r30.not (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5405⟩ :
      UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r32 := r31.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5406⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r33 := r32.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5407⟩ :
      UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r34 := r33.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5408⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r35 := r34.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5409⟩ :
      UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r36 := r35.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5410⟩ :
      UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r37 := r36.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5411⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  exact RD.sstoreStatic r37 hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨5412⟩ :
      UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
