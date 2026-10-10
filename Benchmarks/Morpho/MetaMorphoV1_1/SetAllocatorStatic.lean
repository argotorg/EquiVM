import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_021
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Static execution stops at the allocator update's first storage write. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem setAllocatorStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {value unused : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨3637⟩ (unused :: value :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.push1 (UInt256.ofNat 32) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3637⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat
      52857664851502003590378884884749518882999615076108930615845132697960458669453) (width := 32)
      (op := .PUSH32) (by decide) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3639⟩ :
      UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat
      52857664851502003590378884884749518882999615076108930615845132697960458669453), 32),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3672⟩ :
      UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r4 := r3.dup4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3673⟩ :
      UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r5 := r4.push0 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3674⟩ :
      UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r6 := RD.genMstore r5 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3675⟩ :
      UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 11) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3676⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 11), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.dup3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3678⟩ :
      UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r9 := RD.genMstore r8 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3679⟩ :
      UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3680⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push0 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3682⟩ :
      UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3683⟩ :
      UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 255) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3684⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.not (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3686⟩ :
      UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r15 := r14.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3687⟩ :
      UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3688⟩ :
      UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r17 := r16.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3689⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 255) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3690⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3692⟩ :
      UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r20 := r19.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3693⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r21 := r20.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3694⟩ :
      UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r22 := r21.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3695⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  exact r22.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨3696⟩ :
      UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
