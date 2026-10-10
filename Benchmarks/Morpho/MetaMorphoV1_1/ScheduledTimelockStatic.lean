import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_035
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Static execution stops at the deferred timelock update's first storage write. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem scheduledTimelockStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {value unused : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨6955⟩ (unused :: value :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6955⟩ :
      UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 17) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6956⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 17), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6958⟩ :
      UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6959⟩ :
      UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6960⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6962⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 192) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6964⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6966⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r9 := r8.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6967⟩ :
      UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r10 := r9.not (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6968⟩ :
      UInt256), UInt8.ofNat 25, .NOT, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r11 := r10.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6969⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6970⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6972⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 184) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6974⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6976⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r16 := r15.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6977⟩ :
      UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r17 := r16.dup5 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6978⟩ :
      UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r18 := r17.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6979⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r19 := r18.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6980⟩ :
      UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r20 := r19.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6981⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  exact r20.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨6982⟩ :
      UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
