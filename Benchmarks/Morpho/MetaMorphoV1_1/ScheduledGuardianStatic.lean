import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_025
import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-! Static execution stops at the deferred guardian update's first storage write. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem scheduledGuardianStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {value unused : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨4458⟩ (unused :: value :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4458⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4459⟩ : UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4491) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4460⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 4491), 2),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 14) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4463⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 14), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4465⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4466⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4467⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4469⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4471⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4473⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4474⟩ : UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 160) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4475⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4477⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 15) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4478⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 15), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4480⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4481⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4482⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 15) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4483⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 15), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r18.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨4485⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
