import Benchmarks.Morpho.MetaMorphoV1_1.Mutation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046

/-! Static-mode termination at cap scheduling's first storage write. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem submitCapScheduleStatic {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 ⟨9284⟩ (x0 :: x1 :: x2 :: x3 :: R)
      mem aw out σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9284⟩ :
      UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 14) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9285⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 14), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9287⟩ :
      UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r4 := r3.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9288⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9289⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9291⟩ :
      UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 184) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9292⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9294⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r9 := r8.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9295⟩ :
      UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r10 := r9.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9296⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r11 := r10.dup4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9297⟩ :
      UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 192) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9298⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9300⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r14 := r13.dup6 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9301⟩ :
      UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9302⟩ :
      UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r16 := r15.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9303⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r17 := r16.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9304⟩ :
      UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r18 := r17.dup5 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9305⟩ :
      UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  exact RD.sstoreStatic r18 hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨9306⟩ :
      UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
