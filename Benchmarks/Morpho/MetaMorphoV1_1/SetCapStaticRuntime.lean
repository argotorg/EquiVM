import Benchmarks.Morpho.MetaMorphoV1_1.Mutation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_065

/-! Static-mode termination at each first packed write in the cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapTailStaticRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {a b c ret slot : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨13479⟩
      ([a, b, c, ret, slot] ++ R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  simp only [List.cons_append, List.nil_append] at rd
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13479⟩ :
      UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13480⟩ :
      UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r3 := r2.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13481⟩ :
      UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r4 := r3.swap3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13482⟩ :
      UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r5 := r4.swap4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13483⟩ :
      UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r6 := r5.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13484⟩ :
      UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 4722366482869645213695) (width := 9) (op := .PUSH9) (by
    decide) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13485⟩ :
      UInt256), UInt8.ofNat 104, .Push .PUSH9, some ((UInt256.ofNat 4722366482869645213695), 9),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 184) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13495⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 184), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13497⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r10 := r9.dup3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13498⟩ :
      UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13499⟩ :
      UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r12 := r11.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13500⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r13 := r12.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13501⟩ :
      UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r14 := r13.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13502⟩ :
      UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  exact RD.sstoreStatic r14 hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13503⟩ :
      UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)

theorem setCapClearTimeStaticRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {a b c ret slot : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨13576⟩
      ([a, b, c, ret, slot] ++ R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  simp only [List.cons_append, List.nil_append] at rd
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13576⟩ :
      UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13577⟩ :
      UInt256), UInt8.ofNat 80, .POP, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r3 := r2.dup4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13578⟩ :
      UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13579⟩ :
      UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13580⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13582⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 192) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13584⟩ :
      UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 192), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13586⟩ :
      UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r9 := r8.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13587⟩ :
      UInt256), UInt8.ofNat 3, .SUB, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r10 := r9.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13588⟩ :
      UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by
      evm_ov)
  have r11 := r10.dup5 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13589⟩ :
      UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)
  exact RD.sstoreStatic r11 hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v), (⟨13590⟩ :
      UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov)

theorem setCapQueueStaticRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {len : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨13612⟩ (len :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨13612⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨13613⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 13627) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨13615⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 13627), 2),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨13618⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.add (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨13619⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 21) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨13620⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 21), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r6 hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨13622⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds,
      immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
