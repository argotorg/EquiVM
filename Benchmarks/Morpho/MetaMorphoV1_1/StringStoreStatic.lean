import Benchmarks.Morpho.MetaMorphoV1_1.StringStorePrefix

/-! Metadata setters halt at their first storage write in a static call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem stringShortStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 (stringShortStorePC symbol)
      (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  change RD (immutableLayout.runtime metaMorphoV1_1Bytecode (wordsOf (immStore v)))
    I g s0 _ _ _ _ _ _ _ _ at rd
  cases symbol with
  | false =>
      let r0 := rd
      have r1 := r0.jumpdest (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2359⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r2 := r1.pop (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2360⟩ : UInt256), UInt8.ofNat 80, .POP, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r3 := r2.dup2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2361⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r4 := r3.push1 (UInt256.ofNat 1) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2362⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r5 := r4.shl (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2364⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r6 := r5.swap2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2365⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r7 := r6.push0 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2366⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r8 := r7.not (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2367⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r9 := r8.swap1 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2368⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r10 := r9.push1 (UInt256.ofNat 3) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2369⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r11 := r10.shl (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2371⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r12 := r11.shr (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2372⟩ : UInt256), UInt8.ofNat 28, .SHR, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r13 := r12.not (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2373⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r14 := r13.and (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2374⟩ : UInt256), UInt8.ofNat 22, .AND, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r15 := r14.or (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2375⟩ : UInt256), UInt8.ofNat 23, .OR, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r16 := r15.push1 (UInt256.ofNat 24) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2376⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 24), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      exact RD.sstoreStatic r16 hperm (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2378⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  | true =>
      let r0 := rd
      have r1 := r0.jumpdest (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3121⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r2 := r1.pop (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3122⟩ : UInt256), UInt8.ofNat 80, .POP, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r3 := r2.dup2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3123⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r4 := r3.push1 (UInt256.ofNat 1) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3124⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r5 := r4.shl (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3126⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r6 := r5.swap2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3127⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r7 := r6.push0 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3128⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r8 := r7.not (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3129⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r9 := r8.swap1 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3130⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r10 := r9.push1 (UInt256.ofNat 3) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3131⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r11 := r10.shl (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3133⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r12 := r11.shr (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3134⟩ : UInt256), UInt8.ofNat 28, .SHR, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r13 := r12.not (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3135⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r14 := r13.and (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3136⟩ : UInt256), UInt8.ofNat 22, .AND, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r15 := r14.or (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3137⟩ : UInt256), UInt8.ofNat 23, .OR, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r16 := r15.push1 (UInt256.ofNat 25) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3138⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 25), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      exact RD.sstoreStatic r16 hperm (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3140⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem stringDataBodyStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 11 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ((if symbol then ⟨3312⟩ else ⟨2556⟩))
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  change RD (immutableLayout.runtime metaMorphoV1_1Bytecode (wordsOf (immStore v)))
    I g s0 _ _ _ _ _ _ _ _ at rd
  cases symbol with
  | false =>
      let r0 := rd
      have r1 := r0.jumpdest (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2556⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r2 := r1.swap2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2557⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r3 := r2.swap3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2558⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r4 := r3.push1 (UInt256.ofNat 32) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2559⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r5 := r4.push1 (UInt256.ofNat 1) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2561⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r6 := r5.dup2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2563⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r7 := r6.swap3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2564⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r8 := r7.dup7 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2565⟩ : UInt256), UInt8.ofNat 134, .DUP7, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r9 := r8.dup10 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2566⟩ : UInt256), UInt8.ofNat 137, .DUP10, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r10 := r9.add (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2567⟩ : UInt256), UInt8.ofNat 1, .ADD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r11 := RD.genMload r10 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2568⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r12 := r11.dup2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2569⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      exact RD.sstoreStatic r12 hperm (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2570⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  | true =>
      let r0 := rd
      have r1 := r0.jumpdest (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3312⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r2 := r1.swap2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3313⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r3 := r2.swap3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3314⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r4 := r3.push1 (UInt256.ofNat 32) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3315⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r5 := r4.push1 (UInt256.ofNat 1) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3317⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r6 := r5.dup2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3319⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r7 := r6.swap3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3320⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r8 := r7.dup7 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3321⟩ : UInt256), UInt8.ofNat 134, .DUP7, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r9 := r8.dup10 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3322⟩ : UInt256), UInt8.ofNat 137, .DUP10, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r10 := r9.add (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3323⟩ : UInt256), UInt8.ofNat 1, .ADD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r11 := RD.genMload r10 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3324⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r12 := r11.dup2 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3325⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      exact RD.sstoreStatic r12 hperm (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3326⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem stringClearBodyStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (symbol : Bool) (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ((if symbol then ⟨3391⟩ else ⟨2635⟩))
      (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  change RD (immutableLayout.runtime metaMorphoV1_1Bytecode (wordsOf (immStore v)))
    I g s0 _ _ _ _ _ _ _ _ at rd
  cases symbol with
  | false =>
      let r0 := rd
      have r1 := r0.jumpdest (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2635⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r2 := r1.push0 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2636⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r3 := r2.dup3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2637⟩ : UInt256), UInt8.ofNat 130, .DUP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r4 := r3.dup3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2638⟩ : UInt256), UInt8.ofNat 130, .DUP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r5 := r4.add (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2639⟩ : UInt256), UInt8.ofNat 1, .ADD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r6 := r5.pushConst (stringStorageHash false) 
        (width := 32) (op := .PUSH32) (by decide) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2640⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((stringStorageHash false), 32),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r7 := r6.add (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2673⟩ : UInt256), UInt8.ofNat 1, .ADD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      exact RD.sstoreStatic r7 hperm (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨2674⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  | true =>
      let r0 := rd
      have r1 := r0.jumpdest (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3391⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r2 := r1.push0 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3392⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r3 := r2.dup3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3393⟩ : UInt256), UInt8.ofNat 130, .DUP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r4 := r3.dup3 (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3394⟩ : UInt256), UInt8.ofNat 130, .DUP3, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r5 := r4.add (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3395⟩ : UInt256), UInt8.ofNat 1, .ADD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r6 := r5.pushConst (stringStorageHash true) 
        (width := 32) (op := .PUSH32) (by decide) (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3396⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((stringStorageHash true), 32),
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      have r7 := r6.add (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3429⟩ : UInt256), UInt8.ofNat 1, .ADD, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
      exact RD.sstoreStatic r7 hperm (by
        immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
          (⟨3430⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
          immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
