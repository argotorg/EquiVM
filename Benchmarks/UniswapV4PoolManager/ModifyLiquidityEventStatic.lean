import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem modifyLiquidityEventStatic {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (immutableLayout.runtime poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 6084) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C) :
    RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6084⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pushConst (UInt256.ofNat 340282366920938463463374607431768211455) (width := 16) (op := .PUSH16) (by decide) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6085⟩ : UInt256), UInt8.ofNat 111, .Push .PUSH16, some ((UInt256.ofNat 340282366920938463463374607431768211455), 16), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.and (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6102⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6103⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6104⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6106⟩ : UInt256), UInt8.ofNat 27, .SHL, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.or (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6107⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6108⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6109⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genMload r9 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6110⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 2) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6111⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.signextend (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6113⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap1 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6114⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6115⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6117⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6118⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMload r16 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6119⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 2) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6120⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.signextend (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6122⟩ : UInt256), UInt8.ofNat 11, .SIGNEXTEND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.dup13 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6123⟩ : UInt256), UInt8.ofNat 140, .DUP13, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup5 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6124⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6125⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := RD.genMload r22 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6126⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 96) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6127⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6129⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6130⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMload r26 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6131⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.swap2 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6132⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.dup15 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6133⟩ : UInt256), UInt8.ofNat 142, .DUP15, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := RD.genMload r29 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6134⟩ : UInt256), UInt8.ofNat 81, .MLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.swap5 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6135⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.dup6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6136⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := RD.genMstore r32 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6137⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6138⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r35 := r34.dup6 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6140⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r36 := r35.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6141⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r37 := RD.genMstore r36 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6142⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r38 := r37.dup14 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6143⟩ : UInt256), UInt8.ofNat 141, .DUP14, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r39 := r38.dup5 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6144⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r40 := r39.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6145⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r41 := RD.genMstore r40 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6146⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 96) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6147⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 96), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r43 := r42.dup4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6149⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r44 := r43.add (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6150⟩ : UInt256), UInt8.ofNat 1, .ADD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r45 := RD.genMstore r44 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6151⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r46 := r45.pushConst (UInt256.ofNat 109475532073130641761055205459242340063606971729438454954030529217048402318828) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6152⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 109475532073130641761055205459242340063606971729438454954030529217048402318828), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 128) (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6185⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r48 := r47.caller (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6187⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r49 := r48.swap4 (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨6188⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.log3Static r49 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, immWords,
      (⟨6189⟩ : UInt256), UInt8.ofNat 163, .LOG3, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by evm_ov)

end Benchmarks.UniswapV4PoolManager
