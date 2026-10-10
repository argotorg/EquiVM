import Benchmarks.CompoundIII.Comet.BoolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

-- The supplied write summary assumes permission; its decoded prefix also proves the static halt.
theorem cometStorePauseStatic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11083)
      (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11083⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11084⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11085⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11086⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11088⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 248)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11090⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 248), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11092⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11093⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.and
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11094⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 248)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11095⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 248), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap3
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11097⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11098⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.swap3
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11099⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11100⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11101⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11103⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 248)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11105⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 248), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11107⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.sub
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11108⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.not
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11109⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.and
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11110⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.swap2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11111⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11112⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11113⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.or
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11114⟩ : UInt256), UInt8.ofNat 23, .OR, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11115⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r26 hperm
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11116⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.CompoundIII.Comet
