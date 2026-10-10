import Benchmarks.CompoundIII.Comet.CollateralStorage
import Benchmarks.CompoundIII.Comet.InternalMemoryOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_064

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- The supplied write summary assumes permission; this prefix proves the static halt.
theorem cometStoreLow128Static {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 ⟨13718⟩
      (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13718⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13719⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13720⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13721⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13723⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13725⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13727⟩ : UInt256), UInt8.ofNat 27, .SHL, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.sub
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13728⟩ : UInt256), UInt8.ofNat 3, .SUB, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.not
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13729⟩ : UInt256), UInt8.ofNat 25, .NOT, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.and
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13730⟩ : UInt256), UInt8.ofNat 22, .AND, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13731⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13733⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 128)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13735⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 128), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13737⟩ : UInt256), UInt8.ofNat 27, .SHL, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.sub
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13738⟩ : UInt256), UInt8.ofNat 3, .SUB, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13739⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap3
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13740⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.and
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13741⟩ : UInt256), UInt8.ofNat 22, .AND, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13742⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13743⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13744⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.or
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13745⟩ : UInt256), UInt8.ofNat 23, .OR, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13746⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r23 hperm
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨13747⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem cometStoreLow128 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw slot word ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13718⟩
      (slot :: word :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 mem rdata ret R
      (if evm.executionEnv.perm then .ok (storePackedWord evm slot word 0 16)
        else .staticViolation) := by
  rw [hs.env]
  cases hp : ee.perm
  · exact cometStoreLow128Static hstack hp h
  · obtain ⟨k', C', hr⟩ := cometWithExtendedAssetList_block_13718
      (immWords := wordsOf (immStore v)) hstack hp hret h
    exact ⟨_, aw, k', C', sourceState_low128Write hs slot word, hr⟩

end Benchmarks.CompoundIII.Comet
