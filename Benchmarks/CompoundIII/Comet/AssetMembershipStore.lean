import Benchmarks.CompoundIII.Comet.AssetMembershipModel
import Benchmarks.CompoundIII.Comet.PauseStatic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- The supplied write summary assumes permission; this prefix proves the static halt.
theorem cometStoreAssetsStatic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11547)
      (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11547⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11548⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11549⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 65535)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11550⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 65535), 2), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 232)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11553⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 232), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11555⟩ : UInt256), UInt8.ofNat 27, .SHL, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.not
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11556⟩ : UInt256), UInt8.ofNat 25, .NOT, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.and
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11557⟩ : UInt256), UInt8.ofNat 22, .AND, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 232)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11558⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 232), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.swap3
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11560⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11561⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.swap3
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11562⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11563⟩ : UInt256), UInt8.ofNat 27, .SHL, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 65535)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11564⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((UInt256.ofNat 65535), 2), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 232)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11567⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 232), 1), 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.shl
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11569⟩ : UInt256), UInt8.ofNat 27, .SHL, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11570⟩ : UInt256), UInt8.ofNat 22, .AND, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11571⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11572⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11573⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.or
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11574⟩ : UInt256), UInt8.ofNat 23, .OR, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11575⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r22 hperm
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11576⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, 
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

def assetMembershipStorePc (reserved : Bool) : UInt256 :=
  if reserved then ⟨11083⟩ else ⟨11547⟩

theorem cometStoreMembership {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw slot word ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (reserved : Bool) (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (assetMembershipStorePc reserved)
      (slot :: word :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 mem rdata ret R
      (if evm.executionEnv.perm then .ok (storePackedWord evm slot word
        (if reserved then 31 else 29) (if reserved then 1 else 2))
        else .staticViolation) := by
  rw [hs.env]
  cases reserved <;> cases hp : ee.perm
  · exact cometStoreAssetsStatic (by omega) hp h
  · obtain ⟨k', C', hr⟩ := cometWithExtendedAssetList_block_11547
      (immWords := wordsOf (immStore v)) (by omega) hp hret h
    exact ⟨_, aw, k', C', sourceState_userBasicAssets hs slot word, hr⟩
  · exact cometStorePauseStatic hstack hp h
  · obtain ⟨k', C', hr⟩ := cometWithExtendedAssetList_block_11083
      (immWords := wordsOf (immStore v)) hstack hp hret h
    exact ⟨_, aw, k', C', sourceState_userBasicReserved hs slot word, hr⟩

end Benchmarks.CompoundIII.Comet
