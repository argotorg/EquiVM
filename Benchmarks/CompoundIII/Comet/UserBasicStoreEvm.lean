import Benchmarks.CompoundIII.Comet.UserBasicMemory
import Benchmarks.CompoundIII.Comet.UserBasicState
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometStoreUserBasic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (addr : AccountAddress) (basic : UserBasicData)
    (hstack : R.length + 12 ≤ 1024) (hperm : ee.perm = true)
    (hm : UserBasicMemory mem ptr basic) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11578⟩
      (userBasicSlot addr :: ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ σ' aw' k' C', SourceState s0 ee σ' (storeUserBasic evm addr basic) ∧
      RD (deployedRuntime v) ee g s0 ret R mem aw' rdata σ' k' C' := by
  obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_11578
    (immWords := wordsOf (immStore v)) (by simpa using (show R.length + 1 + 9 ≤ 1024 by omega)) h
  dsimp only [cometWithExtendedAssetList_block_11578_stack] at r1
  rw [hm.principal,
    show memLoad (ptr + UInt256.ofNat 32) mem = basic.index from hm.index,
    show memLoad (ptr + UInt256.ofNat 64) mem = basic.accrued from hm.accrued] at r1
  obtain ⟨_, _, r2⟩ := cometWithExtendedAssetList_block_11660
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 9 ≤ 1024; omega) hperm
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  dsimp only [cometWithExtendedAssetList_block_11660_stack] at r2
  have hassets : UInt256.land (UInt256.ofNat 65535) basic.assets = basic.assets := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 16) rfl basic.assets_lt
  rw [show memLoad (ptr + UInt256.ofNat 96) mem = basic.assets from hm.assets, hassets] at r2
  have hs2 := sourceState_userBasicLow hs addr basic
  obtain ⟨_, _, r3⟩ := cometWithExtendedAssetList_block_11547
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 6 ≤ 1024; omega) hperm
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hs3 := sourceState_userBasicAssets hs2 (userBasicSlot addr) basic.assets
  have r4 := cometWithExtendedAssetList_block_11692
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  dsimp only [cometWithExtendedAssetList_block_11692_stack] at r4
  rw [show memLoad (ptr + UInt256.ofNat 128) mem = basic.reserved from hm.reserved,
    u256LandMaskCleanOfToNat _ _ (bits := 8) rfl basic.reserved_lt] at r4
  obtain ⟨_, _, r5⟩ := cometWithExtendedAssetList_block_11083
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega) hperm
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  have hs5 := sourceState_userBasicReserved hs3 (userBasicSlot addr) basic.reserved
  have r6 := cometWithExtendedAssetList_block_3121
    (immWords := wordsOf (immStore v)) (by simpa using (show R.length + 1 ≤ 1024 by omega))
    hret r5
  refine ⟨_, _, _, _, ?_, r6⟩
  rw [storeUserBasic_eq]
  exact hs5

theorem cometStoreUserBasicStatic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {slot ptr : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 ⟨11578⟩ (slot :: ptr :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_11578
    (immWords := wordsOf (immStore v)) hstack h
  dsimp only [cometWithExtendedAssetList_block_11578_stack] at r1
  have r2 := r1.or
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11660⟩ : UInt256), UInt8.ofNat 23, .OR, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup2
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11661⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r3.sstoreStatic hperm
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨11662⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.CompoundIII.Comet
