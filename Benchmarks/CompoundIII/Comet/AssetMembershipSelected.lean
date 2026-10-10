import Benchmarks.CompoundIII.Comet.AssetMembershipMask

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometMembershipAssets {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw offset ptr ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (add : Bool) (hstack : R.length + 14 ≤ 1024)
    (hoffset : memLoad ptr mem = offset) (hlo : offset.toNat < 16)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (if add then ⟨14188⟩ else ⟨14355⟩)
      (offset :: offset :: EVM.word account.val :: ptr :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (twoWordHashMem (EVM.word account.val) ⟨5⟩ mem) rdata ret R
      (assetMembershipFieldResult evm account add false offset.toNat) := by
  have hc : UInt256.land (UInt256.ofNat 255) offset = offset := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 8) rfl (by change offset.toNat < 256; omega)
  cases add
  · have r1 := cometWithExtendedAssetList_block_14355
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [cometWithExtendedAssetList_block_14355_stack] at r1
    rw [hoffset, hc] at r1
    obtain ⟨k2, C2, r2⟩ := cometMembershipMask16 (v := v)
      (by change R.length + 5 + 4 ≤ 1024; omega) hlo
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    have r4 := cometWithExtendedAssetList_block_14379
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    dsimp only [cometWithExtendedAssetList_block_14379_stack] at r4
    rw [u256_land_comm] at r4
    exact cometMembershipField account false false offset.toNat
      (by omega) hret hs r4
  · have r1 := cometWithExtendedAssetList_block_14188
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [cometWithExtendedAssetList_block_14188_stack] at r1
    rw [hoffset, hc] at r1
    obtain ⟨k2, C2, r2⟩ := cometMembershipMask16 (v := v)
      (by change R.length + 4 + 4 ≤ 1024; omega) hlo
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    exact cometMembershipField account true false offset.toNat
      (by omega) hret hs r2

theorem cometMembershipReserved {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw offset ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (add : Bool) (hstack : R.length + 14 ≤ 1024)
    (hlo : 16 ≤ offset.toNat) (hhi : offset.toNat < 24)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (if add then ⟨14270⟩ else ⟨14425⟩)
      (EVM.word account.val :: offset :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (twoWordHashMem (EVM.word account.val) ⟨5⟩ mem) rdata ret R
      (assetMembershipFieldResult evm account add true (offset.toNat - 16)) := by
  have hd : (UInt256.sub offset (UInt256.ofNat 16)).toNat = offset.toNat - 16 :=
    usub_toNat hlo
  cases add
  · have r1 := cometWithExtendedAssetList_block_14425
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 9 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨k2, C2, r2⟩ := cometCheckedSub8_ok (v := v) (x := offset) (y := UInt256.ofNat 16)
      (by change R.length + 6 + 5 ≤ 1024; omega)
      (by change offset.toNat < 256; omega) (by decide) hlo
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    obtain ⟨k3, C3, r3⟩ := cometMembershipMask8 (v := v)
      (by change R.length + 5 + 5 ≤ 1024; omega) (by rw [hd]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    rw [hd] at r3
    have r4 := cometWithExtendedAssetList_block_14448
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    dsimp only [cometWithExtendedAssetList_block_14448_stack] at r4
    rw [u256_land_comm] at r4
    exact cometMembershipField account false true (offset.toNat - 16)
      (by omega) hret hs r4
  · have r1 := cometWithExtendedAssetList_block_14270
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨k2, C2, r2⟩ := cometCheckedSub8_ok (v := v) (x := offset) (y := UInt256.ofNat 16)
      (by change R.length + 5 + 5 ≤ 1024; omega)
      (by change offset.toNat < 256; omega) (by decide) hlo
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    obtain ⟨k3, C3, r3⟩ := cometMembershipMask8 (v := v)
      (by change R.length + 4 + 5 ≤ 1024; omega) (by rw [hd]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    rw [hd] at r3
    exact cometMembershipField account true true (offset.toNat - 16)
      (by omega) hret hs r3

end Benchmarks.CompoundIII.Comet
