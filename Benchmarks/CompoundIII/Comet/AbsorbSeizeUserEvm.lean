import Benchmarks.CompoundIII.Comet.AbsorbSeizeModel
import Benchmarks.CompoundIII.Comet.CollateralMappingMemory
import Benchmarks.CompoundIII.Comet.CollateralStoreEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_079

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbSeizeUser {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw delta assetPtr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account asset : AccountAddress) (hstack : R.length + 10 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17630⟩
      (userCollateralSlot account asset :: ⟨6⟩ :: EVM.word asset.val :: delta ::
        EVM.word account.val :: assetPtr :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 (userCollateralMemory mem account asset)
      rdata ⟨17671⟩ (delta :: withdrawCollateralBalance evm account asset :: assetPtr :: R)
      (if evm.executionEnv.perm then .ok (absorbSeizeUserState evm account asset)
        else .staticViolation) := by
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_17630
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    (⟨6⟩ :: EVM.word account.val :: ⟨17650⟩ :: EVM.word asset.val :: delta ::
      UInt256.land (UInt256.ofNat (2^128-1))
        (solcSlotWord σ ee (userCollateralSlot account asset)) :: assetPtr :: R)
    _ _ _ _ _ _ at r1
  rw [u256_land_comm (UInt256.ofNat (2^128-1)), ← hs.storageRead] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 4 + 6 ≤ 1024; omega) (addressWord_val_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_17650 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometMappingHash (v := v)
    (by change R.length + 3 + 6 ≤ 1024; omega) (addressWord_val_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_17660 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  exact cometStoreLow128 (v := v) (by change R.length + 3 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r5

end Benchmarks.CompoundIII.Comet
