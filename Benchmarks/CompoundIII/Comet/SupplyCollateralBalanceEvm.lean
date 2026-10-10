import Benchmarks.CompoundIII.Comet.SupplyCollateralStacks
import Benchmarks.CompoundIII.Comet.CheckedAdd128Evm
import Benchmarks.CompoundIII.Comet.CollateralMappingMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_064
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_049

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyCollateralBalance {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr totalPtr amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst asset : AccountAddress) (hstack : R.length + 28 ≤ 1024)
    (ha : amount.toNat < 2^128) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13952⟩
      (EVM.word asset.val :: ptr :: totalPtr :: amount :: EVM.word sender.val ::
        EVM.word dst.val :: ret :: R) mem aw out σ k C) :
    ((withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128 ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨14040⟩
        (supplyCollateralWriteStack sender dst asset ptr totalPtr amount
          (withdrawCollateralBalance evm dst asset) (supplyCollateralNext evm dst asset amount) ret R)
        (userCollateralMemory mem dst asset) aw' out σ k' C') ∨
    (¬ (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128 ∧
      RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_13952
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 24 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 21 + 6 ≤ 1024; omega) (word_val_addr_canonical dst)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_14028
    (immWords := wordsOf (immStore v)) (by change R.length + 22 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometMappingHash (v := v)
    (by change R.length + 19 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  obtain ⟨k5, C5, r5⟩ := cometWithExtendedAssetList_block_10518
    (immWords := wordsOf (immStore v)) (by change R.length + 18 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  have hread : solcSlotWordAt (userCollateralSlot dst asset) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userCollateralSlot dst asset) := by
    simpa only [hs.env] using (hs.storageRead (userCollateralSlot dst asset)).symm
  change RD _ _ _ _ _ (UInt256.land _ (solcSlotWordAt (userCollateralSlot dst asset) σ ee) :: _)
    _ _ _ _ _ _ at r5
  rw [hread, u256_land_comm] at r5
  have r6 := cometWithExtendedAssetList_block_14033
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 12 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  rcases cometCheckedAdd128 (v := v) (by change R.length + 17 + 6 ≤ 1024; omega)
      (low128_lt _) ha (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6 with
    ⟨hf, k7, C7, r7⟩ | ⟨hf, hr⟩
  · exact Or.inl ⟨hf, aw4, k7, C7, r7⟩
  · exact Or.inr ⟨hf, hr⟩

end Benchmarks.CompoundIII.Comet
