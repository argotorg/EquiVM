import Benchmarks.CompoundIII.Comet.SupplyCollateralModel
import Benchmarks.CompoundIII.Comet.TotalsCollateralAllocation
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_064

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def supplyCollateralReadMemory (mem : ByteArray) (free : UInt256) (evm : EVM.State)
    (asset : AccountAddress) : ByteArray :=
  totalsCollateralAllocatedMemory (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem) free
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset))

theorem supplyCollateralReadMemory_asset {mem ptr free out evm asset}
    (hm : AssetMemory mem ptr free out) (hb : free.toNat + 64 < UInt256.size) :
    WordStructMemory (supplyCollateralReadMemory mem free evm asset) ptr 8
      (fun i ↦ calldataWord out (32 * i)) := by
  have hm' := hm.scratch (EVM.word asset.val) ⟨2⟩
  have hw : WordStructMemory (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem)
      ptr 8 (fun i ↦ calldataWord out (32 * i)) :=
    ⟨by have hs := hm'.separate; have hb := hm'.bounded; omega, hm'.present, hm'.words⟩
  apply hw.preserve hm'.lower
  exact (allocatedWordStruct_prefix
    (mem := twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem) (ptr := free) (n := 2)
    (words := collateralTotalWords (withdrawCollateralTotal evm asset)
      (supplyCollateralReserved evm asset)) hb).mono hm'.separate

theorem cometSupplyCollateralRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr free amount ret sender dst : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (asset : AccountAddress) (hstack : R.length + 16 ≤ 1024)
    (hm : AssetMemory mem ptr free out) (hb : free.toNat + 64 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13861⟩
      (ptr :: EVM.word asset.val :: ⟨2^128-1⟩ :: amount :: sender :: dst :: ret :: R)
      mem aw out σ k C) :
    ∃ aw' k' C',
      TotalsCollateralMemory (supplyCollateralReadMemory mem free evm asset) free
        (withdrawCollateralTotal evm asset) (supplyCollateralReserved evm asset) ∧
      WordStructMemory (supplyCollateralReadMemory mem free evm asset) ptr 8
        (fun i ↦ calldataWord out (32 * i)) ∧
      RD (deployedRuntime v) ee g s0 ⟨13881⟩
        (free :: EVM.word asset.val :: ptr :: ⟨2^128-1⟩ :: amount :: sender :: dst :: ret :: R)
        (supplyCollateralReadMemory mem free evm asset) aw' out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_13861
    (immWords := wordsOf (immStore v)) (by change R.length + 5 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 8 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_13876
    (immWords := wordsOf (immStore v)) (by change R.length + 9 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hm' := hm.scratch (EVM.word asset.val) ⟨2⟩
  obtain ⟨aw4, k4, C4, ht, r4⟩ := cometAllocateTotalsCollateral (v := v)
    (by change R.length + 7 + 9 ≤ 1024; omega) hm'.freeWord hb
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have hread : solcSlotWordAt (solcMappingSlot (UInt256.ofNat 2) (EVM.word asset.val)) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset) := by
    simpa only [hs.env] using (hs.storageRead (totalsCollateralSlot asset)).symm
  rw [hread] at ht r4
  exact ⟨aw4, k4, C4, ht, supplyCollateralReadMemory_asset hm
    (by change free.toNat + 64 < 2^256; omega), r4⟩

end Benchmarks.CompoundIII.Comet
