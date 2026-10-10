import Benchmarks.CompoundIII.Comet.SupplyCollateralStacks
import Benchmarks.CompoundIII.Comet.TotalsCollateralStoreEvm
import Benchmarks.CompoundIII.Comet.CollateralMappingMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_065

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def supplyCollateralWriteMemory (mem : ByteArray) (dst asset : AccountAddress) : ByteArray :=
  userCollateralMemory (twoWordHashMem (EVM.word asset.val) ⟨2⟩ mem) dst asset

theorem cometSupplyCollateralWrite {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr totalPtr amount balance next total reserved ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (sender dst asset : AccountAddress)
    (hstack : R.length + 30 ≤ 1024) (htotal : total.toNat < 2^128)
    (hm : TotalsCollateralMemory mem totalPtr total reserved) (hlo : 96 ≤ totalPtr.toNat)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14040⟩
      (supplyCollateralWriteStack sender dst asset ptr totalPtr amount balance next ret R)
      mem aw out σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (supplyCollateralWriteMemory mem dst asset) out ⟨14071⟩
      (supplyCollateralMemberStack sender dst asset ptr amount balance next ret R)
      (if evm.executionEnv.perm then .ok
        (storePackedWord (storeTotalsCollateral evm asset total reserved)
          (userCollateralSlot dst asset) next 0 16) else .staticViolation) := by
  have r1 := cometWithExtendedAssetList_block_14040
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 15 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 19 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_14054
    (immWords := wordsOf (immStore v)) (by change R.length + 20 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hm' := hm.scratch hlo (EVM.word asset.val) ⟨2⟩
  have ht := cometStoreTotalsCollateral (v := v) asset
    (by change R.length + 17 + 12 ≤ 1024; omega) htotal hm'
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r3
  cases hp : evm.executionEnv.perm
  · simpa only [hp, Bool.false_eq_true, if_false, internalMemoryRun] using ht
  · simp only [hp, if_true, internalMemoryRun] at ht ⊢
    obtain ⟨σ', aw4, k4, C4, hs', r4⟩ := ht
    have r5 := cometWithExtendedAssetList_block_14059
      (immWords := wordsOf (immStore v)) (by change R.length + 17 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    obtain ⟨aw6, k6, C6, r6⟩ := cometMappingHash (v := v)
      (by change R.length + 15 + 6 ≤ 1024; omega) (word_val_addr_canonical dst)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
    have r7 := cometWithExtendedAssetList_block_14028
      (immWords := wordsOf (immStore v)) (by change R.length + 16 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
    obtain ⟨aw8, k8, C8, r8⟩ := cometMappingHash (v := v)
      (by change R.length + 13 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
    have r9 := cometWithExtendedAssetList_block_14066
      (immWords := wordsOf (immStore v)) (by change R.length + 14 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
    have hwrite := cometStoreLow128 (v := v) (by change R.length + 11 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs' r9
    simpa only [storeTotalsCollateral, storePackedWord, storageStore_executionEnv,
      hp, if_true, internalMemoryRun] using hwrite

end Benchmarks.CompoundIII.Comet
