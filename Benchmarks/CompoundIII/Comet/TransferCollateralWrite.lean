import Benchmarks.CompoundIII.Comet.TransferCollateralStacks
import Benchmarks.CompoundIII.Comet.CollateralStoreEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_071

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferCollateralWrite {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount srcBalance srcNext dstBalance dstNext ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (src dst asset : AccountAddress)
    (hstack : R.length + 22 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15435⟩
      (transferCollateralWriteStack src dst asset amount srcBalance srcNext dstBalance dstNext ret R)
      mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 (transferCollateralMemory mem src dst asset)
      rdata ⟨15502⟩
      (transferCollateralReadyStack src dst asset amount srcBalance srcNext dstBalance dstNext ret R)
      (if evm.executionEnv.perm then .ok
        (storePackedWord (storePackedWord evm (userCollateralSlot src asset) srcNext 0 16)
          (userCollateralSlot dst asset) dstNext 0 16) else .staticViolation) := by
  have r1 := cometWithExtendedAssetList_block_15435
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 14 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 14 + 6 ≤ 1024; omega) (word_val_addr_canonical src)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_15449
    (immWords := wordsOf (immStore v)) (by change R.length + 13 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometMappingHash (v := v)
    (by change R.length + 13 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_15459
    (immWords := wordsOf (immStore v)) (by change R.length + 12 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  have hw := cometStoreLow128 (v := v) (by change R.length + 12 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r5
  cases hp : evm.executionEnv.perm
  · simpa only [hp, Bool.false_eq_true, if_false, internalMemoryRun] using hw
  · simp only [hp, if_true, internalMemoryRun] at hw ⊢
    obtain ⟨σ', aw6, k6, C6, hs', r6⟩ := hw
    have r7 := cometWithExtendedAssetList_block_15469
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 14 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
    obtain ⟨aw8, k8, C8, r8⟩ := cometMappingHash (v := v)
      (by change R.length + 14 + 6 ≤ 1024; omega) (word_val_addr_canonical dst)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
    have r9 := cometWithExtendedAssetList_block_15482
      (immWords := wordsOf (immStore v)) (by change R.length + 13 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
    obtain ⟨aw10, k10, C10, r10⟩ := cometMappingHash (v := v)
      (by change R.length + 13 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9
    have r11 := cometWithExtendedAssetList_block_15492
      (immWords := wordsOf (immStore v)) (by change R.length + 12 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r10
    have hw2 := cometStoreLow128 (v := v) (by change R.length + 12 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs' r11
    simpa only [storePackedWord, storageStore_executionEnv, hp, if_true,
      internalMemoryRun] using hw2

end Benchmarks.CompoundIII.Comet
