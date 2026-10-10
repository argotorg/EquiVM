import Benchmarks.CompoundIII.Comet.WithdrawCollateralRead
import Benchmarks.CompoundIII.Comet.CollateralStoreEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawCollateralWriteStack (src recipient asset : AccountAddress)
    (amount balance next totalNext ret : UInt256) (R : List UInt256) : List UInt256 :=
  [totalNext, totalsCollateralSlot asset, ⟨0⟩, EVM.word asset.val, next, next,
    balance, EVM.word src.val, ⟨2^128-1⟩, EVM.word recipient.val, solcAddrMask,
    EVM.word asset.val, EVM.word src.val, amount, EVM.word asset.val, ret] ++ R

def withdrawCollateralReadyStack (src recipient asset : AccountAddress)
    (amount balance next ret : UInt256) (R : List UInt256) : List UInt256 :=
  [next, balance, EVM.word src.val, ⟨2^128-1⟩, EVM.word recipient.val, solcAddrMask,
    EVM.word asset.val, EVM.word src.val, amount, EVM.word asset.val, ret] ++ R

theorem cometWithdrawCollateralWrite {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount balance next totalNext ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (src recipient asset : AccountAddress)
    (hstack : R.length + 22 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16380⟩
      (withdrawCollateralWriteStack src recipient asset amount balance next totalNext ret R)
      mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 (userCollateralMemory mem src asset)
      rdata ⟨16421⟩ (withdrawCollateralReadyStack src recipient asset amount balance next ret R)
      (if evm.executionEnv.perm then .ok
        (storePackedWord (storePackedWord evm (totalsCollateralSlot asset) totalNext 0 16)
          (userCollateralSlot src asset) next 0 16) else .staticViolation) := by
  have r1 := cometWithExtendedAssetList_block_16380
    (immWords := wordsOf (immStore v)) (by change R.length + 14 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hw := cometStoreLow128 (v := v) (by change R.length + 14 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases hp : evm.executionEnv.perm
  · simpa only [hp, Bool.false_eq_true, if_false, internalMemoryRun] using hw
  · simp only [hp, if_true, internalMemoryRun] at hw ⊢
    obtain ⟨σ1, aw1, k1, C1, hs1, r2⟩ := hw
    have r3 := cometWithExtendedAssetList_block_16389
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 13 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    dsimp only [cometWithExtendedAssetList_block_16389_stack,
      cometWithExtendedAssetList_block_16389_memory] at r3
    have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((UInt256.ofNat 6).toByteArray.write 0
          ((EVM.word src.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) = solcMappingSlot ⟨6⟩ (EVM.word src.val) :=
      twoWordHashMem_solcMappingSlot_any ⟨6⟩ (EVM.word src.val) mem
    rw [hh] at r3
    obtain ⟨aw4, k4, C4, r4⟩ := cometMappingHash (v := v)
      (by change R.length + 12 + 6 ≤ 1024; omega) (word_val_addr_canonical asset)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    have r5 := cometWithExtendedAssetList_block_16411
      (immWords := wordsOf (immStore v)) (by change R.length + 11 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    have hw2 := cometStoreLow128 (v := v) (by change R.length + 11 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs1 r5
    simpa only [storePackedWord, storageStore_executionEnv, hp, if_true,
      internalMemoryRun] using hw2

end Benchmarks.CompoundIII.Comet
