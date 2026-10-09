import Benchmarks.CompoundIII.Comet.AbsorbSeizeEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbAssetMapping {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ptr absorber i assets reserved old principal price delta : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account asset : AccountAddress) (hstack : R.length + 22 ≤ 1024)
    (hm : memLoad (ptr + UInt256.ofNat 32) mem = EVM.word asset.val)
    (h : RD (deployedRuntime v) ee g s0 ⟨17589⟩
      (ptr :: absorber :: EVM.word account.val :: i :: assets :: reserved :: old :: principal ::
        price :: EVM.word account.val :: delta :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨17630⟩
      (userCollateralSlot account asset :: ⟨6⟩ :: EVM.word asset.val :: delta ::
        EVM.word account.val :: ptr :: absorber :: EVM.word account.val :: i :: assets ::
        reserved :: old :: principal :: price :: EVM.word account.val :: EVM.word asset.val :: R)
      (userCollateralMemory mem account asset) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_17589 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (EVM.word asset.val) = EVM.word asset.val :=
    solcAddrMask_clean_left (addressWord_val_canonical asset)
  dsimp only [cometWithExtendedAssetList_block_17589_stack] at r1
  rw [hm, hmask] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 16 + 6 ≤ 1024; omega) (addressWord_val_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_17620 (immWords := wordsOf (immStore v))
    (by change R.length + 15 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨aw4, k4, C4, r4⟩ := cometMappingHash (v := v)
    (by change R.length + 15 + 6 ≤ 1024; omega) (addressWord_val_canonical asset)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  exact ⟨_, _, _, r4⟩

theorem cometAbsorbAssetSeize {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr absorber i assets reserved old principal price delta : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account asset : AccountAddress) (hstack : R.length + 22 ≤ 1024)
    (hm : memLoad (ptr + UInt256.ofNat 32) mem = EVM.word asset.val)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17589⟩
      (ptr :: absorber :: EVM.word account.val :: i :: assets :: reserved :: old :: principal ::
        price :: EVM.word account.val :: delta :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (absorbSeizeMemory (userCollateralMemory mem account asset) account asset) rdata ⟨17713⟩
      (delta :: withdrawCollateralBalance evm account asset :: ptr :: absorber ::
        EVM.word account.val :: i :: assets :: reserved :: old :: principal :: price ::
        EVM.word account.val :: EVM.word asset.val :: R) (absorbSeizeOutcome evm account asset) := by
  obtain ⟨aw1, k1, C1, r1⟩ := cometAbsorbAssetMapping account asset hstack hm h
  exact cometAbsorbSeize account asset (by omega) hs r1

end Benchmarks.CompoundIII.Comet
