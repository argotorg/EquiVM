import Benchmarks.CompoundIII.Comet.AbsorbSeizeUserEvm
import Benchmarks.CompoundIII.Comet.AbsorbSeizeTotalsEvm
import Benchmarks.CompoundIII.Comet.AbsorbSeizeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbSeize {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw delta assetPtr absorber i assets reserved old oldPrincipal price : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account asset : AccountAddress) (hstack : R.length + 20 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17630⟩
      (userCollateralSlot account asset :: ⟨6⟩ :: EVM.word asset.val :: delta ::
        EVM.word account.val :: assetPtr :: absorber :: EVM.word account.val :: i :: assets ::
        reserved :: old :: oldPrincipal :: price :: EVM.word account.val :: EVM.word asset.val :: R)
      mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 (absorbSeizeMemory mem account asset) rdata
      ⟨17713⟩ (delta :: withdrawCollateralBalance evm account asset :: assetPtr :: absorber ::
        EVM.word account.val :: i :: assets :: reserved :: old :: oldPrincipal :: price ::
        EVM.word account.val :: EVM.word asset.val :: R) (absorbSeizeOutcome evm account asset) := by
  have hr := cometAbsorbSeizeUser (v := v) account asset
    (by change R.length + 10 + 10 ≤ 1024; omega) hs h
  cases hp : evm.executionEnv.perm
  · rw [hp] at hr
    rw [absorbSeizeOutcome, hp]
    simpa only [Bool.false_eq_true, if_false, internalMemoryRun] using hr
  · rw [hp] at hr
    obtain ⟨σ1, aw1, k1, C1, hs1, r1⟩ := hr
    have r2 := cometWithExtendedAssetList_block_17671 (immWords := wordsOf (immStore v))
      (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨aw3, k3, C3, r3⟩ := cometMappingHash (v := v)
      (by change R.length + 13 + 6 ≤ 1024; omega) (addressWord_val_canonical asset)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have hrT := cometAbsorbSeizeTotals (v := v) asset
      (by change R.length + 11 + 9 ≤ 1024; omega) (low128_lt _)
      (by rw [← hs.env]; exact hp) hs1 r3
    rw [absorbSeizeOutcome, hp]
    exact hrT

end Benchmarks.CompoundIII.Comet
