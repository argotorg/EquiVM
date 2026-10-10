import Benchmarks.CompoundIII.Comet.AbsorbSeizeModel
import Benchmarks.CompoundIII.Comet.CollateralStoreEvm
import Benchmarks.CompoundIII.Comet.CheckedSub128Evm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_079

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbSeizeTotals {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw delta seized : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (asset : AccountAddress) (hstack : R.length + 9 ≤ 1024) (hseized : seized.toNat < 2^128)
    (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17682⟩
      (totalsCollateralSlot asset :: delta :: seized :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 mem rdata ⟨17713⟩ (delta :: seized :: R)
      (absorbSeizeTotalOutcome evm asset seized) := by
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_17682
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_2451 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  change RD _ _ _ _ _
    (UInt256.land (UInt256.ofNat (2^128-1)) (solcSlotWord σ ee (totalsCollateralSlot asset)) ::
      seized :: totalsCollateralSlot asset :: delta :: seized :: R) _ _ _ _ _ _ at r2
  rw [u256_land_comm (UInt256.ofNat (2^128-1)), ← hs.storageRead] at r2
  have r3 := cometWithExtendedAssetList_block_17694 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  rcases cometCheckedSub128 (v := v) (x := withdrawCollateralTotal evm asset) (y := seized)
      (by change R.length + 3 + 6 ≤ 1024; omega) (low128_lt _) hseized
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
    ⟨hle, k4, C4, r4⟩ | ⟨hle, hr⟩
  · have r5 := cometWithExtendedAssetList_block_17704 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    have hr := cometStoreLow128 (v := v) (by change R.length + 2 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r5
    rw [hs.env, hperm] at hr
    rw [absorbSeizeTotalOutcome, if_pos hle]
    exact hr
  · rw [absorbSeizeTotalOutcome, if_neg hle]
    exact hr

end Benchmarks.CompoundIII.Comet
