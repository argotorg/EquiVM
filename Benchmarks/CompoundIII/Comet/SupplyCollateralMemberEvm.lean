import Benchmarks.CompoundIII.Comet.SupplyCollateralStacks
import Benchmarks.CompoundIII.Comet.AssetMembershipEvm
import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_064
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_065

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyCollateralMember {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr amount balance next ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (sender dst asset : AccountAddress)
    (hstack : R.length + 21 ≤ 1024) (hperm : ee.perm = true)
    (hoffset : memLoad ptr mem = calldataWord out 0) (hv : AssetValid out)
    (hb : balance.toNat < 2^128) (hn : next.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14071⟩
      (supplyCollateralMemberStack sender dst asset ptr amount balance next ret R)
      mem aw out σ k C) :
    internalDynamicRun (deployedRuntime v) ee g s0 ret R
      (assetMembershipResult evm dst (calldataWord out 0) balance next) := by
  have r1 := cometWithExtendedAssetList_block_14071
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 12 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨mem', _, hr⟩ := cometUpdateAssetsIn (v := v) dst
    (by change R.length + 7 + 14 ≤ 1024; omega) hoffset hv.2.1 hb hn
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases he : assetMembershipResult evm dst (calldataWord out 0) balance next with
  | reverted => simpa only [he, internalMemoryRun, internalDynamicRun] using hr
  | staticViolation => simpa only [he, internalMemoryRun, internalDynamicRun] using hr
  | ok evm' =>
    simp only [he, internalMemoryRun, internalDynamicRun] at hr ⊢
    obtain ⟨σ', aw2, k2, C2, hs', r2⟩ := hr
    have r3 := cometWithExtendedAssetList_block_14077
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_13801
      (immWords := wordsOf (immStore v)) (by change R.length + 7 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    have r5 := cometWithExtendedAssetList_block_14109
      (immWords := wordsOf (immStore v)) (by change R.length + 8 ≤ 1024; omega) hperm hret r4
    exact ⟨σ', _, _, out, _, _, hs', r5⟩

end Benchmarks.CompoundIII.Comet
