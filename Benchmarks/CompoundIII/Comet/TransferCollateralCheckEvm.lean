import Benchmarks.CompoundIII.Comet.TransferCollateralStacks
import Benchmarks.CompoundIII.Comet.CollateralCheckEvm
import Benchmarks.CompoundIII.Comet.CollateralEventEvm
import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_070
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_071
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_064

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferCollateralCheck {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15532⟩
      (transferCollateralCheckStack src dst asset amount ret R) mem aw rdata σ k C) :
    ∃ result, TransferCollateralCheck v src evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_15532
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨result, ht, hr⟩ := cometCollateralCheck (v := v) true src
    (by change R.length + 6 + 35 ≤ 1024; omega) hfree hlo hmem hgap hbound
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .failed ht, hr⟩
  | some pair =>
    obtain ⟨evm', value⟩ := pair
    obtain ⟨σ', mem', free', aw', data, k', C', hs', _, _, _, _, _, r2⟩ := hr
    cases value
    · have r3 := cometWithExtendedAssetList_block_15541_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega)
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      exact ⟨.reverted, .rejected ht,
        cometWithExtendedAssetList_block_15192 (immWords := wordsOf (immStore v))
          (by change R.length + 6 + 3 ≤ 1024; omega) r3⟩
    · have r3 := cometWithExtendedAssetList_block_15541_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega)
        (by decide) r2
      have r4 := cometWithExtendedAssetList_block_15547
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      have r5 := cometWithExtendedAssetList_block_13801
        (immWords := wordsOf (immStore v)) (by change R.length + 7 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      exact ⟨_, .accepted ht, (cometCollateralLog (by change R.length + 8 ≤ 1024; omega)
        hret hs' r5).dynamic⟩

end Benchmarks.CompoundIII.Comet
