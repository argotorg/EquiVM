import Benchmarks.CompoundIII.Comet.SupplyCollateralAfterAssetEvm
import Benchmarks.CompoundIII.Comet.TransferInEvm
import Benchmarks.CompoundIII.Comet.Safe128Evm
import Benchmarks.CompoundIII.Comet.AssetSearchEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyCollateral {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst asset : AccountAddress) (hstack : R.length + 30 ≤ 1024)
    (ha : amount.toNat < 2^128) (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 576 + 768 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13820⟩
      (EVM.word sender.val :: EVM.word dst.val :: EVM.word asset.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, SupplyCollateralTrace v sender dst asset amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_13820
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hclean : UInt256.land amount
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) = amount := low128_clean _ ha
  simp only [cometWithExtendedAssetList_block_13820_stack, hclean] at r1
  obtain ⟨result, ht, hr⟩ := cometTransferInInternal (v := v)
    (by change R.length + 6 + 16 ≤ 1024; omega) hfree hlo (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .transferFailed ht, hr⟩
  | some result =>
    obtain ⟨evm', received⟩ := result
    obtain ⟨σ', mem', aw1, out, k1, C1, hs', hfree', _, r2⟩ := hr
    have hn : (free + ⟨64⟩).toNat = free.toNat + 64 :=
      uadd_word_ofNat_toNat free 64 (by change free.toNat + 64 < 2^256; omega)
    have r3 := cometWithExtendedAssetList_block_13846
      (immWords := wordsOf (immStore v)) (by change R.length + 7 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    rcases cometSafe128 (v := v) (by change R.length + 5 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
      ⟨hw, k4, C4, r4⟩ | ⟨hw, hr⟩
    · have r5 := cometWithExtendedAssetList_block_13851
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      obtain ⟨result, hasset, hr⟩ := cometAssetSearchInternalBounded (v := v)
        (by change R.length + 6 + 18 ≤ 1024; omega) hfree' (by omega) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs' r5
      cases result with
      | none => exact ⟨.reverted, .assetFailed ht hw hasset, hr⟩
      | some result =>
        obtain ⟨evm'', assetOut⟩ := result
        obtain ⟨σ'', mem'', ptr, free', aw6, k6, C6, hs'', hv, hm, hf, _, r6⟩ := hr
        exact ⟨_, .done ht hw hasset hv,
          cometSupplyCollateralAfterAsset sender dst asset hstack hw hv hm
            (by omega) hret hs'' r6⟩
    · exact ⟨.reverted, .tooLarge ht hw, hr⟩

end Benchmarks.CompoundIII.Comet
