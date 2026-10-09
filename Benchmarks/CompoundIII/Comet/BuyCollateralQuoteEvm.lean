import Benchmarks.CompoundIII.Comet.BuyCollateralTransferEvm
import Benchmarks.CompoundIII.Comet.QuoteInternal
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometBuyCollateralAfterQuote {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {free base minimum amount : UInt256} {R : List UInt256}
    {asset recipient : AccountAddress}
    (hstack : R.length + 24 ≤ 1024) (hperm : ee.perm = true)
    (hmin : calldataWord ee.calldata 36 = minimum)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hb : free.toNat + 100 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6497⟩
      (amount :: EVM.word asset.val :: base :: EVM.word recipient.val :: R) mem aw rdata σ k C) :
    ∃ result, BuyCollateralAfterQuote asset recipient minimum amount evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result := by
  by_cases hm : minimum.toNat ≤ amount.toNat
  · have r1 := cometWithExtendedAssetList_block_6497_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by
        change UInt256.lt amount (calldataWord ee.calldata 36) = UInt256.ofNat 0
        rw [hmin]; exact ult_zero hm) h
    simp only [cometWithExtendedAssetList_block_6497_fallthrough_stack] at r1
    have r2 := cometWithExtendedAssetList_block_6508 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [cometWithExtendedAssetList_block_6508_stack] at r2
    obtain ⟨result, ht, hr⟩ := cometCollateralReservesTrace (v := v)
      (by change R.length + 4 + 11 ≤ 1024; omega) hfree hlo (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
    cases result with
    | none => exact ⟨.reverted, .reservesFailed hm ht, hr⟩
    | some r =>
      obtain ⟨evm', reserves⟩ := r
      obtain ⟨σ', mem', aw', out, k', C', hs', hf', _, hr⟩ := hr
      by_cases hstock : amount.toNat ≤ reserves.toNat
      · have r3 := cometWithExtendedAssetList_block_6516_fallthrough
          (immWords := wordsOf (immStore v)) (by omega) (ugt_zero hstock) hr
        simp only [cometWithExtendedAssetList_block_6516_fallthrough_stack] at r3
        have hptr : (free + (⟨32⟩ : UInt256)).toNat = free.toNat + 32 :=
          uadd_word_ofNat_toNat free 32 (by change free.toNat + 32 < 2^256; omega)
        obtain ⟨result, hn, hr⟩ := cometBuyCollateralTransfer (v := v) hstack hperm hf'
          (by rw [hptr]; omega) (by rw [hptr]; omega) hs' r3
        exact ⟨result, .transfer hm ht hstock hn, hr⟩
      · have r3 := cometWithExtendedAssetList_block_6516_taken
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [ugt_one (Nat.lt_of_not_ge hstock)]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) hr
        exact ⟨.reverted, .insufficient hm ht hstock,
          cometWithExtendedAssetList_block_6316 (immWords := wordsOf (immStore v))
            (by change R.length + 4 + 3 ≤ 1024; omega) r3⟩
  · have r1 := cometWithExtendedAssetList_block_6497_taken
      (immWords := wordsOf (immStore v)) (by omega) (by
        change UInt256.lt amount (calldataWord ee.calldata 36) ≠ UInt256.ofNat 0
        rw [hmin, ult_one (Nat.lt_of_not_ge hm)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨.reverted, .minimumFailed hm,
      cometWithExtendedAssetList_block_6648 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 3 ≤ 1024; omega) r1⟩

theorem cometBuyCollateralAfterIn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {free received minimum : UInt256} {R : List UInt256}
    {asset recipient : AccountAddress}
    (hstack : R.length + 26 ≤ 1024) (hperm : ee.perm = true)
    (hmin : calldataWord ee.calldata 36 = minimum)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hb : free.toNat + 832 + 768 * v.numAssets.toNat < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6486⟩
      (received :: EVM.word asset.val :: EVM.word recipient.val :: R) mem aw rdata σ k C) :
    ∃ result, BuyCollateralAfterIn v asset recipient minimum received evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result := by
  have r1 := cometWithExtendedAssetList_block_6486 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_6486_stack] at r1
  obtain ⟨result, ht, hr⟩ := cometQuoteInternalBounded (v := v)
    (by change R.length + 3 + 22 ≤ 1024; omega) hfree hlo hb
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .failed ht, hr⟩
  | some r =>
    obtain ⟨evm', amount⟩ := r
    obtain ⟨σ', mem', free', aw', out, k', C', hs', hf', hlo', hb', _, hr⟩ := hr
    obtain ⟨result, hn, hr⟩ := cometBuyCollateralAfterQuote (v := v)
      (by omega) hperm hmin hf' hlo' (by omega) hs' hr
    exact ⟨result, .quote ht hn, hr⟩

end Benchmarks.CompoundIII.Comet
