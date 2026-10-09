import Benchmarks.CompoundIII.Comet.BuyCollateralQuoteEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometBuyCollateralForSale {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {reserves : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨6424⟩ (reserves :: R) mem aw rdata σ k C) :
    (BuyCollateralForSale v reserves ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨6442⟩ R mem aw rdata σ k' C') ∨
      (¬ BuyCollateralForSale v reserves ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hlo : reserves.toNat < 2^255
  · have hsign : UInt256.slt reserves (UInt256.ofNat 0) = UInt256.ofNat 0 :=
      slt_lit_zero (by decide) (Nat.zero_le _) hlo
    have r1 := cometWithExtendedAssetList_block_6424_taken (immWords := wordsOf (immStore v))
      hstack (by rw [hsign]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [cometWithExtendedAssetList_block_6424_taken_stack] at r1
    have r2 := cometWithExtendedAssetList_block_6684 (immWords := wordsOf (immStore v))
      (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [cometWithExtendedAssetList_block_6684_stack, wordsOf_immStore_targetReserves,
      wordOfInt_ofNat_toNat] at r2
    by_cases htarget : v.targetReserves.toNat ≤ reserves.toNat
    · have r3 := cometWithExtendedAssetList_block_6436_taken (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_zero htarget]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      exact Or.inr ⟨fun hn ↦ hn ⟨(signedWord_nonneg_iff reserves).2 hlo, htarget⟩,
        cometWithExtendedAssetList_block_6666 (immWords := wordsOf (immStore v))
          (by change R.length + 3 ≤ 1024; omega) r3⟩
    · have r3 := cometWithExtendedAssetList_block_6436_fallthrough
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [ugt_one (Nat.lt_of_not_ge htarget)]; decide) r2
      exact Or.inl ⟨fun hv ↦ htarget hv.2, _, _, r3⟩
  · have hsign : UInt256.slt reserves (UInt256.ofNat 0) ≠ UInt256.ofNat 0 :=
      u256_slt_zero_ne_zero_of_high (by change 2^255 ≤ reserves.toNat; omega)
    have r1 := cometWithExtendedAssetList_block_6424_fallthrough
      (immWords := wordsOf (immStore v)) hstack (isZero_eq_zero_of_ne hsign) h
    simp only [cometWithExtendedAssetList_block_6424_fallthrough_stack] at r1
    have r2 := cometWithExtendedAssetList_block_6436_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (isZero_eq_zero_of_ne hsign) r1
    exact Or.inl ⟨fun hv ↦ hlo ((signedWord_nonneg_iff reserves).1 hv.1), _, _, r2⟩

theorem cometBuyCollateralAfterReserves {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {free base minimum reserves : UInt256} {R : List UInt256}
    {asset recipient : AccountAddress}
    (hstack : R.length + 26 ≤ 1024) (hperm : ee.perm = true)
    (hmin : calldataWord ee.calldata 36 = minimum) (hbase : calldataWord ee.calldata 68 = base)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hb : free.toNat + 896 + 768 * v.numAssets.toNat < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6424⟩
      (reserves :: EVM.word asset.val :: EVM.word recipient.val :: R) mem aw rdata σ k C) :
    ∃ result, BuyCollateralAfterReserves v asset recipient minimum base reserves evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result := by
  rcases cometBuyCollateralForSale (v := v) (by change R.length + 2 + 4 ≤ 1024; omega) h with
    ⟨hv, k1, C1, r1⟩ | ⟨hv, hr⟩
  · have r2 := cometWithExtendedAssetList_block_6442 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [cometWithExtendedAssetList_block_6442_stack, wordsOf_immStore_baseToken] at r2
    change RD _ _ _ _ _
      (EVM.word v.baseToken.val :: EVM.word ee.source.val :: calldataWord ee.calldata 68 ::
        UInt256.ofNat 6486 :: EVM.word asset.val :: EVM.word recipient.val :: R) _ _ _ _ _ _ at r2
    rw [hbase] at r2
    obtain ⟨result, ht, hr⟩ := cometTransferInInternal (v := v)
      (by change R.length + 2 + 16 ≤ 1024; omega) hfree hlo (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
    have ht' : TransferInTrace v.baseToken evm.executionEnv.source base evm result := by
      simpa only [hs.env] using ht
    cases result with
    | none => exact ⟨.reverted, .failed hv ht', hr⟩
    | some r =>
      obtain ⟨evm', received⟩ := r
      obtain ⟨σ', mem', aw', out, k', C', hs', hf', _, hr⟩ := hr
      have hptr : (free + (⟨64⟩ : UInt256)).toNat = free.toNat + 64 :=
        uadd_word_ofNat_toNat free 64 (by change free.toNat + 64 < 2^256; omega)
      obtain ⟨result, hn, hr⟩ := cometBuyCollateralAfterIn (v := v) hstack hperm hmin hf'
        (by rw [hptr]; omega) (by rw [hptr]; omega) hs' hr
      exact ⟨result, .received hv ht' hn, hr⟩
  · exact ⟨.reverted, .notForSale hv, hr⟩

end Benchmarks.CompoundIII.Comet
