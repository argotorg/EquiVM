import Benchmarks.CompoundIII.Comet.QuoteFinishEvm
import Benchmarks.CompoundIII.Comet.AssetSearchEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometQuoteAfterAssetBounded {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata assetOut : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {amount ptr free ret : UInt256} {R : List UInt256}
    {evm : EVM.State} (hstack : R.length + 22 ≤ 1024)
    (hm : AssetMemory mem ptr free assetOut) (hv : AssetValid assetOut)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 576 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17981⟩
      (ptr :: ⟨18165⟩ :: amount :: ⟨2425⟩ :: ret :: R) mem aw rdata σ k C) :
    ∃ result, QuoteAfterAsset v assetOut amount evm result ∧ QuoteRunBounded v ee g s0 ret R (free.toNat + 320) result := by
  have r1 := cometWithExtendedAssetList_block_17981 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hf : memLoad (ptr + UInt256.ofNat 64) mem = calldataWord assetOut 64 :=
    hm.words 2 (by decide)
  have hc : (calldataWord assetOut 64).toNat < EVM.addressModulus := hv.2.2.2.1
  have hmask : UInt256.land (calldataWord assetOut 64)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = calldataWord assetOut 64 := u256LandMaskCleanOfToNat _ _ rfl hc
  simp only [cometWithExtendedAssetList_block_17981_stack, hf, hmask] at r1
  rw [← addressWord_eq_ofNat_address hc] at r1
  have hlo : 96 ≤ free.toNat := by have hp := hm.lower; have hf := hm.separate; omega
  obtain ⟨evm', σ', z, out, hcall, hs', hh, hr⟩ := cometPriceInternal (v := v)
    (AccountAddress.ofNat (calldataWord assetOut 64).toNat)
    (by change R.length + 8 + 12 ≤ 1024; omega) hm.freeWord hlo hgap (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  have hh' : out.size < 2^255 := lt_trans hh (by decide)
  by_cases hp : z = true ∧ PriceValid out
  · rw [if_pos hp] at hr
    obtain ⟨rfl, hvp⟩ := hp
    obtain ⟨aw2, k2, C2, r2⟩ := hr
    have hhi : out.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
    have hm' := hm.afterPrice hgap (by change free.toNat + 416 < 2^256; omega) hvp.1 hhi
    have hfree : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
      uadd_word_ofNat_toNat _ _ (by change free.toNat + 160 < 2^256; omega)
    have hgap' : (free + (⟨160⟩ : UInt256)).toNat ≤
        (priceReturnMemory mem free out).size + 32 := by
      rw [hfree, priceReturnMemory_size hlo hgap hvp.1 hhi]
      omega
    obtain ⟨result, ht, hr⟩ := cometQuoteFinishBounded (v := v) hstack hm' hv hgap'
      (by rw [hfree]; omega) hret hs' r2
    exact ⟨result, QuoteAfterAsset.priceOk hcall hh' hvp ht, hr.mono (by rw [hfree])⟩
  · rw [if_neg hp] at hr
    exact ⟨none, QuoteAfterAsset.priceFailed hcall hh' hp, hr⟩

theorem cometQuoteInternalBounded {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {amount free ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State} (hstack : R.length + 22 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 832 + 768 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17965⟩
      (EVM.word asset.val :: amount :: ret :: R) mem aw rdata σ k C) :
    ∃ result, QuoteTrace v asset amount evm result ∧ QuoteRunBounded v ee g s0 ret R
      (free.toNat + 576 + 768 * v.numAssets.toNat) result := by
  have r1 := cometWithExtendedAssetList_block_17965 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨searchResult, hsearch, hr⟩ := cometAssetSearchInternalBounded (v := v)
    (by change R.length + 4 + 18 ≤ 1024; omega) hfree hlo (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases searchResult with
  | none => exact ⟨none, QuoteTrace.assetFailed hsearch, hr⟩
  | some r =>
      obtain ⟨evm', out⟩ := r
      obtain ⟨σ', mem', ptr, free', aw', k2, C2, hs', hv, hm, hlimit, hmem, r2⟩ := hr
      obtain ⟨result, ht, hr⟩ := cometQuoteAfterAssetBounded (v := v) hstack hm hv (by omega)
        (by omega) hret hs' r2
      exact ⟨result, QuoteTrace.assetOk hsearch ht, hr.mono (by omega)⟩

theorem cometQuoteAfterAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata assetOut : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {amount ptr free ret : UInt256} {R : List UInt256}
    {evm : EVM.State} (hstack : R.length + 22 ≤ 1024)
    (hm : AssetMemory mem ptr free assetOut) (hv : AssetValid assetOut)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 576 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17981⟩
      (ptr :: ⟨18165⟩ :: amount :: ⟨2425⟩ :: ret :: R) mem aw rdata σ k C) :
    ∃ result, QuoteAfterAsset v assetOut amount evm result ∧ QuoteRun v ee g s0 ret R result := by
  obtain ⟨result, ht, hr⟩ := cometQuoteAfterAssetBounded hstack hm hv hgap hbound hret hs h
  exact ⟨result, ht, hr.forget⟩

theorem cometQuoteInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {amount free ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State} (hstack : R.length + 22 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 832 + 768 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17965⟩
      (EVM.word asset.val :: amount :: ret :: R) mem aw rdata σ k C) :
    ∃ result, QuoteTrace v asset amount evm result ∧ QuoteRun v ee g s0 ret R result := by
  obtain ⟨result, ht, hr⟩ := cometQuoteInternalBounded hstack hfree hlo hbound hret hs h
  exact ⟨result, ht, hr.forget⟩

end Benchmarks.CompoundIII.Comet
