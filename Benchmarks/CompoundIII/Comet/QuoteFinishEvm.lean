import Benchmarks.CompoundIII.Comet.QuoteTrace
import Benchmarks.CompoundIII.Comet.QuoteDiscountEvm
import Benchmarks.CompoundIII.Comet.QuoteResultEvm
import Benchmarks.CompoundIII.Comet.PriceInternal
import Benchmarks.CompoundIII.Comet.PriceAssetMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def QuoteRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret : UInt256) (R : List UInt256)
    (result : Option (EVM.State × UInt256)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', value) => ∃ σ' mem aw rdata k C, SourceState s0 ee σ' evm' ∧
      RD (deployedRuntime v) ee g s0 ret (value :: R) mem aw rdata σ' k C

-- GENERALIZES QuoteRun with the allocation facts needed by a caller that continues execution.
def QuoteRunBounded (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret : UInt256) (R : List UInt256) (limit : Nat)
    (result : Option (EVM.State × UInt256)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', value) => ∃ σ' mem free aw rdata k C, SourceState s0 ee σ' evm' ∧
      memLoad ⟨64⟩ mem = free ∧ 96 ≤ free.toNat ∧ free.toNat ≤ limit ∧ free.toNat ≤ mem.size ∧
      RD (deployedRuntime v) ee g s0 ret (value :: R) mem aw rdata σ' k C

theorem QuoteRunBounded.forget {v ee g s0 ret R limit result}
    (h : QuoteRunBounded v ee g s0 ret R limit result) : QuoteRun v ee g s0 ret R result := by
  cases result with
  | none => exact h
  | some pair =>
    obtain ⟨evm', value⟩ := pair
    obtain ⟨σ', mem, free, aw, rdata, k, C, hs, _, _, _, _, hr⟩ := h
    exact ⟨σ', mem, aw, rdata, k, C, hs, hr⟩

theorem QuoteRunBounded.mono {v ee g s0 ret R limit limit' result}
    (h : QuoteRunBounded v ee g s0 ret R limit result) (hle : limit ≤ limit') :
    QuoteRunBounded v ee g s0 ret R limit' result := by
  cases result with
  | none => exact h
  | some pair =>
    obtain ⟨evm', value⟩ := pair
    obtain ⟨σ', mem, free, aw, rdata, k, C, hs, hf, hlo, hb, hm, hr⟩ := h
    exact ⟨σ', mem, free, aw, rdata, k, C, hs, hf, hlo, hb.trans hle, hm, hr⟩

theorem cometQuoteFinishBounded {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata assetOut : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {price amount ptr free ret : UInt256} {R : List UInt256}
    {evm : EVM.State} (hstack : R.length + 22 ≤ 1024)
    (hm : AssetMemory mem ptr free assetOut) (hv : AssetValid assetOut)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 416 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨18010⟩
      (price :: ⟨18155⟩ :: ⟨96⟩ :: ⟨18112⟩ :: ptr :: ⟨18165⟩ :: amount :: ⟨2425⟩ :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, QuoteFinish v assetOut amount price evm result ∧ QuoteRunBounded v ee g s0 ret R (free.toNat + 160) result := by
  have hr := cometQuoteDiscount (v := v) (out := assetOut)
    (by change R.length + 4 + 17 ≤ 1024; omega) hm hv h
  rcases hr with ⟨hd, aw1, k1, C1, r1⟩ | ⟨hd, hr⟩
  · have r2 := cometWithExtendedAssetList_block_18112 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 10 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [cometWithExtendedAssetList_block_18112_stack,
      wordsOf_immStore_baseTokenPriceFeed] at r2
    have hlo : 96 ≤ free.toNat := by have ha := hm.lower; have hb := hm.separate; omega
    obtain ⟨evm', σ', z, out, hc, hs', hh, hr⟩ := cometPriceInternal (v := v) v.baseTokenPriceFeed
      (by change R.length + 9 + 12 ≤ 1024; omega) hm.freeWord hlo hgap (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
    have hh' : out.size < 2^255 := lt_trans hh (by decide)
    by_cases hp : z = true ∧ PriceValid out
    · rw [if_pos hp] at hr
      obtain ⟨rfl, hvp⟩ := hp
      obtain ⟨aw3, k3, C3, r3⟩ := hr
      have hm' := hm.afterPrice hgap (by change free.toNat + 416 < 2^256; omega) hvp.1
        (lt_trans hh (by change 2^138 < 2^256; decide))
      have hr := cometQuoteResult (v := v)
        (discounted := quoteDiscountedPrice v assetOut price) (by omega) hm' hv hret r3
      have ht := QuoteFinish.result (amount := amount) hd hc hh' hvp
      rcases hr with ⟨hq, aw4, k4, C4, r4⟩ | ⟨hq, hr⟩
      · rw [if_pos hq] at ht
        have hfree : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
          uadd_word_ofNat_toNat free 160 (by change free.toNat + 160 < 2^256; omega)
        refine ⟨_, ht, σ', _, free + ⟨160⟩, aw4, out, k4, C4, hs', hm'.freeWord,
          ?_, ?_, ?_, r4⟩
        · rw [hfree]; omega
        · rw [hfree]
        · rw [hfree, priceReturnMemory_size hlo hgap hvp.1
            (lt_trans hh (by change 2^138 < 2^256; decide))]
          omega
      · rw [if_neg hq] at ht
        exact ⟨none, ht, hr⟩
    · rw [if_neg hp] at hr
      exact ⟨none, QuoteFinish.priceFailed hd hc hh' hp, hr⟩
  · exact ⟨none, QuoteFinish.discountFailed hd, hr⟩


theorem cometQuoteFinish {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata assetOut : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {price amount ptr free ret : UInt256} {R : List UInt256}
    {evm : EVM.State} (hstack : R.length + 22 ≤ 1024)
    (hm : AssetMemory mem ptr free assetOut) (hv : AssetValid assetOut)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 416 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨18010⟩
      (price :: ⟨18155⟩ :: ⟨96⟩ :: ⟨18112⟩ :: ptr :: ⟨18165⟩ :: amount :: ⟨2425⟩ :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, QuoteFinish v assetOut amount price evm result ∧ QuoteRun v ee g s0 ret R result := by
  obtain ⟨result, ht, hr⟩ := cometQuoteFinishBounded hstack hm hv hgap hbound hret hs h
  exact ⟨result, ht, hr.forget⟩

end Benchmarks.CompoundIII.Comet
