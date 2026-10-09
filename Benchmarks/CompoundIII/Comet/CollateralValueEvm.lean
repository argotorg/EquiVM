import Benchmarks.CompoundIII.Comet.CollateralReadEvm
import Benchmarks.CompoundIII.Comet.PriceInternal
import Benchmarks.CompoundIII.Comet.PriceAssetMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def CollateralValueRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (borrow : Bool) (ret a b : UInt256) (R : List UInt256)
    (free : UInt256) (growth : Nat) (result : Option (EVM.State × CollateralValueData)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', d) => ∃ σ' mem' free' aw' rdata' k' C',
      SourceState s0 ee σ' evm' ∧ free'.toNat = free.toNat + growth ∧
      memLoad ⟨64⟩ mem' = free' ∧ free'.toNat ≤ mem'.size + 32 ∧
      RD (deployedRuntime v) ee g s0 ret (d.value borrow :: a :: b :: ⟨1⟩ :: R)
        mem' aw' rdata' σ' k' C'

theorem cometCollateralPriceMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata out : ByteArray}
    {aw ptr free amount ret a b : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 24 ≤ 1024)
    (hn : amount.toNat < 2^128) (hm : AssetMemory mem ptr free out) (hv : AssetValid out)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 416 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (collateralPricePc borrow)
      (amount :: ⟨10579⟩ :: UInt256.ofNat (collateralFactorOffset borrow) ::
        ⟨10587⟩ :: ⟨10592⟩ :: ptr :: ⟨10598⟩ :: ret :: a :: b :: ⟨1⟩ :: R)
      mem aw rdata σ k C) :
    ∃ result, CollateralAfterAsset borrow out amount evm result ∧
      CollateralValueRun v ee g s0 borrow ret a b R free 160 result := by
  obtain ⟨aw2, k2, C2, r2⟩ := cometCollateralPriceStart borrow
    (by change R.length + 5 + 11 ≤ 1024; omega) hm hv.2 h
  have hlo : 96 ≤ free.toNat := by have ha := hm.lower; have hb := hm.separate; omega
  obtain ⟨evm', σ', z, priceOut, hcall, hs', hh, hr⟩ := cometPriceInternal (v := v)
    (AccountAddress.ofNat (calldataWord out 64).toNat)
    (by change R.length + 11 + 12 ≤ 1024; omega) hm.freeWord hlo hgap (by omega)
    (by cases borrow <;> rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest)
    hs r2
  have hh' : priceOut.size < 2^255 := lt_trans hh (by decide)
  by_cases hp : z = true ∧ PriceValid priceOut
  · rw [if_pos hp] at hr
    obtain ⟨rfl, hvp⟩ := hp
    obtain ⟨aw3, k3, C3, r3⟩ := hr
    have hm3 := hm.afterPrice hgap (by change free.toNat + 416 < 2^256; omega)
      hvp.1 (lt_trans hh (by change 2^138 < 2^256; decide))
    have hmath := cometCollateralMath (v := v) (R := R) (ptr := ptr)
      (free := free + ⟨160⟩) (ret := ret) (a := a) (b := b)
      (amount := amount) (price := calldataWord priceOut 32)
      borrow out (by omega)
      hn hv.2 hm3 hret r3
    have ht := CollateralAfterAsset.result (borrow := borrow)
      (amount := amount) hcall hh' hvp
    rcases hmath with ⟨hvalid, aw4, k4, C4, r4⟩ | ⟨hvalid, hrev⟩
    · rw [if_pos hvalid] at ht
      have hfree : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
        uadd_word_ofNat_toNat free 160 (by change free.toNat + 160 < 2^256; omega)
      refine ⟨_, ht, σ', _, free + ⟨160⟩, aw4, priceOut, k4, C4,
        hs', hfree, hm3.freeWord, ?_, r4⟩
      rw [priceReturnMemory_size hlo hgap hvp.1
        (lt_trans hh (by change 2^138 < 2^256; decide)), hfree]
      omega
    · rw [if_neg hvalid] at ht
      exact ⟨none, ht, hrev⟩
  · rw [if_neg hp] at hr
    exact ⟨none, CollateralAfterAsset.priceFailed hcall hh' hp, hr⟩

theorem cometCollateralAfterAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata out : ByteArray}
    {aw ptr free ret a b : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 24 ≤ 1024)
    (hm : AssetMemory mem ptr free out) (hv : AssetValid out)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 416 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10490⟩
      (ptr :: ⟨10498⟩ :: ⟨10518⟩ :: collateralPricePc borrow :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ ::
        EVM.word account.val :: ⟨10598⟩ :: ret :: a :: b :: ⟨1⟩ :: R)
      mem aw rdata σ k C) :
    ∃ result, CollateralAfterAsset borrow out (collateralBalanceWord evm account out)
      evm result ∧ CollateralValueRun v ee g s0 borrow ret a b R free 160 result := by
  obtain ⟨aw1, k1, C1, r1⟩ := cometCollateralBalanceRead borrow account
    (by change R.length + 5 + 16 ≤ 1024; omega) hm hv.2 hs h
  let mem1 := collateralReadMemory mem account out
  have hm1 := hm.afterCollateralRead account
  have hsize : mem1.size = mem.size := collateralReadMemory_size account
    (by have ha := hm.lower; have hb := hm.present; omega)
  have hgap1 : free.toNat ≤ mem1.size + 32 := by rw [hsize]; exact hgap
  exact cometCollateralPriceMath borrow hstack (low128_lt _) hm1 hv
    hgap1 hbound hs hret r1

theorem cometCollateralValue {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw i free ret a b : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 26 ≤ 1024)
    (hi : i.toNat < 256) (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 1184 < 2^64) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7179⟩
      (i :: ⟨10490⟩ :: ⟨10498⟩ :: ⟨10518⟩ :: collateralPricePc borrow :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ ::
        EVM.word account.val :: ⟨10598⟩ :: ret :: a :: b :: ⟨1⟩ :: R)
      mem aw rdata σ k C) :
    ∃ result, CollateralValueTrace v borrow account i evm result ∧
      CollateralValueRun v ee g s0 borrow ret a b R free 928 result := by
  obtain ⟨evm', σ', z, out, hcall, hs', hh, hr⟩ := cometAssetInternal (v := v)
    (by change R.length + 13 + 13 ≤ 1024; omega) hi hfree hlo (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs h
  have hh' : out.size < 2^255 := lt_trans hh (by decide)
  by_cases hp : z = true ∧ AssetValid out
  · rw [if_pos hp] at hr
    obtain ⟨rfl, hva⟩ := hp
    obtain ⟨aw1, k1, C1, r1⟩ := hr
    have hb : free.toNat + 1184 < UInt256.size := by change free.toNat + 1184 < 2^256; omega
    have h1 : (free + (⟨256⟩ : UInt256)).toNat = free.toNat + 256 :=
      uadd_word_ofNat_toNat free 256 (by omega)
    have h2 : ((free + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat = free.toNat + 512 := by
      have ha : ((free + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat =
          (free + (⟨256⟩ : UInt256)).toNat + 256 :=
        uadd_word_ofNat_toNat _ 256 (by rw [h1]; omega)
      omega
    have h3 : (((free + (⟨256⟩ : UInt256)) + ⟨256⟩) + ⟨256⟩).toNat =
        free.toNat + 768 := by
      have ha : (((free + (⟨256⟩ : UInt256)) + ⟨256⟩) + ⟨256⟩).toNat =
          ((free + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat + 256 :=
        uadd_word_ofNat_toNat _ 256 (by rw [h2]; omega)
      omega
    have hm := assetInternalMemory_spec (mem := mem) (i := i) hlo (by omega) hva.1
      (lt_trans hh (by change 2^138 < 2^256; decide))
    have hmem : (assetInternalMemory mem free i out).size =
        max mem.size (free.toNat + 768) := by
      rw [assetInternalMemory, assetResultMemory_size (by rw [h1]; omega)
        (by rw [h1]; omega) hva.1 (lt_trans hh (by change 2^138 < 2^256; decide)),
        assetZeroMemory_size (by omega) (by omega), h1]
      omega
    obtain ⟨result, ht, hr⟩ := cometCollateralAfterAsset borrow account (by omega) hm hva
      (by rw [hmem, h3]; omega) (by rw [h3]; omega) hs' hret r1
    refine ⟨result, CollateralValueTrace.assetOk hcall hh' hva ht, ?_⟩
    cases result with
    | none => exact hr
    | some r =>
        obtain ⟨evm'', d⟩ := r
        obtain ⟨σ2, mem2, free2, aw2, data2, k2, C2, hs2, hf2, hm2, hg2, r2⟩ := hr
        exact ⟨σ2, mem2, free2, aw2, data2, k2, C2, hs2, by rw [h3] at hf2; omega,
          hm2, hg2, r2⟩
  · rw [if_neg hp] at hr
    exact ⟨none, CollateralValueTrace.assetFailed hcall hh' hp, hr⟩

end Benchmarks.CompoundIII.Comet
