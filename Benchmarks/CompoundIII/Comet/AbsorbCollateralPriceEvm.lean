import Benchmarks.CompoundIII.Comet.AbsorbCollateralPriceModel
import Benchmarks.CompoundIII.Comet.AbsorbCollateralMathEvm
import Benchmarks.CompoundIII.Comet.PriceInternal
import Benchmarks.CompoundIII.Comet.PriceAssetMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

attribute [local irreducible] absorbCollateralMathDecidable absorbCollateralWordsDecidable

def AbsorbCollateralPricedRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (before : ByteArray) (free delta seized : UInt256)
    (assetOut : ByteArray) (R : List UInt256) : Option (State × UInt256) → Prop
  | none => RDrev (deployedRuntime v) g s0
  | some (evm, price) => ∃ σ mem free' aw data k C,
      SourceState s0 ee σ evm ∧ free'.toNat = free.toNat + 160 ∧
      memLoad ⟨64⟩ mem = free' ∧ free'.toNat ≤ mem.size ∧
      MemoryPrefix before mem free.toNat ∧
      RD (deployedRuntime v) ee g s0 ⟨17811⟩
        (absorbCollateralDelta delta seized price assetOut :: seized ::
          absorbCollateralValue seized price assetOut :: R) mem aw data σ k C

theorem cometAbsorbCollateralPriceMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata assetOut : ByteArray}
    {aw ptr free delta seized : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hn : seized.toNat < 2^128)
    (hm : AssetMemory mem ptr free assetOut) (hc : AssetCanonical assetOut)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 416 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17713⟩
      (delta :: seized :: ptr :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbCollateralPriceTrace assetOut delta seized evm result ∧
      AbsorbCollateralPricedRun v ee g s0 mem free delta seized assetOut R result := by
  have r1 := cometWithExtendedAssetList_block_17713 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_17713_stack] at r1
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (calldataWord assetOut 64) = calldataWord assetOut 64 := solcAddrMask_clean_left hc.2.2.1
  rw [hm.words 2 (by decide), hmask,
    ← addressWord_eq_ofNat_address hc.2.2.1] at r1
  have hlo : 96 ≤ free.toNat := by have hl := hm.lower; have hs := hm.separate; omega
  obtain ⟨evm', σ', z, priceOut, hcall, hs', hh, hr⟩ := cometPriceInternal (v := v)
    (AccountAddress.ofNat (calldataWord assetOut 64).toNat)
    (by change R.length + 3 + 12 ≤ 1024; omega) hm.freeWord hlo hgap (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  have hh' : priceOut.size < 2^255 := lt_trans hh (by decide)
  by_cases hp : z = true ∧ PriceValid priceOut
  · rw [if_pos hp] at hr
    obtain ⟨rfl, hvp⟩ := hp
    obtain ⟨aw2, k2, C2, r2⟩ := hr
    have hhi : priceOut.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
    have hm2 := hm.afterPrice hgap (by change free.toNat + 416 < 2^256; omega) hvp.1 hhi
    have hmath := cometAbsorbCollateralMath (v := v) (R := R) (ptr := ptr)
      (free := free + ⟨160⟩) (delta := delta) (seized := seized)
      (price := calldataWord priceOut 32) (out := assetOut) (by omega) hn hc hm2 r2
    have ht := AbsorbCollateralPriceTrace.result (assetOut := assetOut)
      (delta := delta) (seized := seized) hcall hh' hvp
    by_cases hvalid : AbsorbCollateralMathValid delta seized (calldataWord priceOut 32) assetOut
    · rw [if_pos hvalid] at hmath ht
      obtain ⟨aw3, k3, C3, r3⟩ := hmath
      have hfree : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
        uadd_word_ofNat_toNat free 160 (by change free.toNat + 160 < 2^256; omega)
      refine ⟨_, ht, σ', _, free + ⟨160⟩, aw3, priceOut, k3, C3, hs', hfree,
        hm2.freeWord, ?_, priceReturnMemory_prefix hvp.1 hhi, r3⟩
      rw [priceReturnMemory_size hlo hgap hvp.1 hhi, hfree]
      omega
    · rw [if_neg hvalid] at hmath ht
      exact ⟨none, ht, hmath⟩
  · rw [if_neg hp] at hr
    exact ⟨none, AbsorbCollateralPriceTrace.priceFailed hcall hh' hp, hr⟩

def AbsorbCollateralPriceRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (before : ByteArray) (free delta seized : UInt256)
    (assetOut : ByteArray) (i assets reserved old principal basePrice account : UInt256)
    (R : List UInt256) : Option (State × UInt256) → Prop
  | none => RDrev (deployedRuntime v) g s0
  | some (evm, price) => ∃ σ mem free' aw data k C,
      SourceState s0 ee σ evm ∧ free'.toNat = free.toNat + 160 ∧
      memLoad ⟨64⟩ mem = free' ∧ free'.toNat ≤ mem.size ∧
      MemoryPrefix before mem free.toNat ∧
      RD (deployedRuntime v) ee g s0 ⟨17567⟩
        (i :: assets :: reserved :: old :: principal :: basePrice :: account ::
          absorbCollateralDelta delta seized price assetOut :: R) mem aw data σ k C

theorem cometAbsorbCollateralPrice {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata assetOut : ByteArray}
    {aw ptr free delta seized absorber account asset i assets reserved old principal basePrice : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 25 ≤ 1024) (hn : seized.toNat < 2^128)
    (hm : AssetMemory mem ptr free assetOut) (hc : AssetCanonical assetOut)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 416 < 2^64)
    (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17713⟩
      (delta :: seized :: ptr :: absorber :: account :: i :: assets :: reserved :: old ::
        principal :: basePrice :: account :: asset :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbCollateralPriceTrace assetOut delta seized evm result ∧
      AbsorbCollateralPriceRun v ee g s0 mem free delta seized assetOut
        i assets reserved old principal basePrice account R result := by
  obtain ⟨result, ht, hr⟩ := cometAbsorbCollateralPriceMath (v := v)
    (by change R.length + 10 + 15 ≤ 1024; omega) hn hm hc hgap hbound hs h
  refine ⟨result, ht, ?_⟩
  cases result with
  | none => exact hr
  | some r =>
      obtain ⟨evm', price⟩ := r
      obtain ⟨σ1, mem1, free1, aw1, data1, k1, C1, hs1, hf1, hm1, hsize, hprefix, r1⟩ := hr
      have hb : free1.toNat + 32 < UInt256.size := by
        rw [hf1]; change free.toNat + 160 + 32 < 2^256; omega
      obtain ⟨aw2, k2, C2, r2⟩ := cometAbsorbCollateralEvent (v := v)
        (by omega) hperm hm1 hb hn r1
      have hlo : 96 ≤ free1.toNat := by
        have hl := hm.lower; have hs := hm.separate; omega
      have hmem := absorbDebtEventMemory_free (paid := seized)
        (value := absorbCollateralValue seized price assetOut) hm1 hlo hsize
      exact ⟨σ1, _, free1, aw2, data1, k2, C2, hs1, hf1, hmem.1,
        le_trans hsize hmem.2,
        hprefix.trans ((pairEventPrefix _ _ _ _).mono (by omega)), r2⟩

end Benchmarks.CompoundIII.Comet
