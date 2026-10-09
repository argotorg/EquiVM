import Benchmarks.CompoundIII.Comet.QuoteModel
import Benchmarks.CompoundIII.Comet.AssetMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_080
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_081

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000


theorem cometQuoteDiscountMultiplications {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {price ptr x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hsub : (calldataWord out 192).toNat ≤ quoteFactorScale.toNat)
    (h : RD (deployedRuntime v) ee g s0 ⟨7799⟩
      (v.storeFrontPriceFactor :: UInt256.sub quoteFactorScale (calldataWord out 192) ::
        ⟨18095⟩ :: quoteFactorScale :: price :: ⟨18112⟩ :: quoteFactorScale :: x1 :: x2 ::
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
        ptr :: R) mem aw rdata σ k C) :
    (QuoteDiscountValid v out price ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨18112⟩
        (UInt256.mul price (UInt256.sub quoteFactorScale (quoteDiscountFactor v out)) ::
          quoteFactorScale :: x1 :: x2 ::
          UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
          ptr :: R) mem aw' rdata σ k' C') ∨
    (¬ QuoteDiscountValid v out price ∧ RDrev (deployedRuntime v) g s0) := by
  apply Classical.byCases (p := v.storeFrontPriceFactor.toNat *
    (UInt256.sub quoteFactorScale (calldataWord out 192)).toNat < UInt256.size)
  all_goals intro hmul
  · obtain ⟨k3, C3, r3⟩ := cometCheckedMul (v := v)
      (x := v.storeFrontPriceFactor)
      (y := UInt256.sub quoteFactorScale (calldataWord out 192)) (ret := ⟨18095⟩)
      (R := quoteFactorScale :: price :: ⟨18112⟩ :: quoteFactorScale :: x1 :: x2 ::
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
        ptr :: R) (by simp only [List.length_cons]; omega)
      hmul (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
    apply Classical.byCases (p := (quoteDiscountFactor v out).toNat ≤ quoteFactorScale.toNat)
    all_goals intro hsub2
    · have r4 := cometWithExtendedAssetList_block_18095_fallthrough
        (immWords := wordsOf (immStore v))
        (x0 := UInt256.mul v.storeFrontPriceFactor
          (UInt256.sub quoteFactorScale (calldataWord out 192))) (x1 := quoteFactorScale)
        (by simp only [List.length_cons]; omega) (ult_zero hsub2) r3
      have r5 := cometWithExtendedAssetList_block_18104
        (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      change RD _ _ _ _ _ (price :: UInt256.sub quoteFactorScale (quoteDiscountFactor v out) ::
        ⟨18112⟩ :: quoteFactorScale :: x1 :: x2 :: _ :: ptr :: R) _ _ _ _ _ _ at r5
      apply Classical.byCases (p := price.toNat *
        (UInt256.sub quoteFactorScale (quoteDiscountFactor v out)).toNat < UInt256.size)
      all_goals intro hmul2
      · left
        refine ⟨show QuoteDiscountValid v out price from ⟨hsub, hmul, hsub2, hmul2⟩, ?_⟩
        obtain ⟨k6, C6, r6⟩ := cometCheckedMul (v := v)
          (x := price) (y := UInt256.sub quoteFactorScale (quoteDiscountFactor v out))
          (ret := ⟨18112⟩)
          (by simp only [List.length_cons]; omega) hmul2
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
        exact ⟨_, _, _, r6⟩
      · right; refine ⟨show ¬ QuoteDiscountValid v out price from fun h ↦ hmul2 h.2.2.2, ?_⟩
        exact cometCheckedMul_revert (v := v) (by simp only [List.length_cons]; omega)
          (le_of_not_gt hmul2) r5
    · right; refine ⟨show ¬ QuoteDiscountValid v out price from fun h ↦ hsub2 h.2.2.1, ?_⟩
      have r4 := cometWithExtendedAssetList_block_18095_taken
        (immWords := wordsOf (immStore v))
        (x0 := UInt256.mul v.storeFrontPriceFactor
          (UInt256.sub quoteFactorScale (calldataWord out 192))) (x1 := quoteFactorScale)
        (by simp only [List.length_cons]; omega) (by
          change UInt256.lt quoteFactorScale (quoteDiscountFactor v out) ≠ ⟨0⟩
          rw [ult_one (Nat.lt_of_not_ge hsub2)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      have r5 := cometWithExtendedAssetList_block_18226
        (immWords := wordsOf (immStore v))
        (by simp only [cometWithExtendedAssetList_block_18095_taken_stack, List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      exact cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
        (by simp only [cometWithExtendedAssetList_block_18226_stack,
          cometWithExtendedAssetList_block_18095_taken_stack, List.length_cons]; omega) r5
  · right; refine ⟨show ¬ QuoteDiscountValid v out price from fun h ↦ hmul h.2.1, ?_⟩
    exact cometCheckedMul_revert (v := v) (by simp only [List.length_cons]; omega)
      (le_of_not_gt hmul) h

theorem cometQuoteDiscount {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {price ptr free x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hm : AssetMemory mem ptr free out) (hv : AssetValid out)
    (h : RD (deployedRuntime v) ee g s0 ⟨18010⟩
      (price :: x1 :: x2 :: ⟨18112⟩ :: ptr :: R) mem aw rdata σ k C) :
    (QuoteDiscountValid v out price ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨18112⟩
        (UInt256.mul price (UInt256.sub quoteFactorScale (quoteDiscountFactor v out)) ::
          quoteFactorScale :: x1 :: x2 ::
          UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
          ptr :: R) mem aw' rdata σ k' C') ∨
    (¬ QuoteDiscountValid v out price ∧ RDrev (deployedRuntime v) g s0) := by
  classical
  have hl : memLoad (ptr + UInt256.ofNat 192) mem = calldataWord out 192 :=
    hm.words 6 (by decide)
  have hmask := mask64Clean (calldataWord out 192) hv.2.2.2.2.2.2.2.1
  by_cases hsub : (calldataWord out 192).toNat ≤ quoteFactorScale.toNat
  · have r1 := cometWithExtendedAssetList_block_18010_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hl, hmask]; exact ult_zero hsub) h
    simp only [cometWithExtendedAssetList_block_18010_fallthrough_stack, hl, hmask] at r1
    have r2 := cometWithExtendedAssetList_block_18054 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hd : (UInt256.sub quoteFactorScale (calldataWord out 192)).toNat < 2^64 := by
      rw [usub_toNat hsub]
      have hk : quoteFactorScale.toNat < 2^64 := by decide
      omega
    have hmask2 : UInt256.land (UInt256.sub quoteFactorScale (calldataWord out 192))
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) = UInt256.sub quoteFactorScale (calldataWord out 192) := by
      rw [u256_land_comm]
      exact mask64Clean _ hd
    simp only [cometWithExtendedAssetList_block_18054_stack, wordsOf_immStore_storeFrontPriceFactor,
      wordOfInt_ofNat_toNat,
      show UInt256.ofNat 1000000000000000000 = quoteFactorScale from rfl, hmask2] at r2
    exact cometQuoteDiscountMultiplications (v := v) (out := out)
      (price := price) (ptr := ptr) (x1 := x1) (x2 := x2) (R := R) hstack hsub r2
  · right; refine ⟨show ¬ QuoteDiscountValid v out price from fun h ↦ hsub h.1, ?_⟩
    have r1 := cometWithExtendedAssetList_block_18010_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by
        rw [hl, hmask]
        change UInt256.lt quoteFactorScale (calldataWord out 192) ≠ ⟨0⟩
        rw [ult_one (Nat.lt_of_not_ge hsub)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_18239
          (immWords := wordsOf (immStore v))
      (by simp only [cometWithExtendedAssetList_block_18010_taken_stack, List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
      (by simp only [cometWithExtendedAssetList_block_18239_stack,
        cometWithExtendedAssetList_block_18010_taken_stack, List.length_cons]; omega) r2

end Benchmarks.CompoundIII.Comet
