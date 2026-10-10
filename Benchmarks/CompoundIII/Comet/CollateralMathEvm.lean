import Benchmarks.CompoundIII.Comet.CollateralMath
import Benchmarks.CompoundIII.Comet.MulFactorEvm
import Benchmarks.CompoundIII.Comet.AssetMemory
import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_049
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_050
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def collateralMathPc (borrow : Bool) : UInt256 := if borrow then ⟨10554⟩ else ⟨11033⟩

def collateralScalePc (borrow : Bool) : UInt256 := if borrow then ⟨10567⟩ else ⟨11046⟩

theorem cometCollateralScale {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw price amount ptr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (out : ByteArray) (hstack : R.length + 12 ≤ 1024)
    (hs : (calldataWord out 96).toNat < 2^64)
    (hm : memLoad (ptr + UInt256.ofNat 96) mem = calldataWord out 96)
    (h : RD (deployedRuntime v) ee g s0 (collateralMathPc borrow)
      (price :: amount :: ⟨10579⟩ :: UInt256.ofNat (collateralFactorOffset borrow) ::
        ⟨10587⟩ :: ⟨10592⟩ :: ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (collateralScalePc borrow)
      (calldataWord out 96 :: price :: amount :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ :: ptr :: R)
      mem aw' rdata σ k' C' := by
  have hstep : ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2959⟩
      (calldataWord out 96 :: collateralScalePc borrow :: price :: amount :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ :: ptr :: R)
      mem aw' rdata σ k' C' := by
    cases borrow with
    | false =>
        have r1 := cometWithExtendedAssetList_block_11033 (immWords := wordsOf (immStore v))
          (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
        dsimp only [cometWithExtendedAssetList_block_11033_stack] at r1
        rw [hm] at r1
        exact ⟨_, _, _, r1⟩
    | true =>
        have r1 := cometWithExtendedAssetList_block_10554 (immWords := wordsOf (immStore v))
          (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
        dsimp only [cometWithExtendedAssetList_block_10554_stack] at r1
        rw [hm] at r1
        exact ⟨_, _, _, r1⟩
  obtain ⟨aw1, k1, C1, r1⟩ := hstep
  have r2 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by cases borrow <;>
      rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v] <;> jump_dest) r1
  dsimp only [cometWithExtendedAssetList_block_2959_stack] at r2
  rw [mask64Clean _ hs] at r2
  exact ⟨_, _, _, r2⟩

theorem cometCollateralMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw price amount ptr free ret a b : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (borrow : Bool) (out : ByteArray) (hstack : R.length + 17 ≤ 1024)
    (hn : amount.toNat < 2^128) (hc : AssetCanonical out) (hm : AssetMemory mem ptr free out)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (collateralMathPc borrow)
      (price :: amount :: ⟨10579⟩ :: UInt256.ofNat (collateralFactorOffset borrow) ::
        ⟨10587⟩ :: ⟨10592⟩ :: ptr :: ⟨10598⟩ :: ret :: a :: b :: ⟨1⟩ :: R)
      mem aw rdata σ k C) :
    (CollateralMathValid borrow amount price out ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
        (collateralValueWord borrow amount price out :: a :: b :: ⟨1⟩ :: R)
        mem aw' rdata σ k' C') ∨
      (¬ CollateralMathValid borrow amount price out ∧ RDrev (deployedRuntime v) g s0) := by
  have hs := hc.2.2.2.1
  have hf : (calldataWord out (collateralFactorOffset borrow)).toNat < 2^64 := by
    cases borrow
    · exact hc.2.2.2.2.2.1
    · exact hc.2.2.2.2.1
  have hfm : memLoad (ptr + UInt256.ofNat (collateralFactorOffset borrow)) mem =
      calldataWord out (collateralFactorOffset borrow) := by
    cases borrow
    · exact hm.words 5 (by decide)
    · exact hm.words 4 (by decide)
  obtain ⟨aw1, k1, C1, r1⟩ := cometCollateralScale borrow out
    (by simp only [List.length_cons]; omega) hs (hm.words 3 (by decide)) h
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft ⟨1⟩ (UInt256.ofNat 128)) ⟨1⟩) amount = amount := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 128) rfl hn
  have hmul : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11194⟩
      (amount :: price :: calldataWord out 96 :: ⟨10579⟩ ::
        UInt256.ofNat (collateralFactorOffset borrow) :: ⟨10587⟩ :: ⟨10592⟩ :: ptr ::
        ⟨10598⟩ :: ret :: a :: b :: ⟨1⟩ :: R) mem aw1 rdata σ k' C' := by
    cases borrow with
    | false =>
        have r2 := cometWithExtendedAssetList_block_11046 (immWords := wordsOf (immStore v))
          (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
        dsimp only [cometWithExtendedAssetList_block_11046_stack] at r2
        change RD _ _ _ _ _ (UInt256.land _ amount :: _) _ _ _ _ _ _ at r2
        rw [hmask] at r2
        exact ⟨_, _, r2⟩
    | true =>
        have r2 := cometWithExtendedAssetList_block_10567 (immWords := wordsOf (immStore v))
          (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
        dsimp only [cometWithExtendedAssetList_block_10567_stack] at r2
        simp only [collateralFactorOffset, if_true] at r2
        change RD _ _ _ _ _ (UInt256.land _ amount :: _) _ _ _ _ _ _ at r2
        rw [hmask] at r2
        exact ⟨_, _, r2⟩
  obtain ⟨k2, C2, r2⟩ := hmul
  have hprice := cometMulPrice (v := v) (by simp only [List.length_cons]; omega) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  by_cases hv1 : MulPriceValid amount price (calldataWord out 96)
  · rw [if_pos hv1] at hprice
    obtain ⟨k3, C3, r3⟩ := hprice
    have r4 := cometWithExtendedAssetList_block_10579 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    dsimp only [cometWithExtendedAssetList_block_10579_stack] at r4
    rw [hfm] at r4
    have r5 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    dsimp only [cometWithExtendedAssetList_block_2959_stack] at r5
    rw [mask64Clean _ hf] at r5
    have r6 := cometWithExtendedAssetList_block_10587 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    have r7 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
    dsimp only [cometWithExtendedAssetList_block_2959_stack] at r7
    rw [mask64Clean _ hf] at r7
    have r8 := cometWithExtendedAssetList_block_10592 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
    have hfactor := cometMulFactor (v := v) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
    by_cases hv2 : (mulPriceWord amount price (calldataWord out 96)).toNat *
        (calldataWord out (collateralFactorOffset borrow)).toNat < UInt256.size
    · rw [if_pos hv2] at hfactor
      obtain ⟨k9, C9, r9⟩ := hfactor
      have r10 := cometWithExtendedAssetList_block_10598 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r9
      by_cases hv3 : (collateralValueWord borrow amount price out).toNat < 2^255
      · refine Or.inl ⟨⟨hv1, hv2, hv3⟩, ?_⟩
        obtain ⟨k11, C11, r11⟩ := cometSigned256 (v := v)
          (by simp only [List.length_cons]; omega) hv3 hret r10
        exact ⟨_, _, _, r11⟩
      · refine Or.inr ⟨fun hv ↦ hv3 hv.2.2, ?_⟩
        exact cometSigned256_revert (v := v)
          (by simp only [List.length_cons]; omega) hv3 r10
    · refine Or.inr ⟨fun hv ↦ hv2 hv.2.1, ?_⟩
      rwa [if_neg hv2] at hfactor
  · refine Or.inr ⟨fun hv ↦ hv1 hv.1, ?_⟩
    rwa [if_neg hv1] at hprice

end Benchmarks.CompoundIII.Comet
