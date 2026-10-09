import Benchmarks.CompoundIII.Comet.AbsorbCollateralMathModel
import Benchmarks.CompoundIII.Comet.AbsorbCollateralFactorEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

attribute [local irreducible] mulPriceWord mulFactorWord

theorem cometAbsorbCollateralMathWords {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw price delta seized ptr scale factor : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024) (hn : seized.toNat < 2^128)
    (hs : scale.toNat < 2^64) (hf : factor.toNat < 2^64)
    (hms : memLoad (ptr + UInt256.ofNat 96) mem = scale)
    (hmf : memLoad (ptr + UInt256.ofNat 192) mem = factor)
    (h : RD (deployedRuntime v) ee g s0 ⟨17736⟩
      (price :: delta :: seized :: ptr :: R) mem aw rdata σ k C) :
    if AbsorbCollateralWordsValid delta seized price scale factor then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨17811⟩
        ((delta + mulFactorWord (mulPriceWord seized price scale) factor) :: seized ::
          mulPriceWord seized price scale :: R) mem aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_17736 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_17736_stack] at r1
  rw [hms] at r1
  have r2 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  dsimp only [cometWithExtendedAssetList_block_2959_stack] at r2
  rw [mask64Clean _ hs] at r2
  have r3 := cometWithExtendedAssetList_block_17750 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  dsimp only [cometWithExtendedAssetList_block_17750_stack] at r3
  rw [u256LandMaskCleanOfToNat seized _ (bits := 128) rfl hn] at r3
  have hprice := cometMulPrice (v := v) (n := seized) (p := price)
    (scale := scale) (by change R.length + 3 + 7 ≤ 1024; omega)
    hs (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  by_cases hv1 : MulPriceValid seized price scale
  · rw [if_pos hv1] at hprice
    obtain ⟨k4, C4, r4⟩ := hprice
    have hr := cometAbsorbCollateralFactor (v := v) hstack hf hmf r4
    by_cases hv2 : (mulPriceWord seized price scale).toNat * factor.toNat < UInt256.size ∧
        delta.toNat + (mulFactorWord (mulPriceWord seized price scale) factor).toNat < UInt256.size
    · rw [if_pos hv2] at hr
      rw [if_pos (show AbsorbCollateralWordsValid delta seized price scale factor from ⟨hv1, hv2⟩)]
      exact hr
    · rw [if_neg hv2] at hr
      rw [if_neg (fun hh : AbsorbCollateralWordsValid delta seized price scale factor ↦ hv2 hh.2)]
      exact hr
  · rw [if_neg hv1] at hprice
    rw [if_neg (fun hh : AbsorbCollateralWordsValid delta seized price scale factor ↦ hv1 hh.1)]
    exact hprice

theorem cometAbsorbCollateralMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata out : ByteArray}
    {aw price delta seized ptr free : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hn : seized.toNat < 2^128)
    (hc : AssetCanonical out) (hm : AssetMemory mem ptr free out)
    (h : RD (deployedRuntime v) ee g s0 ⟨17736⟩
      (price :: delta :: seized :: ptr :: R) mem aw rdata σ k C) :
    if AbsorbCollateralMathValid delta seized price out then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨17811⟩
        (absorbCollateralDelta delta seized price out :: seized ::
          absorbCollateralValue seized price out :: R) mem aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  exact cometAbsorbCollateralMathWords (v := v) hstack hn hc.2.2.2.1 hc.2.2.2.2.2.2.1
    (hm.words 3 (by decide)) (hm.words 6 (by decide)) h

end Benchmarks.CompoundIII.Comet
