import Benchmarks.CompoundIII.Comet.CollateralDebtRead
import Benchmarks.CompoundIII.Comet.CollateralDebtSource
import Benchmarks.CompoundIII.Comet.CollateralLoopEvm
import Benchmarks.CompoundIII.Comet.SignedMulPriceEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSignedMulPrice_outcome {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw m p scale ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hm : m.toNat ≤ 2^255)
    (hp : 0 < p.toNat) (hp' : p.toNat < 2^255) (hscale : scale.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11226⟩
      (UInt256.sub (UInt256.ofNat 0) m :: p :: scale :: ret :: R) mem aw rdata σ k C) :
    (signedDebtPriceValid m p scale ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (signedDebtPriceWord m p scale :: R) mem aw rdata σ k' C') ∨
      (¬ signedDebtPriceValid m p scale ∧ RDrev (deployedRuntime v) g s0) := by
  have hr := cometSignedMulPrice hstack hm hp hp' hscale hret h
  by_cases hv : signedDebtPriceValid m p scale
  · rw [if_pos hv] at hr
    exact Or.inl ⟨hv, hr⟩
  · rw [if_neg hv] at hr
    exact Or.inr ⟨hv, hr⟩

theorem cometCollateralLoopInit {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw liquidity assets reserved account ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 10 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (collateralLoopInitPc borrow)
      (liquidity :: reserved :: assets :: account :: ⟨0⟩ :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (collateralLoopPc borrow)
      (collateralLoopStack 0 assets reserved account v.numAssets liquidity ret R)
      mem aw rdata σ k' C' := by
  have hmask : UInt256.land v.numAssets (UInt256.ofNat 255) = v.numAssets :=
    lowByteClean v.numAssets_lt
  cases borrow with
  | false =>
      have r1 := cometWithExtendedAssetList_block_10869 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 9 ≤ 1024; omega) h
      simp only [cometWithExtendedAssetList_block_10869_stack,
        wordsOf_immStore_numAssets, wordOfInt_ofNat_toNat, hmask] at r1
      exact ⟨_, _, r1⟩
  | true =>
      have r1 := cometWithExtendedAssetList_block_10348 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 9 ≤ 1024; omega) h
      simp only [cometWithExtendedAssetList_block_10348_stack,
        wordsOf_immStore_numAssets, wordOfInt_ofNat_toNat, hmask] at r1
      exact ⟨_, _, r1⟩

theorem cometCollateralDebt {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free basic magnitude ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 35 ≤ 1024)
    (hmagnitude : magnitude.toNat ≤ 2^255)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨10259⟩
      (UInt256.sub (UInt256.ofNat 0) magnitude :: collateralLoopInitPc borrow ::
        userBasicFieldWord basic 3 :: userBasicFieldWord basic 2 ::
        EVM.word account.val :: ⟨0⟩ :: ret :: R) mem aw rdata σ k C) :
    ∃ result, CollateralDebtTrace v borrow account basic magnitude evm result ∧
      CollateralLoopRun v ee g s0 ret R (free.toNat + 160 + 928 * v.numAssets.toNat) result := by
  have r1 := cometWithExtendedAssetList_block_10259 (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_10259_stack,
    wordsOf_immStore_baseTokenPriceFeed] at r1
  obtain ⟨evm', σ', z, out, hc, hs', hh, hr⟩ := cometPriceInternal (v := v)
    v.baseTokenPriceFeed (by change R.length + 7 + 12 ≤ 1024; omega)
    hfree hlo hgap (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  have hh' : out.size < 2^255 := lt_trans hh (by decide)
  by_cases hp : z = true ∧ PriceValid out
  · rw [if_pos hp] at hr
    obtain ⟨rfl, hv⟩ := hp
    obtain ⟨aw2, k2, C2, r2⟩ := hr
    have r3 := cometWithExtendedAssetList_block_10300 (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [cometWithExtendedAssetList_block_10300_stack, wordsOf_immStore_baseScale,
      wordOfInt_ofNat_toNat] at r3
    have hscale : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
          (UInt256.ofNat 1)) v.baseScale = collateralBaseScale v := u256_land_comm _ _
    rw [hscale] at r3
    obtain ⟨hp0, hp1⟩ := pricePositive_bounds hv.2.2
    have hmath := cometSignedMulPrice_outcome (v := v)
      (by change R.length + 5 + 12 ≤ 1024; omega) hmagnitude hp0 hp1 (uintCastWord_lt _ _)
      (by cases borrow <;> rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest) r3
    rcases hmath with ⟨hm, k4, C4, r4⟩ | ⟨hm, hrev⟩
    · obtain ⟨k5, C5, r5⟩ := cometCollateralLoopInit borrow (by omega) r4
      have hfn : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
        uadd_word_ofNat_toNat free 160 (by change free.toNat + 160 < 2^256; omega)
      have hout : out.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
      have hmSize := priceReturnMemory_size hlo hgap hv.1 hout
      obtain ⟨result, ht, hrun⟩ := cometCollateralLoop borrow account hstack
        (packedUint_lt basic _ (by decide)) (packedUint_lt basic _ (by decide)) (by omega)
        (priceReturnMemory_free hlo hgap hv.1 hout) (by rw [hfn]; omega)
        (by rw [hmSize, hfn]; omega) (by rw [hmSize]; omega)
        (by rw [hfn]; omega) hret hs' r5
      simp only [Nat.sub_zero, hfn] at hrun
      exact ⟨result, .loop hc hh' hv hm ht, hrun⟩
    · exact ⟨none, .mathFailed hc hh' hv hm, hrev⟩
  · rw [if_neg hp] at hr
    exact ⟨none, .priceFailed hc hh' hp, hr⟩

end Benchmarks.CompoundIII.Comet
