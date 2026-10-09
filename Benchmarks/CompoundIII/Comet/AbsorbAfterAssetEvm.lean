import Benchmarks.CompoundIII.Comet.AbsorbAfterAssetModel
import Benchmarks.CompoundIII.Comet.AbsorbAssetSeizeEvm
import Benchmarks.CompoundIII.Comet.AbsorbCollateralPriceEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

attribute [local irreducible] absorbSeizeOutcome absorbCollateralMathDecidable
  absorbCollateralWordsDecidable

theorem cometAbsorbAfterAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata out : ByteArray}
    {aw ptr free absorber i assets reserved old principal price delta : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 25 ≤ 1024)
    (hm : AssetMemory mem ptr free out) (hc : AssetCanonical out)
    (hgap : free.toNat ≤ mem.size + 32) (hbound : free.toNat + 416 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17589⟩
      (ptr :: absorber :: EVM.word account.val :: i :: assets :: reserved :: old :: principal ::
        price :: EVM.word account.val :: delta :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbAfterAssetTrace account out delta evm result ∧
      internalValuePreservingRun (deployedRuntime v) ee g s0 mem free 160 ⟨17567⟩
        (fun p ↦ i :: assets :: reserved :: old :: principal :: price :: EVM.word account.val ::
          absorbCollateralDelta delta
            (withdrawCollateralBalance evm account (absorbAssetAddress out)) p out :: R) result := by
  let asset := absorbAssetAddress out
  have hasset : memLoad (ptr + UInt256.ofNat 32) mem = EVM.word asset.val := by
    rw [hm.words 1 (by decide)]
    exact (addressWord_eq_ofNat_address hc.2.1).symm
  have hr := cometAbsorbAssetSeize (v := v) account asset (by omega) hasset hs h
  cases he : absorbSeizeOutcome evm account asset with
  | reverted =>
      rw [he] at hr
      exact ⟨.reverted, AbsorbAfterAssetTrace.seizeReverted he, hr⟩
  | staticViolation =>
      rw [he] at hr
      exact ⟨.staticViolation, AbsorbAfterAssetTrace.seizeStatic he, hr⟩
  | ok seizedState =>
      rw [he] at hr
      obtain ⟨σ1, aw1, k1, C1, hs1, r1⟩ := hr
      let mem1 := absorbSeizeMemory (userCollateralMemory mem account asset) account asset
      have hm1 := (hm.userCollateral account asset).afterSeize account asset
      have hmem : 64 ≤ mem.size := by have hl := hm.lower; have hs := hm.present; omega
      have hsize : mem1.size = mem.size := by
        dsimp only [mem1]
        rw [absorbSeizeMemory_size account asset
          (by rw [userCollateralMemory_size account asset hmem]; exact hmem),
          userCollateralMemory_size account asset hmem]
      have hprefix : MemoryPrefix mem mem1 free.toNat :=
        (userCollateralMemory_prefix mem account asset free.toNat).trans
          (absorbSeizeMemory_prefix _ account asset free.toNat)
      have hperm : ee.perm = true := by
        rw [← hs.env]
        exact absorbSeizeOutcome_ok_perm he
      obtain ⟨result, ht, hr⟩ := cometAbsorbCollateralPrice (v := v)
        (free := free) (ptr := ptr) (assetOut := out) hstack (low128_lt _) hm1 hc
        (by change free.toNat ≤ mem1.size + 32; rw [hsize]; exact hgap)
        hbound hperm hs1 r1
      refine ⟨InternalValueOutcome.ofOption result, AbsorbAfterAssetTrace.priced he ht, ?_⟩
      cases result with
      | none => exact hr
      | some r =>
          obtain ⟨evm', p⟩ := r
          obtain ⟨σ2, mem2, free2, aw2, data2, k2, C2, hs2, hf2, hm2, hz2, hp2, r2⟩ := hr
          exact ⟨σ2, mem2, free2, aw2, data2, k2, C2, hs2, hf2, hm2, hz2,
            hprefix.trans hp2, r2⟩

end Benchmarks.CompoundIII.Comet
