import Benchmarks.CompoundIII.Comet.SupplyCollateralTotalEvm
import Benchmarks.CompoundIII.Comet.SupplyCollateralAfterTotalEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyCollateralAfterAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst asset : AccountAddress) (hstack : R.length + 30 ≤ 1024)
    (ha : amount.toNat < 2^128) (hv : AssetValid out)
    (hm : AssetMemory mem ptr free out) (hb : free.toNat + 64 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13861⟩
      (ptr :: EVM.word asset.val :: ⟨2^128-1⟩ :: amount :: EVM.word sender.val ::
        EVM.word dst.val :: ret :: R) mem aw out σ k C) :
    internalDynamicRun (deployedRuntime v) ee g s0 ret R
      (supplyCollateralOutcome evm dst asset amount out) := by
  obtain ⟨aw1, k1, C1, htotal, hasset, r1⟩ := cometSupplyCollateralRead (v := v) asset
    (by omega) hm hb hs h
  rcases cometSupplyCollateralTotal (v := v) asset (by omega) (low128_lt _) ha hv
      htotal hasset hm.lower hm.separate r1 with
    ⟨ht, hc, aw2, k2, C2, r2⟩ | ⟨hn, hr⟩
  · have ht' := htotal.writeTotal (supplyCollateralTotalNext evm asset amount)
    have ha' := hasset.preserve hm.lower (memoryPrefix_sparse_writeWord _ free.toNat
      (ptr.toNat + 32 * 8) (supplyCollateralTotalNext evm asset amount) (Or.inl hm.separate))
    exact cometSupplyCollateralAfterTotal sender dst asset hstack ha hv ht hc ht' ha'
      hm.lower (by have hlo := hm.lower; have hsep := hm.separate; omega) hret hs r2
  · have he : supplyCollateralPrefixOutcome evm dst asset amount out = .reverted := by
      by_cases ht : (withdrawCollateralTotal evm asset).toNat + amount.toNat < 2^128
      · have hc : ¬ (supplyCollateralTotalNext evm asset amount).toNat ≤
            (calldataWord out 224).toNat := fun hc ↦ hn ⟨ht, hc⟩
        simp only [supplyCollateralPrefixOutcome, if_pos ht, if_neg hc]
      · simp only [supplyCollateralPrefixOutcome, if_neg ht]
    simpa only [supplyCollateralOutcome, he, internalDynamicRun] using hr

end Benchmarks.CompoundIII.Comet
