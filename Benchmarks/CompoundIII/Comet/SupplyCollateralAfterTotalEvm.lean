import Benchmarks.CompoundIII.Comet.SupplyCollateralBalanceEvm
import Benchmarks.CompoundIII.Comet.SupplyCollateralWrite
import Benchmarks.CompoundIII.Comet.SupplyCollateralMemberEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyCollateralAfterTotal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem out : ByteArray}
    {aw ptr totalPtr amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (sender dst asset : AccountAddress) (hstack : R.length + 30 ≤ 1024)
    (ha : amount.toNat < 2^128) (hv : AssetValid out)
    (ht : (withdrawCollateralTotal evm asset).toNat + amount.toNat < 2^128)
    (hc : (supplyCollateralTotalNext evm asset amount).toNat ≤ (calldataWord out 224).toNat)
    (hm : TotalsCollateralMemory mem totalPtr (supplyCollateralTotalNext evm asset amount)
      (supplyCollateralReserved evm asset))
    (hw : WordStructMemory mem ptr 8 (fun i ↦ calldataWord out (32 * i)))
    (hlo : 96 ≤ ptr.toNat) (htlo : 96 ≤ totalPtr.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨13952⟩
      (EVM.word asset.val :: ptr :: totalPtr :: amount :: EVM.word sender.val ::
        EVM.word dst.val :: ret :: R) mem aw out σ k C) :
    internalDynamicRun (deployedRuntime v) ee g s0 ret R
      (supplyCollateralOutcome evm dst asset amount out) := by
  simp only [supplyCollateralOutcome, supplyCollateralPrefixOutcome, if_pos ht, if_pos hc]
  rcases cometSupplyCollateralBalance sender dst asset (by omega) ha hs h with
    ⟨hb, aw1, k1, C1, r1⟩ | ⟨hb, hr⟩
  · simp only [if_pos hb]
    have htotal : (supplyCollateralTotalNext evm asset amount).toNat < 2^128 := by
      rw [supplyCollateralTotalNext, uadd_toNat,
        Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
      exact ht
    have hnext : (supplyCollateralNext evm dst asset amount).toNat < 2^128 := by
      rw [supplyCollateralNext, uadd_toNat,
        Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
      exact hb
    have hm' := hm.userCollateral htlo dst asset
    have hr := cometSupplyCollateralWrite sender dst asset hstack htotal hm' htlo hs r1
    cases hp : evm.executionEnv.perm
    · simpa only [hp, Bool.false_eq_true, if_false, internalMemoryRun, internalDynamicRun]
        using hr
    · simp only [hp, if_true, internalMemoryRun] at hr ⊢
      obtain ⟨σ', aw2, k2, C2, hs', r2⟩ := hr
      have hw' := ((hw.userCollateral hlo dst asset).scratch hlo
        (EVM.word asset.val) ⟨2⟩).userCollateral hlo dst asset
      have hoffset : memLoad ptr
          (supplyCollateralWriteMemory (userCollateralMemory mem dst asset) dst asset) =
          calldataWord out 0 := by
        simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
          uint256_add_zero_right] using hw'.word 0 (by decide)
      exact cometSupplyCollateralMember sender dst asset (by omega)
        (by rw [← hs.env]; exact hp) hoffset hv (low128_lt _) hnext hret hs' r2
  · simpa only [if_neg hb, internalDynamicRun] using hr

end Benchmarks.CompoundIII.Comet
