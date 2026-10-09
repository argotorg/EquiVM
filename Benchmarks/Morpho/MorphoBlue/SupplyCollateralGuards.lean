import Benchmarks.Morpho.MorphoBlue.SupplyCollateralGuardPrepare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def SupplyCollateralGuards (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords)
    (assets account : UInt256) : Prop :=
  marketFieldWord σ ee p.id 4 ≠ ⟨0⟩ ∧ assets ≠ ⟨0⟩ ∧ account ≠ ⟨0⟩

theorem morphoSupplyCollateralGuards {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets account srcOff len : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 24 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10077)
      ([len, srcOff, account, assets, UInt256.ofNat 0, UInt256.ofNat 128] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    (¬ SupplyCollateralGuards σ ee p assets account ∧ RDrev (deployedRuntime v) g s0) ∨
    (SupplyCollateralGuards σ ee p assets account ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10184)
        (supplyCollateralUpdateTail p.id assets account srcOff len R) (supplyCollateralGuardMem p) aw' out σ k' C') := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoSupplyCollateralCreated p hstack h
  by_cases hc : marketFieldWord σ ee p.id 4 ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hc hg.1, morphoRequireFalseShort (by change R.length + 7 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hc]; rfl) (by rw [(accruePublicMemory p).2]; decide)
      (by rw [(accruePublicMemory p).2]; decide) rd1⟩
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (by change R.length + 7 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hc]; decide) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoSupplyCollateralAssets p hstack rd2
  by_cases hz : assets ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hz hg.2.1, morphoRequireFalseShort (by change R.length + 7 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hz]; rfl) (by rw [(supplyCollateralAssetsHeap p).2]; decide)
      (by rw [(supplyCollateralAssetsHeap p).2]; decide) rd3⟩
  obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (by change R.length + 7 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hz]; decide) rd3
  obtain ⟨a5, k5, C5, rd5⟩ := morphoSupplyCollateralAddress p hstack ha rd4
  by_cases hn : account ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hn hg.2.2, morphoRequireFalseShort (by change R.length + 8 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hn]; rfl) (by rw [(supplyCollateralGuardHeap p).2]; decide)
      (by rw [(supplyCollateralGuardHeap p).2]; decide) rd5⟩
  obtain ⟨k6, C6, rd6⟩ := morphoRequireTrue (by change R.length + 8 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hn]; decide) rd5
  exact .inr ⟨⟨hc, hz, hn⟩, a5, k6, C6, rd6⟩

end Benchmarks.Morpho.MorphoBlue
