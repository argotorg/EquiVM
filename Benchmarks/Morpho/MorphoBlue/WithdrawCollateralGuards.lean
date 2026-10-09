import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralGuardPrepare
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralGuards
import Benchmarks.Morpho.MorphoBlue.WithdrawGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def WithdrawCollateralGuards (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords)
    (assets account receiver : UInt256) : Prop :=
  SupplyCollateralGuards σ ee p assets receiver ∧ senderAuthorizedWord σ ee account ≠ UInt256.ofNat 0

theorem morphoWithdrawCollateralBasicGuards {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5498)
      ([UInt256.ofNat 128, account, solcAddrMask, receiver, assets, receiver, UInt256.ofNat 0] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    (¬ SupplyCollateralGuards σ ee p assets receiver ∧ RDrev (deployedRuntime v) g s0) ∨
    (SupplyCollateralGuards σ ee p assets receiver ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5600)
        (withdrawCollateralGuardTail p.id assets account receiver R) (supplyCollateralGuardMem p) aw' out σ k' C') := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoWithdrawCollateralCreated p (by omega) h
  by_cases hc : marketFieldWord σ ee p.id 4 ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hc hg.1, morphoRequireFalseShort (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
      (by rw [not_not.mp hc]; rfl) (by rw [(accruePublicMemory p).2]; decide)
      (by rw [(accruePublicMemory p).2]; decide) rd1⟩
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hc]; decide) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoWithdrawCollateralAssets p (by omega) rd2
  by_cases hz : assets ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hz hg.2.1, morphoRequireFalseShort (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
      (by rw [not_not.mp hz]; rfl) (by rw [(supplyCollateralAssetsHeap p).2]; decide)
      (by rw [(supplyCollateralAssetsHeap p).2]; decide) rd3⟩
  obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hz]; decide) rd3
  obtain ⟨a5, k5, C5, rd5⟩ := morphoWithdrawCollateralAddress p (by omega) rd4
  by_cases hn : receiver ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hn hg.2.2, morphoRequireFalseShort (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
      (by rw [not_not.mp hn]; rfl) (by rw [(supplyCollateralGuardHeap p).2]; decide)
      (by rw [(supplyCollateralGuardHeap p).2]; decide) rd5⟩
  obtain ⟨k6, C6, rd6⟩ := morphoRequireTrue (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hn]; decide) rd5
  exact .inr ⟨⟨hc, hz, hn⟩, a5, k6, C6, rd6⟩


theorem morphoWithdrawCollateralGuards {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5498)
      ([UInt256.ofNat 128, account, solcAddrMask, receiver, assets, receiver, UInt256.ofNat 0] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    (¬ WithdrawCollateralGuards σ ee p assets account receiver ∧ RDrev (deployedRuntime v) g s0) ∨
    (WithdrawCollateralGuards σ ee p assets account receiver ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5620)
        (withdrawCollateralGuardTail p.id assets account receiver R) (withdrawCollateralGuardMem p ee account) aw' out σ k' C') := by
  rcases morphoWithdrawCollateralBasicGuards p hstack h with ⟨hb, hrev⟩ | ⟨hb, a1, k1, C1, rd1⟩
  · exact .inl ⟨fun hg => hb hg.1, hrev⟩
  · obtain ⟨a2, k2, C2, rd2⟩ := morphoWithdrawCollateralAuthorization p hstack ha rd1
    by_cases hn : senderAuthorizedWord σ ee account ≠ UInt256.ofNat 0
    swap
    · exact .inl ⟨fun hg => hn hg.2, morphoRequireFalseShort (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
        (not_not.mp hn) (by rw [(withdrawCollateralGuardHeap p ee account).2]; decide)
        (by rw [(withdrawCollateralGuardHeap p ee account).2]; decide) rd2⟩
    obtain ⟨k3, C3, rd3⟩ := morphoRequireTrue (by simp only [withdrawCollateralGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (isZero_eq_zero_of_ne hn) rd2
    exact .inr ⟨⟨hb, hn⟩, a2, k3, C3, rd3⟩

end Benchmarks.Morpho.MorphoBlue
