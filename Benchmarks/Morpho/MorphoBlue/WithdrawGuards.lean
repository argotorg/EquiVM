import Benchmarks.Morpho.MorphoBlue.WithdrawAuthorization

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWithdrawBasicGuards {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets shares account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (ha : receiver.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7514)
      ([receiver, account, shares, assets, UInt256.ofNat 128, UInt256.ofNat 0, UInt256.ofNat 64] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    (¬ SupplyGuards σ ee p assets shares receiver ∧ RDrev (deployedRuntime v) g s0) ∨
    (SupplyGuards σ ee p assets shares receiver ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7629)
        (withdrawAccrueTail p.id assets shares account receiver R) (supplyGuardMem p) aw' out σ k' C') := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoWithdrawCreated p hstack h
  by_cases hc : marketFieldWord σ ee p.id 4 ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hc hg.1, morphoRequireFalseShort (by change R.length + 10 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hc]; rfl) (by rw [(accruePublicMemory p).2]; decide)
      (by rw [(accruePublicMemory p).2]; decide) rd1⟩
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (by change R.length + 10 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hc]; decide) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoWithdrawInput p hstack rd2
  by_cases hz : exactlyOneZero assets shares = true
  swap
  · exact .inl ⟨fun hg => hz hg.2.1, morphoRequireFalseShort (by change R.length + 10 + 11 ≤ 1024; omega)
      (by rw [exactlyOneZero_word, if_neg hz]) (by rw [(supplyInputHeap p).2]; decide)
      (by rw [(supplyInputHeap p).2]; decide) rd3⟩
  obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (by change R.length + 10 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [exactlyOneZero_word, if_pos hz]; decide) rd3
  obtain ⟨a5, k5, C5, rd5⟩ := morphoWithdrawAddress p hstack ha rd4
  by_cases hn : receiver ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hn hg.2.2, morphoRequireFalseShort (by change R.length + 11 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hn]; rfl) (by rw [(supplyGuardHeap p).2]; decide)
      (by rw [(supplyGuardHeap p).2]; decide) rd5⟩
  obtain ⟨k6, C6, rd6⟩ := morphoRequireTrue (by change R.length + 11 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hn]; decide) rd5
  exact .inr ⟨⟨hc, hz, hn⟩, a5, k6, C6, rd6⟩


def WithdrawGuards (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords)
    (assets shares account receiver : UInt256) : Prop :=
  SupplyGuards σ ee p assets shares receiver ∧ senderAuthorizedWord σ ee account ≠ UInt256.ofNat 0

theorem morphoWithdrawGuards {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets shares account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7514)
      ([receiver, account, shares, assets, UInt256.ofNat 128, UInt256.ofNat 0, UInt256.ofNat 64] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    (¬ WithdrawGuards σ ee p assets shares account receiver ∧ RDrev (deployedRuntime v) g s0) ∨
    (WithdrawGuards σ ee p assets shares account receiver ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7641)
        (withdrawAccrueTail p.id assets shares account receiver R) (withdrawGuardMem p ee account) aw' out σ k' C') := by
  rcases morphoWithdrawBasicGuards p hstack hr h with ⟨hb, hrev⟩ | ⟨hb, a1, k1, C1, rd1⟩
  · exact .inl ⟨fun hg => hb hg.1, hrev⟩
  · obtain ⟨a2, k2, C2, rd2⟩ := morphoWithdrawAuthorization p hstack ha rd1
    by_cases hn : senderAuthorizedWord σ ee account ≠ UInt256.ofNat 0
    swap
    · exact .inl ⟨fun hg => hn hg.2, morphoRequireFalseShort (by change R.length + 11 + 11 ≤ 1024; omega)
        (not_not.mp hn) (by rw [(withdrawGuardHeap p ee account).2]; decide)
        (by rw [(withdrawGuardHeap p ee account).2]; decide) rd2⟩
    obtain ⟨k3, C3, rd3⟩ := morphoRequireTrue (by change R.length + 11 + 4 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (isZero_eq_zero_of_ne hn) rd2
    exact .inr ⟨⟨hb, hn⟩, a2, k3, C3, rd3⟩

end Benchmarks.Morpho.MorphoBlue
