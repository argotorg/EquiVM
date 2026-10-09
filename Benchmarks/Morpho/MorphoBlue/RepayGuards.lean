import Benchmarks.Morpho.MorphoBlue.RepayGuardPrepare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoRepayGuards {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets shares account srcOff len : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10448)
      ([len, srcOff, account, shares, assets, UInt256.ofNat 128, UInt256.ofNat 0] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    (¬ SupplyGuards σ ee p assets shares account ∧ RDrev (deployedRuntime v) g s0) ∨
    (SupplyGuards σ ee p assets shares account ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10561)
        (repayAccrueTail p.id assets shares account srcOff len R) (supplyGuardMem p) aw' out σ k' C') := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoRepayCreated p hstack h
  by_cases hc : marketFieldWord σ ee p.id 4 ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hc hg.1, morphoRequireFalseShort (by change R.length + 13 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hc]; rfl) (by rw [(accruePublicMemory p).2]; decide)
      (by rw [(accruePublicMemory p).2]; decide) rd1⟩
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (by change R.length + 13 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hc]; decide) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoRepayInput p hstack rd2
  by_cases hz : exactlyOneZero assets shares = true
  swap
  · exact .inl ⟨fun hg => hz hg.2.1, morphoRequireFalseShort (by change R.length + 13 + 11 ≤ 1024; omega)
      (by rw [exactlyOneZero_word, if_neg hz]) (by rw [(supplyInputHeap p).2]; decide)
      (by rw [(supplyInputHeap p).2]; decide) rd3⟩
  obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (by change R.length + 13 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [exactlyOneZero_word, if_pos hz]; decide) rd3
  obtain ⟨a5, k5, C5, rd5⟩ := morphoRepayAddress p hstack ha rd4
  by_cases hn : account ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg => hn hg.2.2, morphoRequireFalseShort (by change R.length + 14 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hn]; rfl) (by rw [(supplyGuardHeap p).2]; decide)
      (by rw [(supplyGuardHeap p).2]; decide) rd5⟩
  obtain ⟨k6, C6, rd6⟩ := morphoRequireTrue (by change R.length + 14 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hn]; decide) rd5
  exact .inr ⟨⟨hc, hz, hn⟩, a5, k6, C6, rd6⟩

end Benchmarks.Morpho.MorphoBlue
