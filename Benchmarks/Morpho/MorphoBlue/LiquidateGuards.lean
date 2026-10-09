import Benchmarks.Morpho.MorphoBlue.SupplyGuards
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralMemory
import Benchmarks.Morpho.MorphoBlue.ExactlyOneZero

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateGuardTail (id seized shares srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [shares, srcOff, len, UInt256.ofNat 0, id, seized, UInt256.ofNat 128] ++ R

def LiquidateGuards (σ : AccountMap) (ee : ExecutionEnv) (p : MarketParamsWords)
    (seized shares : UInt256) : Prop :=
  marketFieldWord σ ee p.id 4 ≠ ⟨0⟩ ∧ exactlyOneZero seized shares = true

section Guards
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {aw assets shares srcOff len : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {R : List UInt256}

theorem morphoLiquidateCreated (p : MarketParamsWords) (hstack : R.length + 30 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1378)
      ([len, srcOff, UInt256.ofNat 0, UInt256.ofNat 128] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.isZero (UInt256.isZero (marketFieldWord σ ee p.id 4)), UInt256.ofNat 288, UInt256.ofNat 1439] ++
        liquidateGuardTail p.id (calldataWord ee.calldata 196) (calldataWord ee.calldata 228) srcOff len R) (accruePublicMem p) aw' out σ k' C' := by
  have hid : keccakWord (UInt256.ofNat 128) (UInt256.ofNat 160) (createMarketDecodedMem p) = p.id :=
    marketParamsMem_hash p _ _ (by decide) (by native_decide) (by native_decide)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_1378_packed
    (immWords := wordsOf (immStore v)) (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [morphoBlocks.morpho_block_1378_stack, morphoBlocks.morpho_block_1378_memory, hid] at rd1
  let mem := twoWordHashMem p.id (UInt256.ofNat 3) (createMarketDecodedMem p)
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.ofNat 585, UInt256.isZero (UInt256.isZero (UInt256.land
      (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem + UInt256.ofNat 2) σ ee)
      uint128Mask)), UInt256.ofNat 1439] ++ liquidateGuardTail p.id (calldataWord ee.calldata 196) (calldataWord ee.calldata 228) srcOff len R)
    mem _ _ _ _ _ at rd1
  rw [hh] at rd1
  have hm := createMarketHeap_morpho ((createMarketDecodedHeap p).hash (by decide) p.id (UInt256.ofNat 3))
    (by decide) 64 (by decide) (lt_usize _ (by decide))
  obtain ⟨a2, k2, C2, rd2⟩ := morphoMarketCreatedMessage (v := v)
    (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hm (by decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  have rd3 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩

theorem morphoLiquidateInput (p : MarketParamsWords) (hstack : R.length + 30 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1439)
      (liquidateGuardTail p.id assets shares srcOff len R) (accruePublicMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([UInt256.xor (UInt256.isZero assets) (UInt256.isZero shares), UInt256.ofNat 352, UInt256.ofNat 1460] ++
        liquidateGuardTail p.id assets shares srcOff len R) (supplyInputMem p) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_1439 (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoInconsistentInputMessage (v := v)
    (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (accruePublicMemory p).1.freePtr (by decide) rd1
  have rd3 := morphoBlocks.morpho_block_1450 (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨a2, _, _, rd3⟩


theorem morphoLiquidateGuards (p : MarketParamsWords) (hstack : R.length + 30 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1378)
      ([len, srcOff, UInt256.ofNat 0, UInt256.ofNat 128] ++ R)
      (createMarketDecodedMem p) aw out σ k C) :
    (¬ LiquidateGuards σ ee p (calldataWord ee.calldata 196) (calldataWord ee.calldata 228) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (LiquidateGuards σ ee p (calldataWord ee.calldata 196) (calldataWord ee.calldata 228) ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1460)
        (liquidateGuardTail p.id (calldataWord ee.calldata 196) (calldataWord ee.calldata 228) srcOff len R)
        (supplyInputMem p) aw' out σ k' C') := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoLiquidateCreated p hstack h
  by_cases hc : marketFieldWord σ ee p.id 4 ≠ ⟨0⟩
  swap
  · exact .inl ⟨fun hg ↦ hc hg.1, morphoRequireFalseShort (by change R.length + 7 + 11 ≤ 1024; omega)
      (by rw [not_not.mp hc]; rfl) (by rw [(accruePublicMemory p).2]; decide)
      (by rw [(accruePublicMemory p).2]; decide) rd1⟩
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (by change R.length + 7 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [isZero_eq_zero_of_ne hc]; decide) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoLiquidateInput p hstack rd2
  by_cases hz : exactlyOneZero (calldataWord ee.calldata 196) (calldataWord ee.calldata 228) = true
  swap
  · exact .inl ⟨fun hg ↦ hz hg.2, morphoRequireFalseShort (by change R.length + 7 + 11 ≤ 1024; omega)
      (by rw [exactlyOneZero_word, if_neg hz]) (by rw [(supplyInputHeap p).2]; decide)
      (by rw [(supplyInputHeap p).2]; decide) rd3⟩
  obtain ⟨k4, C4, rd4⟩ := morphoRequireTrue (by change R.length + 7 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [exactlyOneZero_word, if_pos hz]; decide) rd3
  exact .inr ⟨⟨hc, hz⟩, a3, k4, C4, rd4⟩

end Guards
end Benchmarks.Morpho.MorphoBlue
