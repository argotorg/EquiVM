import Benchmarks.Midnight.OfferCanonical
import Benchmarks.Midnight.OfferHeapMemory
import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.RuntimeBlocks_042
import Benchmarks.Midnight.RuntimeBlocks_055

variable {fork : Ethereum.Fork}

/-! Exactly one of an offer's assets and units caps must be nonzero. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def TakeCapsValid (offer : OfferData) : Prop :=
  ¬ (offer.maxAssets = ⟨0⟩ ↔ offer.maxUnits = ⟨0⟩)

instance (offer : OfferData) : Decidable (TakeCapsValid offer) := by
  unfold TakeCapsValid
  infer_instance

-- LIBRARY CANDIDATE: comparing zero tests expresses exclusive nonzeroness.
theorem zeroTests_differ_iff (a b : UInt256) :
    UInt256.eq (UInt256.isZero a) (UInt256.isZero b) = ⟨0⟩ ↔ ¬ (a = ⟨0⟩ ↔ b = ⟨0⟩) := by
  by_cases ha : a = ⟨0⟩ <;> by_cases hb : b = ⟨0⟩
  · simp only [ha, hb]
    decide
  · rw [ha, isZero_eq_zero_of_ne hb]
    simp only [ha, hb, iff_false, not_true_eq_false, not_false_eq_true]
    decide
  · rw [hb, isZero_eq_zero_of_ne ha]
    simp only [ha, hb, false_iff, not_true_eq_false, not_false_eq_true]
    decide
  · rw [isZero_eq_zero_of_ne ha, isZero_eq_zero_of_ne hb]
    simp only [ha, hb, iff_self, not_true_eq_false]
    decide

theorem midnightTakeCapsGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 4 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hc : OfferCanonical offer) (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11009⟩ R mem aw rdata σ k C) :
    (¬ TakeCapsValid offer ∧ RDrev fork midnightBytecode g s0) ∨
    (TakeCapsValid offer ∧ ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11051⟩ R mem aw' rdata σ k' C') := by
  have hassets : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 416) mem = offer.maxAssets :=
    ho.words.load_offset ⟨13, by change 13 < 15; decide⟩ rfl
  have hunits : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 384) mem = offer.maxUnits :=
    ho.words.load_offset ⟨12, by change 12 < 15; decide⟩ rfl
  by_cases hv : TakeCapsValid offer
  · have hc0 := (zeroTests_differ_iff offer.maxAssets offer.maxUnits).mpr hv
    have rd1 := midnightBlocks.midnight_block_11009_fallthrough hstack (by
      rw [hroot, hassets, hunits, uint128Mask_computed,
        uint128Mask_clean hc.maxAssets, uint128Mask_clean hc.maxUnits]
      exact hc0) rd
    exact Or.inr ⟨hv, _, _, _, by memory_fund ha, rd1⟩
  · have hc0 : UInt256.eq (UInt256.isZero offer.maxAssets) (UInt256.isZero offer.maxUnits) ≠
        ⟨0⟩ := fun h ↦ hv ((zeroTests_differ_iff _ _).mp h)
    have rr := midnightBlocks.midnight_block_11009_taken hstack (by
      rw [hroot, hassets, hunits, uint128Mask_computed,
        uint128Mask_clean hc.maxAssets, uint128Mask_clean hc.maxUnits]
      exact hc0) (by jump_dest) rd
    exact Or.inl ⟨hv, midnightBlocks.midnight_block_14983 (by omega) rr⟩

end Benchmarks.Midnight
