import Benchmarks.Midnight.TakeConsumptionMemory
import Benchmarks.Midnight.RuntimeBlocks_054

variable {fork : Ethereum.Fork}

/-! The runtime cap checks store newConsumed and reject values above the selected limit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeConsumptionCheckPC (offer : OfferData) : UInt256 :=
  if offer.maxAssets = ⟨0⟩ then ⟨14672⟩ else ⟨11794⟩

theorem midnightTakeConsumptionCap {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root value : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 3 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hc : OfferCanonical offer) (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 (takeConsumptionCheckPC offer) (value :: R)
      mem aw rdata σ k C) :
    (¬ value.toNat ≤ (takeConsumedCap offer).toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (value.toNat ≤ (takeConsumedCap offer).toNat ∧
      ∃ aw' k' C', MemoryFunding credit (writeWord mem 480 value) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨11826⟩ R (writeWord mem 480 value) aw' rdata σ k' C') := by
  have hm : 416 ≤ mem.size := by
    have hh := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hh
    omega
  have ho1 := ho.writeWord_below (off := 480) value (by decide)
  have hroot1 : memLoad (UInt256.ofNat 384) (writeWord mem 480 value) = ⟨832⟩ := by
    rw [memLoad_writeWord_preserved mem 480 (UInt256.ofNat 384) _ hm (Or.inl (by decide)), hroot]
  have hvalue : memLoad (UInt256.ofNat 480) (writeWord mem 480 value) = value :=
    memLoad_writeWord _ _ _
  have hfold : value.toByteArray.write 0 mem (UInt256.ofNat 480).toNat 32 =
      writeWord mem 480 value := rfl
  by_cases hz : offer.maxAssets = ⟨0⟩
  · simp only [takeConsumptionCheckPC, takeConsumedCap, if_pos hz] at rd ⊢
    have hcap : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 384)
        (writeWord mem 480 value) = offer.maxUnits :=
      ho1.words.load_offset ⟨12, by change 12 < 15; decide⟩ rfl
    by_cases hle : value.toNat ≤ offer.maxUnits.toNat
    · have rd1 := midnightBlocks.midnight_block_14672_taken hstack (by
        rw [hfold, hroot1, hvalue, hcap, uint128Mask_computed, uint128Mask_clean hc.maxUnits,
          ugt_zero hle]
        decide) (by jump_dest) rd
      simp only [midnightBlocks.midnight_block_14672_taken_stack,
        midnightBlocks.midnight_block_14672_taken_memory] at rd1
      have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
      exact Or.inr ⟨hle, _, _, _, ha1, rd1⟩
    · have rd1 := midnightBlocks.midnight_block_14672_fallthrough hstack (by
        rw [hfold, hroot1, hvalue, hcap, uint128Mask_computed, uint128Mask_clean hc.maxUnits,
          ugt_one (by omega)]
        decide) rd
      simp only [midnightBlocks.midnight_block_14672_fallthrough_stack] at rd1
      exact Or.inl ⟨hle, midnightBlocks.midnight_block_14703 (by omega) rd1⟩
  · simp only [takeConsumptionCheckPC, takeConsumedCap, if_neg hz] at rd ⊢
    have hcap : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 416)
        (writeWord mem 480 value) = offer.maxAssets :=
      ho1.words.load_offset ⟨13, by change 13 < 15; decide⟩ rfl
    by_cases hle : value.toNat ≤ offer.maxAssets.toNat
    · have rd1 := midnightBlocks.midnight_block_11794_fallthrough hstack (by
        rw [hfold, hroot1, hvalue, hcap, uint128Mask_computed, uint128Mask_clean hc.maxAssets]
        exact ugt_zero hle) rd
      simp only [midnightBlocks.midnight_block_11794_fallthrough_stack,
        midnightBlocks.midnight_block_11794_fallthrough_memory] at rd1
      have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
      exact Or.inr ⟨hle, _, _, _, ha1, rd1⟩
    · have rd1 := midnightBlocks.midnight_block_11794_taken hstack (by
        rw [hfold, hroot1, hvalue, hcap, uint128Mask_computed, uint128Mask_clean hc.maxAssets,
          ugt_one (by omega)]
        decide) (by jump_dest) rd
      simp only [midnightBlocks.midnight_block_11794_taken_stack] at rd1
      exact Or.inl ⟨hle, midnightBlocks.midnight_block_14579 (by omega) rd1⟩

end Benchmarks.Midnight
