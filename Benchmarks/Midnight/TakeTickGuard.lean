import Benchmarks.Midnight.TakeFeeCapGuard
import Benchmarks.Midnight.ModArithmetic

variable {fork : Ethereum.Fork}

/-! Checked modulo and tick accessibility for take. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeTickGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root feeWord : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 8 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11080⟩ (feeWord :: R) mem aw rdata σ k C) :
    ((marketTickSpacing feeWord = ⟨0⟩ ∨
        offer.tick.toNat % (marketTickSpacing feeWord).toNat ≠ 0) ∧
      RDrev fork midnightBytecode g s0) ∨
    (marketTickSpacing feeWord ≠ ⟨0⟩ ∧
      offer.tick.toNat % (marketTickSpacing feeWord).toNat = 0 ∧
      ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨11108⟩ R mem aw' rdata σ k' C') := by
  have ht : memLoad (UInt256.ofNat 160 + (⟨832⟩ : UInt256)) mem = offer.tick := by
    rw [u256_add_comm]
    exact ho.words.load_offset ⟨5, by change 5 < 15; decide⟩ rfl
  have rd1 := midnightBlocks.midnight_block_11080 (by omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
  simp only [midnightBlocks.midnight_block_11080_stack, hroot, ht,
    u256_land_comm (UInt256.ofNat 255)] at rd1 ha1
  change RD fork midnightBytecode I g s0 ⟨20085⟩
    (offer.tick :: marketTickSpacing feeWord :: ⟨11103⟩ :: R) mem _ rdata σ _ _ at rd1
  by_cases hz : marketTickSpacing feeWord = ⟨0⟩
  · have rr := midnightBlocks.midnight_block_20085_taken
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide) (by jump_dest) rd1
    exact Or.inl ⟨Or.inl hz, midnightBlocks.midnight_block_19401 (by
      simp only [List.length_cons]; omega) rr⟩
  · have rd2 := midnightBlocks.midnight_block_20085_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hz) rd1
    have rd3 := midnightBlocks.midnight_block_20092 (by omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_20092_stack] at rd3
    by_cases hmod : UInt256.mod offer.tick (marketTickSpacing feeWord) = ⟨0⟩
    · have rd4 := midnightBlocks.midnight_block_11103_fallthrough (by omega) hmod rd3
      exact Or.inr ⟨hz, (mod_eq_zero_iff _ _ hz).mp hmod,
        _, _, _, by memory_fund ha1, rd4⟩
    · have rr := midnightBlocks.midnight_block_11103_taken (by omega) hmod (by jump_dest) rd3
      exact Or.inl ⟨Or.inr (fun h ↦ hmod ((mod_eq_zero_iff _ _ hz).mpr h)),
        midnightBlocks.midnight_block_14953 (by change R.length + 2 ≤ 1024; omega) rr⟩

end Benchmarks.Midnight
