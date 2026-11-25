import Benchmarks.Midnight.TakeTradeGuardsSource

variable {fork : Ethereum.Fork}

/-! Runtime selection of the delta constrained by a reduce-only offer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeReduceGuardWord (offer : OfferData) (increase debt : UInt256) : UInt256 :=
  if offer.reduceOnly = ⟨0⟩ then ⟨1⟩ else UInt256.isZero (takeReduceDelta offer increase debt)

theorem takeReduceGuardWord_eq (offer : OfferData) (increase debt : UInt256) :
    takeReduceGuardWord offer increase debt =
      if TakeReduceAllowed offer increase debt then ⟨1⟩ else ⟨0⟩ := by
  by_cases hr : offer.reduceOnly = ⟨0⟩
  · have h : TakeReduceAllowed offer increase debt := Or.inl hr
    rw [takeReduceGuardWord, if_pos hr, if_pos h]
  · rw [takeReduceGuardWord, if_neg hr]
    by_cases hd : takeReduceDelta offer increase debt = ⟨0⟩
    · have h : TakeReduceAllowed offer increase debt := Or.inr hd
      rw [if_pos h, hd]
      rfl
    · have h : ¬ TakeReduceAllowed offer increase debt := fun h ↦ h.elim hr hd
      rw [if_neg h, isZero_eq_zero_of_ne hd]

theorem midnightTakeReduceRead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr root buyerSlot debt buyerDebt sellerSlot marketSlot
      decrease ratifierPtr increase : UInt256} {offer : OfferData} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12212⟩
      ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12228⟩
        ([takeReduceGuardWord offer increase debt, buyerSlot, debt, buyerDebt, sellerSlot,
          marketSlot, decrease, ratifierPtr, increase] ++ R) mem aw' rdata σ k' C' := by
  have hr : memLoad (memLoad (UInt256.ofNat 384) mem + UInt256.ofNat 352) mem =
      offer.reduceOnly := by
    rw [hoffer]
    exact ho.words.load_offset ⟨11, by change 11 < 15; decide⟩ rfl
  have hb : memLoad (UInt256.ofNat 32 + memLoad (UInt256.ofNat 384) mem) mem = offer.buy := by
    rw [hoffer, u256_add_comm]
    exact ho.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hz : offer.reduceOnly = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_12212_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hr, hz]; decide) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_12212_fallthrough_stack, hr, hz] at rd1
    simp only [takeReduceGuardWord, if_pos hz]
    exact ⟨_, _, _, ha1, rd1⟩
  · have rd1 := midnightBlocks.midnight_block_12212_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hr, isZero_eq_zero_of_ne hz]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_12212_taken_stack] at rd1
    by_cases hbuy : offer.buy = ⟨0⟩
    · have rd2 := midnightBlocks.midnight_block_14402_taken
        (by simp only [List.length_cons]; omega) (by rw [hb, hbuy]; decide) (by jump_dest) rd1
      have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
      simp only [midnightBlocks.midnight_block_14402_taken_stack] at rd2
      have rd3 := midnightBlocks.midnight_block_14423
        (by simp only [List.length_cons]; omega) (by jump_dest) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
      simp only [takeReduceGuardWord, if_neg hz, takeReduceDelta, if_pos hbuy]
      exact ⟨_, _, _, ha3, rd3⟩
    · have rd2 := midnightBlocks.midnight_block_14402_fallthrough
        (by simp only [List.length_cons]; omega) (by rw [hb, isZero_eq_zero_of_ne hbuy]; rfl) rd1
      have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
      simp only [midnightBlocks.midnight_block_14402_fallthrough_stack] at rd2
      have rd3 := midnightBlocks.midnight_block_14417 (by omega) (by jump_dest) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
      simp only [takeReduceGuardWord, if_neg hz, takeReduceDelta, if_neg hbuy]
      exact ⟨_, _, _, ha3, rd3⟩

end Benchmarks.Midnight
