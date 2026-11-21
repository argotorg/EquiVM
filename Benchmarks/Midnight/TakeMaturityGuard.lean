import Benchmarks.Midnight.TakeTradeGuardsSource

/-! The maturity check permits an expired market only when no new seller debt is created. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeMaturityGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root buyerSlot debt : UInt256}
    {offer : OfferData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12187⟩ (buyerSlot :: debt :: R) mem aw rdata σ k C) :
    (¬ TakeMaturityAllowed I offer debt ∧ RDrev midnightBytecode g s0) ∨
    (TakeMaturityAllowed I offer debt ∧ ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨12212⟩ (buyerSlot :: debt :: R) mem aw' rdata σ k' C') := by
  have hm : memLoad (⟨832⟩ : UInt256) mem = marketPtr :=
    ho.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
  have hread : memLoad (memLoad (memLoad (UInt256.ofNat 384) mem) mem + UInt256.ofNat 128) mem =
      offer.market.maturity := by rw [hoffer, hm, ho.market.maturity]
  by_cases htime : (UInt256.ofNat I.header.timestamp).toNat ≤ offer.market.maturity.toNat
  · have hc : UInt256.gt (UInt256.ofNat I.header.timestamp)
        (memLoad (memLoad (memLoad (UInt256.ofNat 384) mem) mem + UInt256.ofNat 128) mem) = ⟨0⟩ :=
      by rw [hread]; exact ugt_zero htime
    have rd1 := midnightBlocks.midnight_block_12187_fallthrough
      (by simp only [List.length_cons]; omega) hc rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_12187_fallthrough_stack, hc] at rd1
    have rd2 := midnightBlocks.midnight_block_12206_fallthrough
      (by simp only [List.length_cons]; omega) (by decide) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    exact Or.inr ⟨Or.inl htime, _, _, _, ha2, rd2⟩
  · have hc : UInt256.gt (UInt256.ofNat I.header.timestamp)
        (memLoad (memLoad (memLoad (UInt256.ofNat 384) mem) mem + UInt256.ofNat 128) mem) = ⟨1⟩ := by
      rw [hread]
      exact ugt_one (Nat.lt_of_not_ge htime)
    have rd1 := midnightBlocks.midnight_block_12187_taken
      (by simp only [List.length_cons]; omega) (by rw [hc]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_12187_taken_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_14445 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_14445_stack] at rd2
    by_cases hz : debt = ⟨0⟩
    · have rd3 := midnightBlocks.midnight_block_12206_fallthrough
        (by simp only [List.length_cons]; omega) (by rw [hz]; decide) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
      exact Or.inr ⟨Or.inr hz, _, _, _, ha3, rd3⟩
    · have rd3 := midnightBlocks.midnight_block_12206_taken
        (by simp only [List.length_cons]; omega)
        (by rw [isZero_eq_zero_of_ne hz]; decide) (by jump_dest) rd2
      simp only [midnightBlocks.midnight_block_12206_taken_stack] at rd3
      exact Or.inl ⟨fun h ↦ h.elim htime hz,
        midnightBlocks.midnight_block_14430 (by simp only [List.length_cons]; omega) rd3⟩

end Benchmarks.Midnight
