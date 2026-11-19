import Benchmarks.Midnight.TakePricing
import Benchmarks.Midnight.CheckedAddGas
import Benchmarks.Midnight.CheckedSubGas

/-! Checked seller and buyer prices after the settlement fee is known. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeSellerPrice (buy price fee : UInt256) : UInt256 :=
  if buy = ⟨0⟩ then price else UInt256.sub price fee

def takeBuyerPrice (buy price fee : UInt256) : UInt256 := takeSellerPrice buy price fee + fee

def TakeSpreadSafe (buy price fee : UInt256) : Prop :=
  (buy ≠ ⟨0⟩ → fee.toNat ≤ price.toNat) ∧
    (takeSellerPrice buy price fee).toNat + fee.toNat < UInt256.size

theorem midnightTakeSpread {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root price fee : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 6 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11556⟩
      (fee :: UInt256.ofNat 11591 :: price :: R) mem aw rdata σ k C) :
    (¬ TakeSpreadSafe offer.buy price fee ∧ RDrev midnightBytecode g s0) ∨
    (TakeSpreadSafe offer.buy price fee ∧ ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨11591⟩
        (takeBuyerPrice offer.buy price fee :: takeSellerPrice offer.buy price fee :: R)
        mem aw' rdata σ k' C') := by
  have hbuy : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 32) mem = offer.buy :=
    ho.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  have hstage :
      (offer.buy ≠ ⟨0⟩ ∧ price.toNat < fee.toNat ∧ RDrev midnightBytecode g s0) ∨
      ((offer.buy ≠ ⟨0⟩ → fee.toNat ≤ price.toNat) ∧
        ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
          RD midnightBytecode I g s0 ⟨11585⟩
            (fee :: UInt256.ofNat 11591 :: takeSellerPrice offer.buy price fee :: R)
            mem aw' rdata σ k' C') := by
    by_cases hb : offer.buy = ⟨0⟩
    · have rd1 := midnightBlocks.midnight_block_11556_taken hstack
        (by rw [hroot, hbuy, hb]; decide) (by jump_dest) rd
      simp only [midnightBlocks.midnight_block_11556_taken_stack] at rd1
      have rd2 := midnightBlocks.midnight_block_14759 (by omega) (by jump_dest) rd1
      have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
      simp only [midnightBlocks.midnight_block_14759_stack] at rd2
      exact Or.inr ⟨fun hn ↦ False.elim (hn hb), _, _, _, ha2, by
        simpa only [takeSellerPrice, if_pos hb] using rd2⟩
    · have rd1 := midnightBlocks.midnight_block_11556_fallthrough hstack (by
        rw [hroot, hbuy, isZero_eq_zero_of_ne hb]
        decide) rd
      simp only [midnightBlocks.midnight_block_11556_fallthrough_stack] at rd1
      have rd2 := midnightBlocks.midnight_block_11575
        (by simp only [List.length_cons]; omega) (by jump_dest) rd1
      have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
      simp only [midnightBlocks.midnight_block_11575_stack] at rd2
      by_cases hle : fee.toNat ≤ price.toNat
      · obtain ⟨k3, C3, hC3, rd3⟩ := midnightCheckedSub_mono
          (by simp only [List.length_cons]; omega) hle (by jump_dest) rd2
        have ha3 := ha2.mono hC3
        have rd4 := midnightBlocks.midnight_block_11583 (by omega) rd3
        have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha3)
        simp only [midnightBlocks.midnight_block_11583_stack] at rd4
        exact Or.inr ⟨fun _ ↦ hle, _, _, _, ha4, by
          simpa only [takeSellerPrice, if_neg hb] using rd4⟩
      · exact Or.inl ⟨hb, by omega, midnightCheckedSubRevert
          (by simp only [List.length_cons]; omega) (by omega) rd2⟩
  rcases hstage with ⟨hb, hlt, hr⟩ | ⟨hsub, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨fun h ↦ Nat.not_lt_of_ge (h.1 hb) hlt, hr⟩
  · have rd2 := midnightBlocks.midnight_block_11585 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_11585_stack] at rd2
    by_cases hadd : (takeSellerPrice offer.buy price fee).toNat + fee.toNat < UInt256.size
    · obtain ⟨k3, C3, hC3, rd3⟩ := midnightCheckedAdd_mono
        (by simp only [List.length_cons]; omega) hadd (by jump_dest) rd2
      exact Or.inr ⟨⟨hsub, hadd⟩, aw1, k3, C3, ha2.mono hC3, rd3⟩
    · exact Or.inl ⟨fun h ↦ hadd h.2, midnightCheckedAddRevert
        (by simp only [List.length_cons]; omega) (by omega) rd2⟩

end Benchmarks.Midnight
