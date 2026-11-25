import Benchmarks.Midnight.TakeCallbackSelect

variable {fork : Ethereum.Fork}

/-! Runtime payer selection, including the zero-callback branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

theorem midnightTakePayerSelect {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw decrease ratifierPtr increase : UInt256}
    {offer : OfferData} {callback buyer : AccountAddress} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 9 ≤ 1024) (hc : OfferCanonical offer)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = UInt256.ofNat buyer.val)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12757⟩
      ([decrease, increase, ratifierPtr, UInt256.ofNat (takeSellerCallback offer callback).val,
        offer.buy, UInt256.ofNat (takeBuyerCallback offer callback).val] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12775⟩
        ([offer.buy, decrease, increase, ratifierPtr,
          UInt256.ofNat (takeSellerCallback offer callback).val,
          UInt256.ofNat (takePayer offer callback buyer I.source).val,
          UInt256.ofNat (takeBuyerCallback offer callback).val] ++ R)
        mem aw' rdata σ k' C' := by
  have hclean : UInt256.land (UInt256.ofNat (takeBuyerCallback offer callback).val) solcAddrMask =
      UInt256.ofNat (takeBuyerCallback offer callback).val :=
    addressWord_val_clean (takeBuyerCallback offer callback)
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hcb : takeBuyerCallback offer callback = 0
  · have hw : UInt256.ofNat (takeBuyerCallback offer callback).val = (⟨0⟩ : UInt256) := by
      rw [hcb]; rfl
    have rd1 := midnight_block_12757_taken (by omega)
      (by rw [addressMask_computed, hclean, hw]; decide) (by jump_dest) rd
    rcases hc.buy with hb | hb
    · have rd2 := midnight_block_14090_taken (by simp only [List.length_cons]; omega)
        (by rw [hb]; decide) (by jump_dest) rd1
      have rd3 := midnight_block_14107 (by simp only [List.length_cons]; omega)
        (by jump_dest) rd2
      simp only [midnight_block_14107_stack] at rd3
      have rd4 := midnight_block_14101 (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      simp only [midnight_block_14101_stack] at rd4
      simp only [takePayer, if_pos hcb, hb, if_true]
      rw [hb] at rd4
      exact ⟨_, _, _, ha.mono (by omega), rd4⟩
    · have hb0 : offer.buy ≠ ⟨0⟩ := by rw [hb]; decide
      have rd2 := midnight_block_14090_fallthrough (by simp only [List.length_cons]; omega)
        (by rw [hb]; decide) rd1
      have rd3 := midnight_block_14097 (by simp only [List.length_cons]; omega) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha)
      simp only [midnight_block_14097_stack, hbuyer] at rd3
      have rd4 := midnight_block_14101 (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      simp only [midnight_block_14101_stack] at rd4
      simp only [takePayer, if_pos hcb, if_neg hb0]
      exact ⟨_, _, _, ha3.mono (by omega), rd4⟩
  · have hw : UInt256.ofNat (takeBuyerCallback offer callback).val ≠ (⟨0⟩ : UInt256) := by
      intro he
      have hv := congrArg UInt256.toNat he
      have hn : (UInt256.ofNat (takeBuyerCallback offer callback).val).toNat =
          (takeBuyerCallback offer callback).val := addressWord_toNat_val _
      rw [hn] at hv
      exact hcb (Fin.ext hv)
    have rd1 := midnight_block_12757_fallthrough (by omega)
      (by rw [addressMask_computed, hclean, isZero_eq_zero_of_ne hw]; rfl) rd
    have rd2 := midnight_block_12773 (by omega) rd1
    simp only [midnight_block_12773_stack] at rd2
    simp only [takePayer, if_neg hcb]
    exact ⟨_, _, _, ha.mono (by omega), rd2⟩

end Benchmarks.Midnight
