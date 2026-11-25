import Benchmarks.Midnight.TakeAccountingStore
import Benchmarks.Midnight.TakeRecipientsSource
import Benchmarks.Midnight.RuntimeBlocks_053

variable {fork : Ethereum.Fork}

/-! Runtime selection of buyer and seller callback addresses. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

theorem midnightTakeCallbackSelect {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw decrease ratifierPtr increase marketPtr arrayPtr callbackPtr root : UInt256}
    {offer : OfferData} {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hc : OfferCanonical offer)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat callback.val)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12719⟩
      ([offer.buy, decrease, ratifierPtr, increase] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12757⟩
        ([decrease, increase, ratifierPtr, UInt256.ofNat (takeSellerCallback offer callback).val,
          offer.buy, UInt256.ofNat (takeBuyerCallback offer callback).val] ++ R)
        mem aw' rdata σ k' C' := by
  have ho_cb : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 224) mem =
      UInt256.ofNat offer.callback.val :=
    ho.words.load_offset ⟨7, by change 7 < 15; decide⟩ rfl
  have hclean : UInt256.land (UInt256.ofNat offer.callback.val) solcAddrMask =
      UInt256.ofNat offer.callback.val := addressWord_val_clean offer.callback
  simp only [List.cons_append, List.nil_append] at rd
  rcases hc.buy with hb | hb
  · have rd1 := midnight_block_12719_taken (by simp only [List.length_cons]; omega)
      (by rw [hb]; decide) (by jump_dest) rd
    simp only [midnight_block_12719_taken_stack, hb] at rd1
    have rd2 := midnight_block_14136 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnight_block_14136_stack, hcallback] at rd2
    have rd3 := midnight_block_12746_taken (by simp only [List.length_cons]; omega)
      (by decide) (by jump_dest) rd2
    have rd4 := midnight_block_14113 (by simp only [List.length_cons]; omega) (by jump_dest) rd3
    have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha2)
    simp only [midnight_block_14113_stack, hoffer, ho_cb, addressMask_computed, hclean] at rd4 ha4
    simp only [takeBuyerCallback, takeSellerCallback, hb, if_true]
    exact ⟨_, _, _, ha4, rd4⟩
  · have hb0 : offer.buy ≠ ⟨0⟩ := by rw [hb]; decide
    have rd1 := midnight_block_12719_fallthrough (by simp only [List.length_cons]; omega)
      (by rw [hb]; decide) rd
    simp only [midnight_block_12719_fallthrough_stack, hb] at rd1
    have rd2 := midnight_block_12728 (by omega) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnight_block_12728_stack, hoffer, ho_cb, addressMask_computed, hclean] at rd2 ha2
    have rd3 := midnight_block_12746_fallthrough (by simp only [List.length_cons]; omega)
      (by decide) rd2
    have rd4 := midnight_block_12753 (by simp only [List.length_cons]; omega) rd3
    have ha4 := memoryFundingAt (credit := credit) rd4 (by memory_fund ha2)
    simp only [midnight_block_12753_stack, hcallback] at rd4
    simp only [takeBuyerCallback, takeSellerCallback, hb, show (⟨1⟩ : UInt256) ≠ ⟨0⟩ from by decide, if_false]
    exact ⟨_, _, _, ha4, rd4⟩

end Benchmarks.Midnight
