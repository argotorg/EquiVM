import Benchmarks.Midnight.TakeCallbackSelect

variable {fork : Ethereum.Fork}

/-! Runtime selection and storage of the transfer receiver. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

def takeReceiverMemory (mem : ByteArray) (offer : OfferData) (receiver : AccountAddress) : ByteArray :=
  writeWord (writeWord mem 128 ⟨0⟩) 128 (UInt256.ofNat (takeReceiver offer receiver).val)

set_option maxRecDepth 10000

theorem midnightTakeReceiverSelect {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {offer : OfferData} {receiver : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hc : OfferCanonical offer)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat receiver.val)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12775⟩ (offer.buy :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (takeReceiverMemory mem offer receiver) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12792⟩ R
        (takeReceiverMemory mem offer receiver) aw' rdata σ k' C' := by
  have hmem : 416 ≤ mem.size := by
    have h := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at h
    omega
  have ho1 := ho.writeWord_below (off := 128) ⟨0⟩ (by decide)
  have hoffer1 : memLoad (UInt256.ofNat 384) (writeWord mem 128 ⟨0⟩) = ⟨832⟩ := by
    rw [memLoad_writeWord_preserved mem 128 (UInt256.ofNat 384) ⟨0⟩ hmem (Or.inr (by decide)), hoffer]
  have hreceiver1 : memLoad (UInt256.ofNat 288) (writeWord mem 128 ⟨0⟩) =
      UInt256.ofNat receiver.val := by
    rw [memLoad_writeWord_preserved mem 128 (UInt256.ofNat 288) ⟨0⟩ (by change 320 ≤ mem.size; omega)
      (Or.inr (by decide)), hreceiver]
  have ho_rec : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 288) (writeWord mem 128 ⟨0⟩) =
      UInt256.ofNat offer.receiverIfMakerIsSeller.val :=
    ho1.words.load_offset ⟨9, by change 9 < 15; decide⟩ rfl
  have hclean : UInt256.land (UInt256.ofNat offer.receiverIfMakerIsSeller.val) solcAddrMask =
      UInt256.ofNat offer.receiverIfMakerIsSeller.val :=
    addressWord_val_clean offer.receiverIfMakerIsSeller
  rcases hc.buy with hb | hb
  · have rd1 := midnight_block_12775_taken (by omega) (by rw [hb]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnight_block_12775_taken_memory
      memory_fund ha)
    change MemoryFunding credit (writeWord mem 128 ⟨0⟩) _ _ at ha1
    change RD fork _ _ _ _ ⟨14064⟩ R (writeWord mem 128 ⟨0⟩) _ _ _ _ _ at rd1
    have rd2 := midnight_block_14064 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by
      unfold midnight_block_14064_memory
      memory_fund ha1)
    simp only [midnight_block_14064_memory, hoffer1, ho_rec, addressMask_computed, hclean]
      at rd2 ha2
    simp only [takeReceiverMemory, takeReceiver, hb, if_true]
    exact ⟨_, _, _, ha2, rd2⟩
  · have hb0 : offer.buy ≠ ⟨0⟩ := by rw [hb]; decide
    have rd1 := midnight_block_12775_fallthrough (by omega) (by rw [hb]; decide) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnight_block_12775_fallthrough_memory
      memory_fund ha)
    change MemoryFunding credit (writeWord mem 128 ⟨0⟩) _ _ at ha1
    change RD fork _ _ _ _ ⟨12785⟩ R (writeWord mem 128 ⟨0⟩) _ _ _ _ _ at rd1
    have rd2 := midnight_block_12785 (by omega) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by
      unfold midnight_block_12785_memory
      memory_fund ha1)
    simp only [midnight_block_12785_memory, hreceiver1] at rd2 ha2
    simp only [takeReceiverMemory, takeReceiver, if_neg hb0]
    exact ⟨_, _, _, ha2, rd2⟩

end Benchmarks.Midnight
