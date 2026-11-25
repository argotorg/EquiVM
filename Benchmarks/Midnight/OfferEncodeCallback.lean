import Benchmarks.Midnight.OfferEncodeFirst

variable {fork : Ethereum.Fork}

/-! The callback address and dynamic callback-data offset in an encoded offer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def offerEncodeCallbackMemory (mem : ByteArray) (output offset : UInt256)
    (offer : OfferData) : ByteArray :=
  writeWordArray mem (output.toNat + 224) [UInt256.ofNat offer.callback.val, offset]

set_option maxHeartbeats 800000 in
theorem midnightOfferEncodeCallback_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr output marketPtr callbackPtr finish : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (offer : OfferData)
    (hstack : R.length + 10 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (offer.words marketPtr callbackPtr))
    (hbelow : ptr.toNat + 480 ≤ output.toNat) (hout : output.toNat + 288 < UInt256.size)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨20243⟩
      (ptr :: ⟨224⟩ :: solcAddrMask :: finish :: ⟨20270⟩ :: ⟨448⟩ :: ⟨448⟩ :: output :: ptr :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit
        (offerEncodeCallbackMemory mem output (UInt256.sub finish output) offer) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨20095⟩
        (callbackPtr :: finish :: ⟨20270⟩ :: ⟨448⟩ :: ⟨448⟩ :: output :: ptr :: R)
        (offerEncodeCallbackMemory mem output (UInt256.sub finish output) offer)
        aw' rdata σ k' C' := by
  have hadd (off : Nat) (h : off ≤ 256) :
      (output + UInt256.ofNat off).toNat = output.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hc : memLoad (ptr + UInt256.ofNat 224) mem = UInt256.ofNat offer.callback.val :=
    hm.load_offset ⟨7, by change 7 < 15; decide⟩ rfl
  have hm1 := hm.writeWord (UInt256.ofNat offer.callback.val)
    (off := (output + UInt256.ofNat 224).toNat) (Or.inl (by
      rw [hadd 224 (by decide)]; change ptr.toNat + 32 * 15 ≤ _; omega))
  have hd : memLoad (ptr + UInt256.ofNat 256)
      (writeWord mem (output + UInt256.ofNat 224).toNat (UInt256.ofNat offer.callback.val)) =
      callbackPtr := hm1.load_offset ⟨8, by change 8 < 15; decide⟩ rfl
  have rd1 := midnightBlocks.midnight_block_20243 (x1 := UInt256.ofNat 224)
    hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_20243_memory
    memory_fund ha)
  have hr := And.intro ha1 rd1
  simp only [midnightBlocks.midnight_block_20243_stack,
    midnightBlocks.midnight_block_20243_memory, writeWord_fold, hc,
    solcAddrMask_clean (addressWord_canonical offer.callback)] at hr
  rw [hd] at hr
  simp only [hadd 224 (by decide), hadd 256 (by decide)] at hr
  simp only [offerEncodeCallbackMemory, writeWordArray, Nat.add_assoc, Nat.reduceAdd]
  exact ⟨_, _, _, hr⟩

end Benchmarks.Midnight
