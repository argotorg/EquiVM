import Benchmarks.Midnight.TakeTimingGuard

/-! Only the receiver belonging to the seller side may be nonzero. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeUnusedReceiverWord (offer : OfferData) (receiver : AccountAddress) : UInt256 :=
  if offer.buy = ⟨0⟩ then UInt256.ofNat receiver.val
  else UInt256.ofNat offer.receiverIfMakerIsSeller.val

theorem midnightTakeReceiverGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData} {receiver : AccountAddress}
    (hstack : R.length + 3 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat receiver.val)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11171⟩ R mem aw rdata σ k C) :
    (takeUnusedReceiverWord offer receiver ≠ ⟨0⟩ ∧ RDrev midnightBytecode g s0) ∨
    (takeUnusedReceiverWord offer receiver = ⟨0⟩ ∧
      ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
        RD midnightBytecode I g s0 ⟨11209⟩ R mem aw' rdata σ k' C') := by
  have hbuy : memLoad (UInt256.ofNat 32 + (⟨832⟩ : UInt256)) mem = offer.buy := by
    rw [u256_add_comm]
    exact ho.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  have hrecv : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 288) mem =
      UInt256.ofNat offer.receiverIfMakerIsSeller.val :=
    ho.words.load_offset ⟨9, by change 9 < 15; decide⟩ rfl
  have finish {aw' k' C'} (word : UInt256) (ha' : MemoryFunding credit mem aw' C')
      (rd' : RD midnightBytecode I g s0 ⟨11203⟩ (UInt256.isZero word :: R)
        mem aw' rdata σ k' C') :
      (word ≠ ⟨0⟩ ∧ RDrev midnightBytecode g s0) ∨
      (word = ⟨0⟩ ∧ ∃ aw'' k'' C'', MemoryFunding credit mem aw'' C'' ∧
        RD midnightBytecode I g s0 ⟨11209⟩ R mem aw'' rdata σ k'' C'') := by
    by_cases hw : word = ⟨0⟩
    · have rd2 := midnightBlocks.midnight_block_11203_fallthrough (by omega)
        (by rw [hw]; rfl) rd'
      exact Or.inr ⟨hw, _, _, _, by memory_fund ha', rd2⟩
    · have rr := midnightBlocks.midnight_block_11203_taken (by omega)
        (by rw [isZero_eq_zero_of_ne hw]; decide) (by jump_dest) rd'
      exact Or.inl ⟨hw, midnightBlocks.midnight_block_14874 (by
        change R.length + 2 ≤ 1024; omega) rr⟩
  by_cases hb : offer.buy = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_11171_taken (by omega)
      (by rw [hroot, hbuy, hb]; decide) (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_14889 hstack (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_14889_stack, hreceiver, addressMask_computed,
      solcAddrMask_clean (addressWord_canonical receiver)] at rd2
    simpa only [takeUnusedReceiverWord, hb, if_true] using finish (UInt256.ofNat receiver.val) ha2 rd2
  · have rd1 := midnightBlocks.midnight_block_11171_fallthrough (by omega)
      (by rw [hroot, hbuy]; exact isZero_eq_zero_of_ne hb) rd
    have rd2 := midnightBlocks.midnight_block_11184 hstack rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_11184_stack, hroot, hrecv, addressMask_computed,
      solcAddrMask_clean (addressWord_canonical offer.receiverIfMakerIsSeller)] at rd2 ha2
    simpa only [takeUnusedReceiverWord, hb, if_false] using
      finish (UInt256.ofNat offer.receiverIfMakerIsSeller.val) ha2 rd2

end Benchmarks.Midnight
