import Benchmarks.Midnight.TakeParticipantsMemory

variable {fork : Ethereum.Fork}

/-! Runtime selection and storage of the buyer and seller addresses. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeParticipantsRuntime {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root taker : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 4 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 544) mem = taker)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11826⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (takeParticipantsMemory mem offer taker) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11880⟩ R
        (takeParticipantsMemory mem offer taker) aw' rdata σ k' C' := by
  have hm : 576 ≤ mem.size := by
    have hh := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hh
    omega
  have hbuy : memLoad (UInt256.ofNat 32 + (⟨832⟩ : UInt256)) mem = offer.buy := by
    rw [u256_add_comm]
    exact ho.words.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  have hroot1 : memLoad (UInt256.ofNat 384) (takeParticipantsInitMemory mem) = ⟨832⟩ := by
    rw [takeParticipantsInitMemory_load (mem := mem) (UInt256.ofNat 384)
      (by change 416 ≤ mem.size; omega) (Or.inl (by decide)) (Or.inl (by decide)), hroot]
  have htaker1 : memLoad (UInt256.ofNat 544) (takeParticipantsInitMemory mem) = taker := by
    rw [takeParticipantsInitMemory_load (UInt256.ofNat 544) hm
      (Or.inl (by decide)) (Or.inr (by decide)), htaker]
  have ho1 := takeParticipantsInitMemory_offer ho
  have hmaker1 : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 64)
      (takeParticipantsInitMemory mem) = UInt256.ofNat offer.maker.val :=
    ho1.words.load_offset ⟨2, by change 2 < 15; decide⟩ rfl
  have htaker2 : memLoad (UInt256.ofNat 544)
      (writeWord (takeParticipantsInitMemory mem) 576 (UInt256.ofNat offer.maker.val)) = taker := by
    rw [memLoad_writeWord_preserved _ 576 (UInt256.ofNat 544) _
      (hm.trans (takeParticipantsInitMemory_size mem)) (Or.inl (by decide)), htaker1]
  by_cases hz : offer.buy = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_11826_taken hstack
      (by rw [hroot, hbuy, hz]; decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_11826_taken_memory] at rd1
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    change MemoryFunding credit (takeParticipantsInitMemory mem) _ _ at ha1
    change RD fork midnightBytecode I g s0 ⟨14545⟩ R
      (takeParticipantsInitMemory mem) _ rdata σ _ _ at rd1
    have rd2 := midnightBlocks.midnight_block_14545 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by
      simp only [midnightBlocks.midnight_block_14545_memory]
      memory_fund ha1)
    have hfinal : midnightBlocks.midnight_block_14545_memory
        (mem := takeParticipantsInitMemory mem) = takeParticipantsMemory mem offer taker := by
      simp only [midnightBlocks.midnight_block_14545_memory, hroot1, hmaker1, htaker1,
        addressMask_computed, solcAddrMask_clean (addressWord_canonical offer.maker)]
      simp only [takeParticipantsMemory, takeBuyer, takeSeller, if_pos hz]
      rfl
    rw [hfinal] at rd2 ha2
    exact ⟨_, _, _, ha2, rd2⟩
  · have rd1 := midnightBlocks.midnight_block_11826_fallthrough hstack
      (by rw [hroot, hbuy]; exact isZero_eq_zero_of_ne hz) rd
    simp only [midnightBlocks.midnight_block_11826_fallthrough_memory] at rd1
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    change MemoryFunding credit (takeParticipantsInitMemory mem) _ _ at ha1
    change RD fork midnightBytecode I g s0 ⟨11851⟩ R
      (takeParticipantsInitMemory mem) _ rdata σ _ _ at rd1
    have rd2 := midnightBlocks.midnight_block_11851 (by omega) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by
      simp only [midnightBlocks.midnight_block_11851_memory]
      memory_fund ha1)
    have hfinal : midnightBlocks.midnight_block_11851_memory
        (mem := takeParticipantsInitMemory mem) = takeParticipantsMemory mem offer taker := by
      simp only [midnightBlocks.midnight_block_11851_memory, hroot1, hmaker1,
        addressMask_computed, solcAddrMask_clean (addressWord_canonical offer.maker)]
      change writeWord (writeWord (takeParticipantsInitMemory mem) 576
        (UInt256.ofNat offer.maker.val)) 448
        (memLoad (UInt256.ofNat 544) (writeWord (takeParticipantsInitMemory mem) 576
          (UInt256.ofNat offer.maker.val))) = _
      rw [htaker2]
      simp only [takeParticipantsMemory, takeBuyer, takeSeller, if_neg hz]
    rw [hfinal] at rd2 ha2
    exact ⟨_, _, _, ha2, rd2⟩

end Benchmarks.Midnight
