import Benchmarks.Midnight.OfferBytesMemory
import Benchmarks.Midnight.MarketBytesFunding

variable {fork : Ethereum.Fork}

/-! Offer encoding retains gas funding and checks its dynamic allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem offerBytesAllocationEnd {root : UInt256} (offer : OfferData)
    (hb : root.toNat + offerBytesSize offer + 32 < 2^64) :
    allocationEnd root (UInt256.ofNat (offerBytesSize offer + 32)) =
      root + UInt256.ofNat (offerBytesSize offer + 32) := by
  have hs : (UInt256.ofNat (offerBytesSize offer + 32)).toNat = offerBytesSize offer + 32 :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hr : (offerBytesSize offer + 32 + 31) / 32 * 32 = offerBytesSize offer + 32 := by
    simp only [offerBytesSize, offerEncodedSize, offerCallbackOffset, paddedSize]
    omega
  apply u256_inj
  rw [allocationEnd_toNat (by rw [hs]; change _ < 2^256; omega)
    (by rw [hs, hr]; change _ < 2^256; omega), hs, hr,
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]

set_option maxRecDepth 10000

theorem midnightOfferBytesEncode_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr marketPtr arrayPtr callbackPtr limit root ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (offer : OfferData)
    (hstack : R.length + 25 ≤ 1024)
    (ho : OfferStored mem ptr marketPtr arrayPtr callbackPtr limit offer)
    (hc : OfferCanonical offer) (hlimit : limit.toNat ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 128 < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hgas : midnightGasBound g.toUInt256)
    (ha : MemoryFunding credit (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨20131⟩
      (ptr :: (root + UInt256.ofNat 64) :: ⟨12824⟩ :: root :: ret :: root :: R)
      (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (root.toNat + offerBytesSize offer + 32 + 2^62 < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding (credit + 128 * offer.market.collaterals.length +
          3 * ((offer.callbackData.size + 31) / 32))
          (offerBytesMemory mem root callbackPtr offer) aw' C' ∧
        RD fork midnightBytecode I g s0 ret (root :: R)
          (offerBytesMemory mem root callbackPtr offer) aw' rdata σ k' C') := by
  have h64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hp := memoryPrefix_writeWord mem (root.toNat + 32) limit.toNat (UInt256.ofNat 32)
    (Or.inl (by omega))
  have ho1 := ho.preserve hp
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightOfferEncoder_funded offer
    (by simp only [List.length_cons]; omega) ho1 hc (by rw [h64]; omega)
    (by rw [h64]; omega) (by jump_dest) ha rd
  have hpad : paddedSize offer.callbackData.size < 2^64 := by
    have hh := ho.extent
    have hl := ho.bound
    omega
  have hbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat :=
    ho.extent.trans hlimit
  have hsize := (offerBytesDataMemory_spec offer ho.callback hpad hbelow hb).2.1
  rcases memoryAccounting_headroom rd1 ha1.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  have hfitRoom : root.toNat + offerBytesSize offer + 32 + 2^62 < 2^64 := by
    change (offerBytesDataMemory mem root callbackPtr offer).size + 2^62 < 2^64 at hroom
    omega
  have hfit : root.toNat + offerBytesSize offer + 32 < 2^64 := by omega
  refine Or.inr ⟨hfitRoom, ?_⟩
  have hend : (root + UInt256.ofNat 64) + UInt256.ofNat (offerEncodedSize offer) =
      root + UInt256.ofNat (offerBytesSize offer + 32) := by
    rw [wordAddNat_add]
    congr 2
    unfold offerBytesSize
    omega
  have hsub : UInt256.sub ((root + UInt256.ofNat 64) +
      UInt256.ofNat (offerEncodedSize offer)) root =
      UInt256.ofNat (offerBytesSize offer + 32) := by rw [hend, word_add_sub_left]
  have hlength : UInt256.ofNat (offerBytesSize offer + 32) + UInt256.lnot (UInt256.ofNat 31) =
      UInt256.ofNat (offerBytesSize offer) := by
    rw [addNot31_ofNat (by omega) (by change _ < 2^256; omega)]
    congr 1
  have rd2 := midnightBlocks.midnight_block_12824 (by omega) (by jump_dest) rd1
  have ha2 := memoryFundingAt
    (credit := credit + 128 * offer.market.collaterals.length +
      3 * ((offer.callbackData.size + 31) / 32)) rd2 (by
      unfold midnightBlocks.midnight_block_12824_memory
      memory_fund ha1)
  simp only [midnightBlocks.midnight_block_12824_stack,
    midnightBlocks.midnight_block_12824_memory, hsub, hlength] at rd2 ha2
  have he := offerBytesAllocationEnd offer hfit
  have hcheck : allocationCheck root (allocationEnd root (UInt256.ofNat (offerBytesSize offer + 32)))
      = ⟨0⟩ := by
    rw [he]
    apply allocationCheck_ok
    · rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]; omega
    · rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]; omega
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightAllocate_funded
    (by simp only [List.length_cons]; omega) hcheck hret ha2 rd2
  rw [he] at rd3 ha3
  exact ⟨aw3, k3, C3, ha3, rd3⟩

end Benchmarks.Midnight
