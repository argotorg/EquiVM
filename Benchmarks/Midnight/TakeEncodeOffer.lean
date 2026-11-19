import Benchmarks.Midnight.OfferBytesFunding

/-! The trade's complete offer-encoding step, up to event preparation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeEncodeOffer {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr limit root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 26 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr limit offer)
    (hc : OfferCanonical offer) (hlimit : limit.toNat ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 128 < UInt256.size)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hgas : midnightGasBound g.toUInt256) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12792⟩ R mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (root.toNat + offerBytesSize offer + 32 + 2^62 < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding (credit + 128 * offer.market.collaterals.length +
          3 * ((offer.callbackData.size + 31) / 32))
          (offerBytesMemory mem root callbackPtr offer) aw' C' ∧
        RD midnightBytecode I g s0 ⟨12838⟩ (root :: (root + UInt256.ofNat 32) :: R)
          (offerBytesMemory mem root callbackPtr offer) aw' rdata σ k' C') := by
  have hroot : 416 ≤ root.toNat := by
    have h1 := ho.layout
    have h2 := ho.market.array
    have h3 := ho.market.extent
    have h4 := ho.extent
    change 832 + 480 ≤ marketPtr.toNat at h1
    omega
  have hmem : 416 ≤ mem.size := by
    have h := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at h
    omega
  have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hread : memLoad (UInt256.ofNat 384)
      (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) = ⟨832⟩ := by
    rw [memLoad_writeWord_preserved mem (root.toNat + 32) (UInt256.ofNat 384)
      (UInt256.ofNat 32) hmem (Or.inl (by change 416 ≤ root.toNat + 32; omega)), hoffer]
  have rd1 := midnightBlocks.midnight_block_12792 (by omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_12792_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_12792_stack,
    midnightBlocks.midnight_block_12792_memory, hfree, h32] at rd1 ha1
  change RD _ _ _ _ ⟨20131⟩
    (memLoad (UInt256.ofNat 384) (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) ::
      (root + UInt256.ofNat 64) :: ⟨12824⟩ :: root :: ⟨12838⟩ :: root ::
      (root + UInt256.ofNat 32) :: R)
    (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) _ _ _ _ _ at rd1
  rw [hread] at rd1
  exact midnightOfferBytesEncode_funded offer (by simp only [List.length_cons]; omega)
    ho hc hlimit hb (by jump_dest) hgas ha1 rd1

end Benchmarks.Midnight
