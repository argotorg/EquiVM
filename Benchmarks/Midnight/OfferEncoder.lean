import Benchmarks.Midnight.OfferEncodeCallback
import Benchmarks.Midnight.OfferEncodeLast
import Benchmarks.Midnight.MarketEncoderFunding
import Benchmarks.Midnight.MemoryBytesEncodeMemory
import Benchmarks.Midnight.BytesCalldataMemory

/-! The complete offer ABI encoder, with funding and the original offer preserved. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def offerCallbackOffset (offer : OfferData) : Nat := 768 + 128 * offer.market.collaterals.length

def offerEncodedSize (offer : OfferData) : Nat :=
  offerCallbackOffset offer + 32 + paddedSize offer.callbackData.size

def offerEncodeMemory (mem : ByteArray) (callbackPtr output : UInt256)
    (offer : OfferData) : ByteArray :=
  let head := writeWord mem output.toNat (UInt256.ofNat 480)
  let market := marketEncodeMemory head (output.toNat + 480) offer.market
  let first := writeWordArray market (output.toNat + 32) offer.encodeFirstWords
  let callback := offerEncodeCallbackMemory first output (UInt256.ofNat (offerCallbackOffset offer)) offer
  let bytes := memoryBytesEncodeMemory callback callbackPtr.toNat
    (output.toNat + offerCallbackOffset offer) offer.callbackData.size
  writeWordArray bytes (output.toNat + 288) offer.encodeLastWords

set_option maxHeartbeats 800000 in
theorem midnightOfferEncoder_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr marketPtr arrayPtr callbackPtr root output ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (offer : OfferData)
    (hstack : R.length + 22 ≤ 1024)
    (ho : OfferStored mem ptr marketPtr arrayPtr callbackPtr root offer)
    (hc : OfferCanonical offer) (hbelow : root.toNat ≤ output.toNat)
    (hout : output.toNat + offerEncodedSize offer + 64 < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨20131⟩ (ptr :: output :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding (credit + 128 * offer.market.collaterals.length +
        3 * ((offer.callbackData.size + 31) / 32))
        (offerEncodeMemory mem callbackPtr output offer) aw' C' ∧
      RD midnightBytecode I g s0 ret ((output + UInt256.ofNat (offerEncodedSize offer)) :: R)
        (offerEncodeMemory mem callbackPtr output offer) aw' rdata σ k' C' := by
  have hlayout := ho.layout
  have harray := ho.market.array
  have hextent := ho.market.extent
  have hcallback := ho.extent
  have hpad := nat_le_paddedSize offer.callbackData.size
  have hout' : output.toNat + 864 + 128 * offer.market.collaterals.length +
      paddedSize offer.callbackData.size < UInt256.size := by
    unfold offerEncodedSize offerCallbackOffset at hout
    omega
  have hrecord : ptr.toNat + 480 ≤ output.toNat := by omega
  have hmarket : memLoad ptr mem = marketPtr :=
    ho.words.load_word ⟨0, by change 0 < 15; decide⟩ rfl
  let head := writeWord mem output.toNat (UInt256.ofNat 480)
  have ho0 : OfferStored head ptr marketPtr arrayPtr callbackPtr root offer :=
    ho.preserve (memoryPrefix_writeWord mem output.toNat root.toNat _ (Or.inl hbelow))
  have rd0 := midnightBlocks.midnight_block_20131 (by simp only [List.length_cons]; omega)
    (by jump_dest) rd
  have ha0 := memoryFundingAt (credit := credit) rd0 (by
    unfold midnightBlocks.midnight_block_20131_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_20131_stack, hmarket] at rd0
  have h480 : (output + UInt256.ofNat 480).toNat = output.toNat + 480 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hn : memLoad arrayPtr head = UInt256.ofNat offer.market.collaterals.length :=
    ho0.market.header.load_word ⟨0, by change 0 < 1; decide⟩ rfl
  have hnin : arrayPtr.toNat + 32 ≤ head.size := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.mul_one] using
      ho0.market.header.size
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightMarketEncoder_funded offer.market
    (by simp only [List.length_cons]; omega) ho0.market.words hn hnin ho0.market.collaterals
    (by omega) hextent (by rw [h480]; omega) (by rw [h480]; omega) (by jump_dest) ha0 rd0
  have hfinish : (output + UInt256.ofNat 480) +
      UInt256.ofNat (288 + 128 * offer.market.collaterals.length) =
      output + UInt256.ofNat (offerCallbackOffset offer) := by
    rw [wordAddNat_add]
    simp only [offerCallbackOffset, ← Nat.add_assoc, Nat.reduceAdd]
  simp only [h480, hfinish] at ha1 rd1
  let market := marketEncodeMemory head (output.toNat + 480) offer.market
  have ho1 : OfferStored market ptr marketPtr arrayPtr callbackPtr root offer :=
    ho0.preserve (marketEncodeMemory_prefix head _ root.toNat offer.market (by omega))
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightOfferEncodeFirst_funded offer
    (by simp only [List.length_cons]; omega) ho1.words hc hrecord (by omega) ha1 rd1
  let first := writeWordArray market (output.toNat + 32) offer.encodeFirstWords
  have ho2 : OfferStored first ptr marketPtr arrayPtr callbackPtr root offer :=
    ho1.preserve (memoryPrefix_writeWordArray market _ root.toNat _ (by omega))
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightOfferEncodeCallback_funded offer
    (by simp only [List.length_cons]; omega) ho2.words hrecord (by omega) ha2 rd2
  rw [word_add_sub_left] at ha3 rd3
  let callback := offerEncodeCallbackMemory first output
    (UInt256.ofNat (offerCallbackOffset offer)) offer
  have ho3 : OfferStored callback ptr marketPtr arrayPtr callbackPtr root offer :=
    ho2.preserve (memoryPrefix_writeWordArray first _ root.toNat _ (by omega))
  have hcptr : callbackPtr.toNat + 32 < UInt256.size := by
    have hb := ho.bound
    change _ < 2^256
    omega
  have hcfinish : (output + UInt256.ofNat (offerCallbackOffset offer)).toNat =
      output.toNat + offerCallbackOffset offer :=
    uadd_word_ofNat_toNat _ _ (by unfold offerCallbackOffset; omega)
  obtain ⟨aw4, k4, C4, ha4, rd4⟩ := midnightMemoryBytesEncoder_funded
    (by simp only [List.length_cons]; omega) ho3.callback.length hcptr
    (by rw [hcfinish]; unfold offerCallbackOffset; omega) ho3.callback.header
    (by jump_dest) ha3 rd3
  have hend : (output + UInt256.ofNat (offerCallbackOffset offer)) +
      UInt256.ofNat (returnDataAllocation offer.callbackData.size) =
      output + UInt256.ofNat (offerEncodedSize offer) := by
    rw [wordAddNat_add, returnDataAllocation_eq]
    unfold offerEncodedSize
    rw [Nat.add_assoc]
  simp only [hcfinish, hend] at ha4 rd4
  let bytes := memoryBytesEncodeMemory callback callbackPtr.toNat
    (output.toNat + offerCallbackOffset offer) offer.callbackData.size
  have ho4 : OfferStored bytes ptr marketPtr arrayPtr callbackPtr root offer :=
    ho3.preserve (memoryBytesEncodeMemory_prefix callback _ _ _ root.toNat
      (by have hs := ho3.callback.size; omega) (by unfold offerCallbackOffset; omega))
  obtain ⟨aw5, k5, C5, ha5, rd5⟩ := midnightOfferEncodeLast_funded offer (by omega)
    ho4.words hc hrecord (by omega) hret ha4 rd4
  exact ⟨aw5, k5, C5, ha5, rd5⟩

end Benchmarks.Midnight
