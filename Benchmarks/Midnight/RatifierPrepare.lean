import Benchmarks.Midnight.RatifierABI
import Benchmarks.Midnight.OfferEncodeMemory
import Benchmarks.Midnight.RuntimeBlocks_043

variable {fork : Ethereum.Fork}

/-! The runtime preparation of the ratifier's complete call buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def ratifierInputHead (mem : ByteArray) (root : Nat) : ByteArray :=
  writeWord (writeWord mem root (UInt256.ofNat (574377686 * 2^224)))
    (root + 4) (UInt256.ofNat 96)

def ratifierInputMemory (mem : ByteArray) (root callbackPtr ratifierPtr : UInt256)
    (offer : OfferData) (data : ByteArray) (taker : AccountAddress) : ByteArray :=
  let head := ratifierInputHead mem root.toNat
  let encoded := offerEncodeMemory head callbackPtr (root + UInt256.ofNat 100) offer
  let offset := writeWord encoded (root.toNat + 36) (UInt256.ofNat (96 + offerEncodedSize offer))
  let bytes := memoryBytesEncodeMemory offset ratifierPtr.toNat
    (root.toNat + 100 + offerEncodedSize offer) data.size
  writeWord bytes (root.toNat + 68) (UInt256.ofNat taker.val)

theorem ratifierInputHead_prefix (mem : ByteArray) (root : Nat) :
    MemoryPrefix mem (ratifierInputHead mem root) root :=
  (memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl)).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))

set_option maxHeartbeats 800000 in
theorem midnightRatifierPrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata data : ByteArray}
    {aw ptr marketPtr arrayPtr callbackPtr offerRoot root ratifierPtr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (offer : OfferData) (taker : AccountAddress)
    (hstack : R.length + 30 ≤ 1024) (hmem : 576 ≤ mem.size) (hlower : 576 ≤ root.toNat)
    (ho : OfferStored mem ptr marketPtr arrayPtr callbackPtr offerRoot offer)
    (hc : OfferCanonical offer) (hb : MemoryByteString mem ratifierPtr data)
    (hbelow : offerRoot.toNat ≤ root.toNat)
    (hrat : ratifierPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hout : root.toNat + ratifierCalldataSize offer data + 64 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hptr : memLoad (UInt256.ofNat 384) mem = ptr)
    (htaker : memLoad (UInt256.ofNat 544) mem = UInt256.ofNat taker.val)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11276⟩ (ratifierPtr :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C',
      MemoryFunding (credit + 128 * offer.market.collaterals.length +
        3 * ((offer.callbackData.size + 31) / 32) + 3 * ((data.size + 31) / 32))
        (ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11378⟩
        ([gasArg, UInt256.ofNat offer.ratifier.val, root,
          UInt256.ofNat (ratifierCalldataSize offer data), root, ⟨32⟩, root, ratifierPtr] ++ R)
        (ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker) aw' rdata σ k' C' := by
  have hpad := nat_le_paddedSize data.size
  have hcpad : paddedSize offer.callbackData.size < 2^64 := by
    have he := ho.extent
    have hb := ho.bound
    omega
  have hoff : root.toNat + 100 + offerEncodedSize offer + 96 + data.size < UInt256.size := by
    unfold ratifierCalldataSize at hout
    omega
  have hn (n : Nat) (h : n ≤ 100 + offerEncodedSize offer + 32 + paddedSize data.size) :
      (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by unfold ratifierCalldataSize at hout; omega)
  have h100 := hn 100 (by omega)
  have hsel : UInt256.shiftLeft (UInt256.ofNat 287188843) (UInt256.ofNat 225) =
      UInt256.ofNat (574377686 * 2^224) := by decide +kernel
  let head := ratifierInputHead mem root.toNat
  have hp0 : MemoryPrefix mem head root.toNat := ratifierInputHead_prefix mem root.toNat
  have ho0 := ho.preserve (hp0.mono hbelow)
  have hb0 := hb.preserve hp0 hrat
  have hptr0 : memLoad (UInt256.ofNat 384) head = ptr := by
    rw [hp0.load _ (by decide) (by change 416 ≤ _; omega) (by exact Nat.le_trans (by decide) hmem),
      hptr]
  have hratifier : memLoad (ptr + UInt256.ofNat 320) mem = UInt256.ofNat offer.ratifier.val :=
    ho.words.load_offset ⟨10, by change 10 < 15; decide⟩ rfl
  have rd0 := midnightBlocks.midnight_block_11276 (by simp only [List.length_cons]; omega)
    (by jump_dest) rd
  have ha0 := memoryFundingAt (credit := credit) rd0 (by
    unfold midnightBlocks.midnight_block_11276_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_11276_memory, hfree, hptr, hsel,
    hn 4 (by omega)] at ha0
  simp only [midnightBlocks.midnight_block_11276_stack,
    midnightBlocks.midnight_block_11276_memory, hfree, hptr, hratifier,
    addressMask_computed, solcAddrMask_clean (addressWord_canonical offer.ratifier),
    hsel, hn 4 (by omega)] at rd0
  change MemoryFunding credit head _ _ at ha0
  change RD fork midnightBytecode I g s0 ⟨20131⟩
    (memLoad (UInt256.ofNat 384) head :: (root + UInt256.ofNat 100) ::
      UInt256.ofNat 11338 :: UInt256.ofNat 11356 :: root :: root ::
      UInt256.ofNat offer.ratifier.val :: root :: UInt256.ofNat 32 :: root :: ratifierPtr :: R)
    head _ rdata σ _ _ at rd0
  rw [hptr0] at rd0
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightOfferEncoder_funded offer
    (by simp only [List.length_cons]; omega) ho0 hc (by rw [h100]; omega)
    (by rw [h100]; omega) (by jump_dest) ha0 rd0
  let encoded := offerEncodeMemory head callbackPtr (root + UInt256.ofNat 100) offer
  have he1 : (root + UInt256.ofNat 100) + UInt256.ofNat (offerEncodedSize offer) =
      root + UInt256.ofNat (100 + offerEncodedSize offer) := wordAddNat_add _ _ _
  rw [he1] at rd1
  have hp1 := (offerEncodeMemory_spec (output := root + UInt256.ofNat 100) offer ho0.callback hcpad
    (by rw [h100]; have he := ho.extent; omega) (by rw [h100]; omega)).2.2.1
  have hb1 : MemoryByteString encoded ratifierPtr data :=
    hb0.preserve hp1 (by rw [h100]; omega)
  have rd2 := midnightBlocks.midnight_block_11338
    (by omega) (by jump_dest) rd1
  have ha2 := memoryFundingAt
    (credit := credit + 128 * offer.market.collaterals.length +
      3 * ((offer.callbackData.size + 31) / 32)) rd2 (by
    unfold midnightBlocks.midnight_block_11338_memory
    memory_fund ha1)
  have hdelta : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat (100 + offerEncodedSize offer) =
      UInt256.ofNat (96 + offerEncodedSize offer) := by
    have hh : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat 100 = UInt256.ofNat 96 :=
      by decide +kernel
    rw [← wordAddNat_add, hh]
    apply u256_inj
    simp only [uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  simp only [midnightBlocks.midnight_block_11338_stack,
    midnightBlocks.midnight_block_11338_memory, word_add_sub_left, hdelta,
    hn 36 (by omega)] at ha2 rd2
  let offset := writeWord encoded (root.toNat + 36) (UInt256.ofNat (96 + offerEncodedSize offer))
  have hp2 : MemoryPrefix encoded offset root.toNat :=
    memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))
  have hb2 := hb1.preserve hp2 hrat
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightMemoryBytesEncoder_funded
    (by simp only [List.length_cons]; omega) hb2.length
    (by have h := hb.bound; omega) (by rw [hn _ (by omega)]; omega) hb2.header
    (by jump_dest) ha2 rd2
  have he2 : (root + UInt256.ofNat (100 + offerEncodedSize offer)) +
      UInt256.ofNat (returnDataAllocation data.size) =
      root + UInt256.ofNat (ratifierCalldataSize offer data) := by
    rw [wordAddNat_add, returnDataAllocation_eq]
    unfold ratifierCalldataSize
    congr 2
    omega
  simp only [hn (100 + offerEncodedSize offer) (by omega), he2, ← Nat.add_assoc] at ha3 rd3
  let bytes := memoryBytesEncodeMemory offset ratifierPtr.toNat
    (root.toNat + 100 + offerEncodedSize offer) data.size
  have hp3 : MemoryPrefix offset bytes root.toNat :=
    memoryBytesEncodeMemory_prefix _ _ _ _ _ (by have h := hb2.size; omega) (by omega)
  have hp := hp0.trans ((hp1.mono (by rw [h100]; omega)).trans (hp2.trans hp3))
  have htaker3 : memLoad (UInt256.ofNat 544) bytes = UInt256.ofNat taker.val := by
    rw [hp.load (UInt256.ofNat 544) (by decide) hlower hmem, htaker]
  have rd4 := midnightBlocks.midnight_block_11356
    (by simp only [List.length_cons]; omega) rd3
  have ha4 := memoryFundingAt
    (credit := credit + 128 * offer.market.collaterals.length +
      3 * ((offer.callbackData.size + 31) / 32) + 3 * ((data.size + 31) / 32)) rd4 (by
    unfold midnightBlocks.midnight_block_11356_memory
    memory_fund ha3)
  change memLoad (UInt256.ofNat 544) (memoryBytesEncodeMemory offset ratifierPtr.toNat
    (root.toNat + 100 + offerEncodedSize offer) data.size) = _ at htaker3
  have hf := And.intro ha4 rd4
  simp only [midnightBlocks.midnight_block_11356_stack,
    midnightBlocks.midnight_block_11356_memory, word_add_sub_left, hn 68 (by omega),
    addressMask_computed] at hf
  rw [htaker3] at hf
  simp only [solcAddrMask_clean (addressWord_canonical taker)] at hf
  exact ⟨_, _, _, _, by
    simpa only [ratifierInputMemory, head, encoded, offset, Reasoning.Theory.writeWord,
      Nat.add_assoc, List.cons_append, List.nil_append] using hf⟩

end Benchmarks.Midnight
