import Benchmarks.Auction.CreateAuctionCall
import Benchmarks.Auction.SettleAuctionEventMemory
import Benchmarks.Auction.CreateAuctionDecodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- Memory available to `_createAuction` after the settlement event. -/
structure AuctionCreateMemoryValid (mem : ByteArray) (aw free : UInt256) : Prop where
  freeLow : 96 ≤ free.toNat
  freeBound : free.toNat + 95 < UInt256.size
  memCover : free.toNat + 64 ≤ mem.size
  wordsLow : 3 ≤ aw.toNat
  wordsBound : aw.toNat * 32 < UInt256.size
  wordsCover : free.toNat + 64 ≤ 32 * aw.toNat
  read64 : mem.readWithPadding 64 32 = free.toByteArray

theorem AuctionCreateMemoryValid.load64 {mem : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) : auctionLoadWord mem aw ⟨64⟩ = free := by
  apply mloadWordValue_of_readWithPadding
  · have := hm.memCover; have := hm.freeLow; change 64 < mem.size; omega
  · apply u256_not_ge_mul32_of_cover hm.wordsBound
    have := hm.wordsLow; change 64 + 32 ≤ 32 * aw.toNat; omega
  · exact hm.read64

theorem AuctionCreateMemoryValid.grow64 {mem : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) : auctionGrowWords aw ⟨64⟩ 32 = aw := by
  apply auctionGrowWords_inBounds
  have := hm.wordsLow; change 64 + 32 ≤ 32 * aw.toNat; omega

theorem AuctionCreateMemoryValid.growFree {mem : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) {len : Nat} (hlen : len ≤ 64) :
    auctionGrowWords aw free len = aw := by
  apply auctionGrowWords_inBounds
  have := hm.wordsCover; omega

theorem AuctionCreateMemoryValid.selector {mem : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) :
    AuctionCreateMemoryValid (auctionCreateAuctionMintSelMemAt mem free) aw free := by
  have hmem : free.toNat ≤ mem.size := by have := hm.memCover; omega
  refine ⟨hm.freeLow, hm.freeBound, ?_, hm.wordsLow, hm.wordsBound, hm.wordsCover, ?_⟩
  · rw [auctionCreateAuctionMintSelMemAt,
      toByteArray_write32_size_of_le _ _ _ mem.size mem.size rfl hmem (by
        have := hm.memCover; omega)]
    exact hm.memCover
  · exact (write32_read_below _ _ _ _ (by rw [toByteArray_size]) hmem hm.freeLow).trans hm.read64

theorem AuctionCreateMemoryValid.returnCopy {mem out : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) (hout : out.size < UInt256.size) :
    AuctionCreateMemoryValid
      (out.write 0 mem free.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      aw free := by
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
  have hlen32 : len ≤ 32 := auctionSettleAuctionTransferReturnCopyLen_le32
  have hsrc : len ≤ out.size := auctionSettleAuctionTransferReturnCopyLen_le_size hout
  by_cases hz : len = 0
  · simpa only [show (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 from hz,
      byteArray_write_len_zero] using hm
  have hin : free.toNat + len ≤ mem.size := by have := hm.memCover; omega
  refine ⟨hm.freeLow, hm.freeBound, ?_, hm.wordsLow, hm.wordsBound, hm.wordsCover, ?_⟩
  · change free.toNat + 64 ≤ (out.write 0 mem free.toNat len).size
    rw [write_eq_gen out mem free.toNat len hz hsrc hin]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    have := hm.memCover; omega
  · exact (write_read_below_gen out mem free.toNat len 64 hz hsrc hin hm.freeLow).trans hm.read64

theorem AuctionCreateMemoryValid.decodeWord {mem out : ByteArray} {aw free nounId : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) (hout : out.size < UInt256.size)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat))) :
    let returned := out.write 0 mem free.toNat
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    auctionLoadWord (auctionMintDecodedMemory free returned out) aw free = nounId := by
  intro returned
  have ho32 := auctionDecodeReturn_uint256_size_ge32 hdec
  have hmin := auctionUnpauseMintCallCopyLen_eq32 (o := out) ho32 hout
  have hsize : returned.size = mem.size := by
    dsimp only [returned]
    rw [hmin, write32_eq _ _ _ ho32 (by have := hm.memCover; omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    have := hm.memCover; omega
  have hdecodedSize : (auctionMintDecodedMemory free returned out).size = mem.size := by
    rw [auctionMintDecodedMemory, auctionStoreWord,
      toByteArray_write32_size_of_le _ _ _ mem.size mem.size hsize]
    · have := hm.memCover; have := hm.freeLow; change 64 ≤ returned.size; omega
    · have := hm.memCover; have := hm.freeLow; change max mem.size (64 + 32) = mem.size; omega
  have hread : (auctionMintDecodedMemory free returned out).readWithPadding free.toNat 32 =
      out.extract 0 32 := by
    dsimp only [auctionMintDecodedMemory, auctionStoreWord]
    change ((UInt256.add free (UInt256.land (UInt256.lnot ⟨31⟩)
      (UInt256.add (UInt256.ofNat out.size) ⟨31⟩))).toByteArray.write 0 returned 64 32).readWithPadding
      free.toNat 32 = out.extract 0 32
    rw [write32_read_above
      (UInt256.add free (UInt256.land (UInt256.lnot ⟨31⟩)
        (UInt256.add (UInt256.ofNat out.size) ⟨31⟩))).toByteArray returned 64 free.toNat
      (by rw [toByteArray_size]) (by have := hm.memCover; have := hm.freeLow; omega)
      hm.freeLow (by have := hm.memCover; omega)]
    dsimp only [returned]
    rw [hmin]
    exact write32_read_back _ _ _ ho32 (by have := hm.memCover; omega)
  have hmnot : ¬ free.toNat ≥ (auctionMintDecodedMemory free returned out).size := by
    rw [hdecodedSize]; have := hm.memCover; omega
  have hawnot : ¬ free ≥ aw * ⟨32⟩ :=
    u256_not_ge_mul32_of_cover hm.wordsBound (by have := hm.wordsCover; omega)
  simp only [auctionLoadWord, if_neg (not_or.mpr ⟨hmnot, hawnot⟩), hread]
  exact auctionDecodeReturn_uint256_word hdec

end Auction
