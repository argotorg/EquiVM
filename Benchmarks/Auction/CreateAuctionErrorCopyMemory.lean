import Benchmarks.Auction.CreateAuctionFailureMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: a bounded memory expansion with any positive access length.
theorem auctionGrowWords_positive_bounds {aw off : UInt256} {len : Nat}
    (hlen : 0 < len) (haw : 3 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hbound : off.toNat + len + 31 < UInt256.size) :
    3 ≤ (auctionGrowWords aw off len).toNat ∧
      (auctionGrowWords aw off len).toNat * 32 < UInt256.size ∧
      off.toNat + len ≤ 32 * (auctionGrowWords aw off len).toNat := by
  have hm : MachineState.M aw.toNat off.toNat len =
      max aw.toNat ((off.toNat + len + 31) / 32) := by
    simp [MachineState.M, Nat.ne_of_gt hlen]
  have hmWord : MachineState.M aw.toNat off.toNat len < UInt256.size := by
    rw [hm]
    exact max_lt aw.val.isLt (lt_of_le_of_lt (Nat.div_le_self _ _) hbound)
  simp only [auctionGrowWords, UInt256.toNat_ofNat_of_lt hmWord]
  refine ⟨le_trans haw (by rw [hm]; exact Nat.le_max_left _ _), ?_,
    auctionMachineState_M_pos_offset_len_le_words_mul hlen⟩
  rw [hm, max_mul]
  exact max_lt hawSize (lt_of_le_of_lt (Nat.div_mul_le_self _ _) hbound)

def auctionCreateErrorCopiedMemory (mem out : ByteArray) (free : UInt256) : ByteArray :=
  out.write 4 mem free.toNat (out.size - 4)

theorem auctionCreateErrorCopiedMemory_size {mem out : ByteArray} {free : UInt256}
    (hlong : 68 ≤ out.size) (hfree : free.toNat ≤ mem.size) :
    free.toNat + (out.size - 4) ≤ (auctionCreateErrorCopiedMemory mem out free).size := by
  unfold auctionCreateErrorCopiedMemory
  by_cases hin : free.toNat + (out.size - 4) ≤ mem.size
  · rw [write_eq_gen_from _ _ _ _ _ (by omega) (by omega) hin]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  · rw [write_eq_gen_from_extend _ _ _ _ _ (by omega) (by omega) hfree (by omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

theorem auctionCreateErrorCopiedMemory_read {mem out : ByteArray} {free : UInt256} {off : Nat}
    (hlong : 68 ≤ out.size) (hfree : free.toNat ≤ mem.size) (hoff : off + 36 ≤ out.size) :
    (auctionCreateErrorCopiedMemory mem out free).readWithPadding (free.toNat + off) 32 =
      (out.extract 4 out.size).readWithPadding off 32 := by
  have hext : off + 32 ≤ (out.extract 4 out.size).size := by
    simp only [ByteArray.size_extract]; omega
  rw [auctionCreateErrorCopiedMemory,
    write_from_read_window out mem 4 free.toNat (out.size - 4) off 32
      (by omega) (by decide) (by omega) (by omega) hfree (by decide),
    readWithPadding_eq_extract _ off hext, extract_extract_BA]
  congr 1
  omega

theorem auctionCreateErrorCopiedMemory_mload {mem out : ByteArray} {aw free : UInt256}
    {off word : Nat}
    (hm : AuctionCreateMemoryValid mem aw free) (hlong : 68 ≤ out.size)
    (hbound : free.toNat + out.size + 31 < UInt256.size)
    (hoff : off + 36 ≤ out.size)
    (hword : ABI.readNat? (out.extract 4 out.size).toList off = some word) :
    let awCopy := auctionGrowWords aw free (out.size - 4)
    auctionLoadWord (auctionCreateErrorCopiedMemory mem out free) awCopy
      (free + UInt256.ofNat off) = UInt256.ofNat word := by
  intro awCopy
  have haw := auctionGrowWords_positive_bounds (off := free) (by omega : 0 < out.size - 4)
    hm.wordsLow hm.wordsBound (by omega)
  have hfree : free.toNat ≤ mem.size := by have := hm.memCover; omega
  have hsize := auctionCreateErrorCopiedMemory_size hlong hfree
  have hoffSize : off < UInt256.size := by omega
  have haddr : (free + UInt256.ofNat off).toNat = free.toNat + off := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hoffSize]
    exact Nat.mod_eq_of_lt (by omega)
  have hnmem : ¬ (free + UInt256.ofNat off).toNat ≥
      (auctionCreateErrorCopiedMemory mem out free).size := by rw [haddr]; omega
  have hnaw : ¬ free + UInt256.ofNat off ≥ awCopy * ⟨32⟩ := by
    apply u256_not_ge_mul32_of_cover haw.2.1
    rw [haddr]
    have hc := haw.2.2
    omega
  rw [auctionLoadWord, if_neg (not_or.mpr ⟨hnmem, hnaw⟩), haddr,
    auctionCreateErrorCopiedMemory_read hlong hfree hoff]
  exact readNat?_some_mload_word hword

theorem auctionCreateErrorCopiedMemory_grow {mem out : ByteArray} {aw free : UInt256}
    {off : Nat} (hm : AuctionCreateMemoryValid mem aw free) (hlong : 68 ≤ out.size)
    (hbound : free.toNat + out.size + 31 < UInt256.size) (hoff : off + 36 ≤ out.size) :
    auctionGrowWords (auctionGrowWords aw free (out.size - 4))
      (free + UInt256.ofNat off) 32 = auctionGrowWords aw free (out.size - 4) := by
  have haw := auctionGrowWords_positive_bounds (off := free) (by omega : 0 < out.size - 4)
    hm.wordsLow hm.wordsBound (by omega)
  apply auctionGrowWords_inBounds
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : off < UInt256.size),
    Nat.mod_eq_of_lt (by omega : free.toNat + off < UInt256.size)]
  omega

end Auction
