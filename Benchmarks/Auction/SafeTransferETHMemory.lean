import Benchmarks.Auction.SafeTransferETHReturn
import Benchmarks.Auction.SafeTransferAllocator
import Benchmarks.Auction.CreateAuctionErrorCopyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: copying an available nonempty byte range covers its destination.
theorem auctionByteCopy_covers (src mem : ByteArray) {off len : Nat}
    (hpos : len ≠ 0) (hsrc : len ≤ src.size) (hoff : off ≤ mem.size) :
    off + len ≤ (src.write 0 mem off len).size := by
  by_cases hin : off + len ≤ mem.size
  · rw [write_eq_gen _ _ _ _ hpos hsrc hin]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  · rw [write_eq_gen_extend _ _ _ _ hpos hsrc hoff (by omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

theorem auctionPayoutFreeWord {out : ByteArray} (hsize : out.size < 2 ^ 64)
    (hne : out.size ≠ 0) :
    (⟨352⟩ : UInt256) + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩) =
      UInt256.ofNat (auctionPayoutFreeNat out.size) := by
  have hs : out.size + 63 < UInt256.size := by norm_num [UInt256.size]; omega
  have hround : (UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toNat =
      auctionRoundedMemoryNat (out.size + 32) := by
    rw [uland_toNat, lnot31_toNat, uadd_toNat,
      UInt256.toNat_ofNat_of_lt (by omega : out.size < UInt256.size)]
    change (((out.size + 63) % UInt256.size) &&& (UInt256.size - 32)) = _
    rw [Nat.mod_eq_of_lt hs, Nat.land_comm]
    rfl
  have hb := auctionRoundedMemoryNat_le (out.size + 32)
  have hn : 352 + auctionRoundedMemoryNat (out.size + 32) < UInt256.size := by
    norm_num [UInt256.size]; omega
  apply u256_inj
  rw [uadd_toNat, hround]
  change (352 + auctionRoundedMemoryNat (out.size + 32)) % UInt256.size = _
  rw [Nat.mod_eq_of_lt hn]
  simp only [auctionPayoutFreeNat, if_neg hne, UInt256.toNat_ofNat_of_lt hn]

theorem auctionETHReturnedState_memory {mem out : ByteArray} {aw : UInt256}
    (hmem : 384 ≤ mem.size) (hread : mem.readWithPadding 64 32 = (⟨352⟩ : UInt256).toByteArray)
    (haw : 12 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hsize : out.size < 2 ^ 64) :
    let state := auctionETHReturnedState mem aw out
    let free := UInt256.ofNat (auctionPayoutFreeNat out.size)
    free.toNat = auctionPayoutFreeNat out.size ∧
    state.1.readWithPadding 64 32 = free.toByteArray ∧
    384 ≤ state.1.size ∧ 12 ≤ state.2.toNat ∧ state.2.toNat * 32 < UInt256.size ∧
    352 ≤ free.toNat ∧ free.toNat < 2 ^ 68 ∧
    free.toNat + 2 ^ 64 + 128 < UInt256.size ∧
    free.toNat - state.1.size < USize.size ∧
    state.1.readWithPadding 224 32 = mem.readWithPadding 224 32 := by
  dsimp only
  have hfreeLe := auctionPayoutFreeNat_le out.size
  have hfreeBound : auctionPayoutFreeNat out.size < UInt256.size := by
    norm_num [UInt256.size]; omega
  have hfreeNat := UInt256.toNat_ofNat_of_lt hfreeBound
  have hfreeLow : 352 ≤ auctionPayoutFreeNat out.size := by
    unfold auctionPayoutFreeNat
    split <;> omega
  have hfreeSmall : auctionPayoutFreeNat out.size < 2 ^ 68 := by omega
  have hfreeCap : auctionPayoutFreeNat out.size + 2 ^ 64 + 128 < UInt256.size := by
    norm_num [UInt256.size]; omega
  refine ⟨hfreeNat, ?_⟩
  rw [hfreeNat]
  by_cases hz : out.size = 0
  · have hf : UInt256.ofNat (auctionPayoutFreeNat out.size) = (⟨352⟩ : UInt256) := by
      simp only [auctionPayoutFreeNat, hz, if_pos rfl]; rfl
    simp only [auctionETHReturnedState, if_pos hz, Prod.fst, Prod.snd, hf]
    refine ⟨hread, hmem, haw, hawSize, hfreeLow, hfreeSmall, hfreeCap, ?_, rfl⟩
    have hf0 : auctionPayoutFreeNat out.size = 352 := by simp only [auctionPayoutFreeNat, hz, if_pos rfl]
    rw [hf0, Nat.sub_eq_zero_of_le (by omega : 352 ≤ mem.size)]
    exact lt_usize _ (by omega)
  · let free := UInt256.ofNat (auctionPayoutFreeNat out.size)
    let mf := free.toByteArray.write 0 mem 64 32
    let ml := (UInt256.ofNat out.size).toByteArray.write 0 mf 352 32
    have hmfs : mf.size = mem.size :=
      toByteArray_write32_size_of_le _ _ _ mem.size mem.size rfl (by omega) (by omega)
    have hmls : ml.size = mem.size :=
      toByteArray_write32_size_of_le _ _ _ mem.size mem.size hmfs (by omega) (by omega)
    have hload : auctionLoadWord mem aw ⟨64⟩ = ⟨352⟩ :=
      mload64_of_readWithPadding_of_aw (by omega) hread (by omega) hawSize
    have hg64 : auctionGrowWords aw ⟨64⟩ 32 = aw :=
      auctionGrowWords_inBounds (by change 64 + 32 ≤ 32 * aw.toNat; omega)
    have hg352 : auctionGrowWords aw ⟨352⟩ 32 = aw :=
      auctionGrowWords_inBounds (by change 352 + 32 ≤ 32 * aw.toNat; omega)
    have hstate : auctionETHReturnedState mem aw out =
        (out.write 0 ml 384 out.size, auctionGrowWords aw ⟨384⟩ out.size) := by
      simp only [auctionETHReturnedState, if_neg hz, hload, hg64, auctionStoreWord,
        auctionPayoutFreeWord hsize hz, hg352,
        show (⟨352⟩ : UInt256) + ⟨32⟩ = ⟨384⟩ by decide,
        UInt256.toNat_ofNat_of_lt (lt_trans hsize (by decide))]
      rfl
    rw [hstate]
    have hsz : 384 + out.size ≤ (out.write 0 ml 384 out.size).size :=
      auctionByteCopy_covers out ml hz (by omega) (by rw [hmls]; omega)
    have hb := auctionGrowWords_positive_bounds (aw := aw) (off := ⟨384⟩)
      (Nat.pos_of_ne_zero hz) (by omega) hawSize (by change 384 + out.size + 31 < UInt256.size
                                                 norm_num [UInt256.size]; omega)
    have haw12 : 12 ≤ (auctionGrowWords aw ⟨384⟩ out.size).toNat := by
      have hh := hb.2.2
      change 384 + out.size ≤ 32 * (auctionGrowWords aw ⟨384⟩ out.size).toNat at hh
      omega
    refine ⟨?_, by omega, haw12, hb.2.1, hfreeLow, hfreeSmall, hfreeCap, ?_, ?_⟩
    · rw [write_read_below_gen_extend out ml 384 out.size 64 hz (by omega)
        (by rw [hmls]; omega) (by decide)]
      change ml.readWithPadding 64 32 = free.toByteArray
      rw [show ml = (UInt256.ofNat out.size).toByteArray.write 0 mf 352 32 from rfl,
        write32_read_below _ _ _ _ (by rw [toByteArray_size]) (by rw [hmfs]; omega) (by decide)]
      exact toByteArray_write_read_back_of_gap free mem 64 (by
        rw [Nat.sub_eq_zero_of_le (by omega : 64 ≤ mem.size)]; exact lt_usize _ (by omega))
    · have hu : USize.size = 2 ^ 64 := by native_decide
      rw [hu]
      omega
    · rw [write_read_below_gen_extend out ml 384 out.size 224 hz (by omega)
        (by rw [hmls]; omega) (by decide)]
      change ml.readWithPadding 224 32 = _
      rw [show ml = (UInt256.ofNat out.size).toByteArray.write 0 mf 352 32 from rfl,
        write32_read_below _ _ _ _ (by rw [toByteArray_size]) (by rw [hmfs]; omega) (by decide)]
      exact write32_read_above _ mem 64 224 (by rw [toByteArray_size]) (by omega) (by decide) (by omega)

end Auction
