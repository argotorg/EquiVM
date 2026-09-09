import Benchmarks.Auction.SettleAuctionEvent
import Benchmarks.Auction.SettleAuctionDynamicWethBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the active-word count is unchanged for an in-bounds access.
theorem auctionGrowWords_inBounds {aw off : UInt256} {len : Nat}
    (hcover : off.toNat + len ≤ 32 * aw.toNat) : auctionGrowWords aw off len = aw := by
  simp only [auctionGrowWords, auctionMachineState_M_inBounds hcover, u256_ofNat_toNat]

-- LIBRARY CANDIDATE: bounds for a dynamic 32-byte memory access.
theorem auctionGrowWords_bounds {aw off : UInt256}
    (haw : 3 ≤ aw.toNat) (hsize : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 63 < UInt256.size) :
    3 ≤ (auctionGrowWords aw off 32).toNat ∧
    (auctionGrowWords aw off 32).toNat * 32 < UInt256.size ∧
    off.toNat + 32 ≤ 32 * (auctionGrowWords aw off 32).toNat := by
  have h := auctionMachineState_M_word_bounds haw hsize hoff
  simpa only [auctionGrowWords, UInt256.toNat_ofNat_of_lt h.2.2.2] using
    (show 3 ≤ MachineState.M aw.toNat off.toNat 32 ∧
      MachineState.M aw.toNat off.toNat 32 * 32 < UInt256.size ∧
      off.toNat + 32 ≤ 32 * MachineState.M aw.toNat off.toNat 32 from
      ⟨h.1, h.2.1, h.2.2.1⟩)

theorem auctionSettleEventState_preservesFree {mem : ByteArray} {aw free : UInt256}
    (hmem : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = free.toByteArray)
    (haw : 10 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hfree : 96 ≤ free.toNat) (hfreeBound : free.toNat + 95 < UInt256.size)
    (hgap : free.toNat - mem.size < USize.size) :
    let afterEvent := auctionSettleEventState ⟨128⟩ mem aw
    afterEvent.1.readWithPadding 64 32 = free.toByteArray ∧
    free.toNat + 64 ≤ afterEvent.1.size ∧
    3 ≤ afterEvent.2.toNat ∧ afterEvent.2.toNat * 32 < UInt256.size ∧
    free.toNat + 64 ≤ 32 * afterEvent.2.toNat := by
  have h128 : auctionGrowWords aw ⟨128⟩ 32 = aw :=
    auctionGrowWords_inBounds (by change 128 + 32 ≤ 32 * aw.toNat; omega)
  have h256 : auctionGrowWords aw ⟨256⟩ 32 = aw :=
    auctionGrowWords_inBounds (by change 256 + 32 ≤ 32 * aw.toNat; omega)
  have h160 : auctionGrowWords aw ⟨160⟩ 32 = aw :=
    auctionGrowWords_inBounds (by change 160 + 32 ≤ 32 * aw.toNat; omega)
  have h64 : auctionGrowWords aw ⟨64⟩ 32 = aw :=
    auctionGrowWords_inBounds (by change 64 + 32 ≤ 32 * aw.toNat; omega)
  have hload : auctionLoadWord mem aw ⟨64⟩ = free :=
    mloadWordValue_of_readWithPadding (by change 64 < mem.size; omega)
      (u256_not_ge_mul32_of_cover hawSize (by change 64 + 32 ≤ 32 * aw.toNat; omega)) hread
  let winner := UInt256.land (auctionLoadWord mem aw ⟨256⟩)
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
  let amount := auctionLoadWord mem aw ⟨160⟩
  let memWinner := auctionStoreWord mem free winner
  let awWinner := auctionGrowWords aw free 32
  let memData := auctionStoreWord memWinner (free + ⟨32⟩) amount
  let awData := auctionGrowWords awWinner (free + ⟨32⟩) 32
  have hplus : (free + (⟨32⟩ : UInt256)).toNat = free.toNat + 32 := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change free.toNat + 32 < UInt256.size; omega)
  have hwsize : free.toNat + 32 ≤ memWinner.size :=
    toByteArray_write_size_ge_off_add32 _ _ _ hgap
  have hwread : memWinner.readWithPadding 64 32 = mem.readWithPadding 64 32 :=
    toByteArray_write_read_below_of_gap _ _ _ _ hmem hfree hgap
  have hdgap : free.toNat + 32 - memWinner.size < USize.size := by
    have hz : free.toNat + 32 - memWinner.size = 0 := by omega
    rw [hz]
    exact lt_usize _ (by omega)
  have hdsize : free.toNat + 64 ≤ memData.size := by
    dsimp only [memData, auctionStoreWord]
    rw [hplus]
    have h := toByteArray_write_size_ge_off_add32 amount memWinner (free.toNat + 32) hdgap
    omega
  have hdread : memData.readWithPadding 64 32 = free.toByteArray := by
    dsimp only [memData, auctionStoreWord]
    rw [hplus, toByteArray_write_read_below_of_gap _ _ _ _ (by omega) (by omega) hdgap,
      hwread, hread]
  have hawW := auctionGrowWords_bounds (aw := aw) (off := free) (by omega) hawSize (by omega)
  have hawD := auctionGrowWords_bounds (aw := awWinner) (off := free + ⟨32⟩)
    hawW.1 hawW.2.1 (by rw [hplus]; omega)
  have hawCover : free.toNat + 64 ≤ 32 * awData.toNat := by
    have h := hawD.2.2
    rw [hplus] at h
    exact h
  have hd64 : auctionGrowWords awData ⟨64⟩ 32 = awData :=
    auctionGrowWords_inBounds (by change 64 + 32 ≤ 32 * awData.toNat; omega)
  have hdload : auctionLoadWord memData awData ⟨64⟩ = free :=
    mloadWordValue_of_readWithPadding (by change 64 < memData.size; omega)
      (u256_not_ge_mul32_of_cover hawD.2.1 (by change 64 + 32 ≤ 32 * awData.toNat; omega))
      hdread
  have hlog : UInt256.sub (free + ⟨64⟩) free = ⟨64⟩ := by
    apply u256_inj
    have hsum : (free + (⟨64⟩ : UInt256)).toNat = free.toNat + 64 := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by change free.toNat + 64 < UInt256.size; omega)
    rw [usub_toNat (a := free + ⟨64⟩) (b := free) (by rw [hsum]; omega), hsum]
    change free.toNat + 64 - free.toNat = 64
    omega
  have hfinal : auctionGrowWords awData free 64 = awData := auctionGrowWords_inBounds hawCover
  have hstate : auctionSettleEventState ⟨128⟩ mem aw = (memData, awData) := by
    simp only [auctionSettleEventState, h128,
      show (⟨128⟩ : UInt256) + ⟨128⟩ = ⟨256⟩ by decide, h256,
      show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ by decide, h160, hload, h64]
    change (memData, auctionGrowWords
      (auctionGrowWords awData ⟨64⟩ 32) (auctionLoadWord memData awData ⟨64⟩)
      (UInt256.sub (free + ⟨64⟩) (auctionLoadWord memData awData ⟨64⟩)).toNat) = _
    rw [hdload, hd64, hlog]
    exact congrArg (fun w ↦ (memData, w)) hfinal
  dsimp only
  rw [hstate]
  exact ⟨hdread, hdsize, hawD.1, hawD.2.1, hawCover⟩

end Auction
