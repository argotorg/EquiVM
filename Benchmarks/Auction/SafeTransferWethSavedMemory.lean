import Benchmarks.Auction.SafeTransferWethMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionSafeTransferDecodedAw_eq {base aw : UInt256}
    (haw : 3 ≤ aw.toNat) (hcover : base.toNat + 32 ≤ 32 * aw.toNat) :
    auctionSafeTransferDecodedAw base aw = aw := by
  have h64 : MachineState.M aw.toNat 64 32 = aw.toNat :=
    auctionMachineState_M_inBounds (by omega)
  have hbase : MachineState.M aw.toNat base.toNat 32 = aw.toNat :=
    auctionMachineState_M_inBounds (by omega)
  simp only [auctionSafeTransferDecodedAw, h64, u256_ofNat_toNat, hbase]

set_option maxHeartbeats 1000000 in
theorem auctionWethDecodedMemory_properties {mem out : ByteArray} {aw amount owner : UInt256}
    (hmem : 256 ≤ mem.size)
    (hfree : 256 ≤ (auctionSettleAuctionDynMload64 mem aw).toNat)
    (hptr : (auctionSettleAuctionDynMload64 mem aw).toNat + 99 < UInt256.size)
    (hgap : (auctionSettleAuctionDynMload64 mem aw).toNat - mem.size < USize.size)
    (hout : 32 ≤ out.size) (hsize : out.size < UInt256.size) :
    let decoded := auctionSafeTransferDecodedMem (auctionSettleAuctionDynMload64 mem aw)
      (auctionWethTransferReturnMem mem aw amount owner out) out
    (auctionSettleAuctionDynMload64 mem aw).toNat + 68 ≤ decoded.size ∧
    decoded.readWithPadding 224 32 = mem.readWithPadding 224 32 ∧
    decoded.readWithPadding 64 32 =
      (UInt256.add (auctionSettleAuctionDynMload64 mem aw)
        (UInt256.land (UInt256.add (UInt256.ofNat out.size) ⟨31⟩)
          (UInt256.lnot ⟨31⟩))).toByteArray := by
  let free := auctionSettleAuctionDynMload64 mem aw
  let dep := auctionSettleAuctionDynDepositMem mem aw
  let sel := auctionSettleAuctionDynTransferSelMem dep free
  let arg := auctionSettleAuctionDynTransferArgMem dep free amount owner
  let xfer := auctionWethTransferMem mem aw amount owner
  change 256 ≤ free.toNat at hfree
  change free.toNat + 99 < UInt256.size at hptr
  change free.toNat - mem.size < USize.size at hgap
  have h4 : (free + (⟨4⟩ : UInt256)).toNat = free.toNat + 4 := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change free.toNat + 4 < UInt256.size; omega)
  have h36 : (free + (⟨36⟩ : UInt256)).toNat = free.toNat + 36 := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change free.toNat + 36 < UInt256.size; omega)
  have hdsize : free.toNat + 32 ≤ dep.size :=
    toByteArray_write_size_ge_off_add32 _ _ _ hgap
  have hdread : dep.readWithPadding 224 32 = mem.readWithPadding 224 32 :=
    toByteArray_write_read_below_of_gap _ _ _ _ hmem hfree hgap
  have hssize : free.toNat + 32 ≤ sel.size :=
    toByteArray_write_size_ge_off_add32 _ _ _ (by
      have hz : free.toNat - dep.size = 0 := by omega
      rw [hz]; exact lt_usize _ (by omega))
  have hsread : sel.readWithPadding 224 32 = dep.readWithPadding 224 32 :=
    write32_read_below _ _ _ _ (by rw [toByteArray_size]) (by omega) hfree
  have hasize : free.toNat + 36 ≤ arg.size := by
    dsimp only [arg, auctionSettleAuctionDynTransferArgMem]
    rw [h4]
    exact (show free.toNat + 36 = free.toNat + 4 + 32 by omega) ▸
      toByteArray_write_size_ge_off_add32 _ _ _ (by
        have hz : free.toNat + 4 - sel.size = 0 := by omega
        rw [hz]; exact lt_usize _ (by omega))
  have haread : arg.readWithPadding 224 32 = sel.readWithPadding 224 32 := by
    dsimp only [arg, auctionSettleAuctionDynTransferArgMem]
    rw [h4]
    exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
      (by change free.toNat + 4 ≤ sel.size; omega) (by omega)
  have hxsize : free.toNat + 68 ≤ xfer.size := by
    dsimp only [xfer, auctionWethTransferMem, auctionSettleAuctionDynTransferMem]
    rw [h36]
    exact (show free.toNat + 68 = free.toNat + 36 + 32 by omega) ▸
      toByteArray_write_size_ge_off_add32 _ _ _ (by
        have hz : free.toNat + 36 - arg.size = 0 := by omega
        rw [hz]; exact lt_usize _ (by omega))
  have hxread : xfer.readWithPadding 224 32 = arg.readWithPadding 224 32 := by
    dsimp only [xfer, auctionWethTransferMem, auctionSettleAuctionDynTransferMem]
    rw [h36]
    exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
      (by change free.toNat + 36 ≤ arg.size; omega) (by omega)
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    have hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change 32 ≤ (UInt256.ofNat out.size).toNat
      rwa [UInt256.toNat_ofNat_of_lt hsize]
    simp only [min, hle, ↓reduceIte]
    rfl
  let returned := out.write 0 xfer free.toNat 32
  have hrsize : returned.size = xfer.size := by
    rw [show returned = out.write 0 xfer free.toNat 32 from rfl,
      write32_eq _ _ _ hout (by omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  have hrread : returned.readWithPadding 224 32 = xfer.readWithPadding 224 32 :=
    write32_read_below _ _ _ _ hout (by omega) hfree
  dsimp only [auctionWethTransferReturnMem]
  rw [hmin]
  change free.toNat + 68 ≤ (auctionSafeTransferDecodedMem free returned out).size ∧
    (auctionSafeTransferDecodedMem free returned out).readWithPadding 224 32 = _ ∧
    (auctionSafeTransferDecodedMem free returned out).readWithPadding 64 32 = _
  constructor
  · dsimp only [auctionSafeTransferDecodedMem]
    rw [toByteArray_write32_size_of_le _ _ 64 returned.size returned.size rfl
      (by omega) (by omega)]
    omega
  constructor
  · rw [auctionSafeTransferDecodedMem,
      write32_read_above _ _ 64 224 (by rw [toByteArray_size]) (by omega) (by omega) (by omega),
      hrread, hxread, haread, hsread, hdread]

  · exact toByteArray_write_read_back_of_gap _ _ _ (by
      have hz : 64 - returned.size = 0 := by omega
      rw [hz]
      exact lt_usize _ (by omega))

set_option maxHeartbeats 1000000 in
theorem auctionWethDecodedMemory_preserves224 {mem out : ByteArray} {aw amount owner : UInt256}
    (hmem : 256 ≤ mem.size)
    (hfree : 256 ≤ (auctionSettleAuctionDynMload64 mem aw).toNat)
    (hptr : (auctionSettleAuctionDynMload64 mem aw).toNat + 99 < UInt256.size)
    (hgap : (auctionSettleAuctionDynMload64 mem aw).toNat - mem.size < USize.size)
    (hout : 32 ≤ out.size) (hsize : out.size < UInt256.size) :
    let decoded := auctionSafeTransferDecodedMem (auctionSettleAuctionDynMload64 mem aw)
      (auctionWethTransferReturnMem mem aw amount owner out) out
    256 ≤ decoded.size ∧ decoded.readWithPadding 224 32 = mem.readWithPadding 224 32 := by
  have h := auctionWethDecodedMemory_properties (amount := amount) (owner := owner)
    hmem hfree hptr hgap hout hsize
  exact ⟨by have hs := h.1; omega, h.2.1⟩

theorem auctionWethDecodedMemory_load224 {mem out : ByteArray} {aw amount owner finish : UInt256}
    (hmem : 256 ≤ mem.size)
    (hfree : 256 ≤ (auctionSettleAuctionDynMload64 mem aw).toNat)
    (hptr : (auctionSettleAuctionDynMload64 mem aw).toNat + 99 < UInt256.size)
    (hgap : (auctionSettleAuctionDynMload64 mem aw).toNat - mem.size < USize.size)
    (hout : 32 ≤ out.size) (hsize : out.size < UInt256.size)
    (hread : mem.readWithPadding 224 32 = finish.toByteArray)
    (haw : 3 ≤ (auctionWethTransferCallAw mem aw).toNat)
    (hawMul : (auctionWethTransferCallAw mem aw).toNat * 32 < UInt256.size)
    (hcover : (auctionSettleAuctionDynMload64 mem aw).toNat + 32 ≤
      32 * (auctionWethTransferCallAw mem aw).toNat) :
    auctionLoadWord (auctionSafeTransferDecodedMem (auctionSettleAuctionDynMload64 mem aw)
      (auctionWethTransferReturnMem mem aw amount owner out) out)
      (auctionSafeTransferDecodedAw (auctionSettleAuctionDynMload64 mem aw)
        (auctionWethTransferCallAw mem aw)) ⟨224⟩ = finish := by
  have hd := auctionWethDecodedMemory_preserves224
    (amount := amount) (owner := owner) hmem hfree hptr hgap hout hsize
  rw [auctionSafeTransferDecodedAw_eq haw hcover]
  apply mloadWordValue_of_readWithPadding
  · exact Nat.lt_of_lt_of_le (by native_decide : 224 < 256) hd.1
  · apply u256_not_ge_mul32_of_cover hawMul
    change 224 + 32 ≤ 32 * (auctionWethTransferCallAw mem aw).toNat
    omega
  · exact hd.2.trans hread

end Auction
