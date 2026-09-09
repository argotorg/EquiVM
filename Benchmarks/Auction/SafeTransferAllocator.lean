import Benchmarks.Auction.SafeTransferWethSavedMemory
import Benchmarks.Auction.SafeTransferWethWithMemory
import Benchmarks.Auction.SettleAuctionEventMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionRoundedMemoryWord_toNat {n : Nat} (hn : n + 31 < UInt256.size) :
    (UInt256.land (UInt256.add (UInt256.ofNat n) ⟨31⟩) (UInt256.lnot ⟨31⟩)).toNat =
      auctionRoundedMemoryNat n := by
  rw [uland_toNat, lnot31_toNat]
  change ((UInt256.ofNat n + ⟨31⟩).toNat &&& (UInt256.size - 32)) = _
  rw [uadd_toNat,
    UInt256.toNat_ofNat_of_lt (by omega : n < UInt256.size)]
  change Nat.land ((n + 31) % UInt256.size) (UInt256.size - 32) =
    Nat.land (UInt256.size - 32) (n + 31)
  rw [Nat.mod_eq_of_lt hn]
  exact Nat.land_comm _ _

theorem auctionWethDecodedMemory_allocator {mem out : ByteArray} {aw amount owner : UInt256}
    (hmem : 256 ≤ mem.size)
    (hbase : 256 ≤ (auctionSettleAuctionDynMload64 mem aw).toNat)
    (hbaseBound : (auctionSettleAuctionDynMload64 mem aw).toNat + 2 ^ 64 + 128 < UInt256.size)
    (hgap : (auctionSettleAuctionDynMload64 mem aw).toNat - mem.size < USize.size)
    (hout : 32 ≤ out.size) (hsize : out.size < 2 ^ 64)
    (haw : 10 ≤ (auctionWethTransferCallAw mem aw).toNat)
    (hawSize : (auctionWethTransferCallAw mem aw).toNat * 32 < UInt256.size)
    (hcover : (auctionSettleAuctionDynMload64 mem aw).toNat + 32 ≤
      32 * (auctionWethTransferCallAw mem aw).toNat) :
    let base := auctionSettleAuctionDynMload64 mem aw
    let free := UInt256.ofNat (base.toNat + auctionRoundedMemoryNat out.size)
    let returned := auctionSafeTransferDecodedMem base
      (auctionWethTransferReturnMem mem aw amount owner out) out
    let awReturned := auctionSafeTransferDecodedAw base (auctionWethTransferCallAw mem aw)
    free.toNat = base.toNat + auctionRoundedMemoryNat out.size ∧
    returned.readWithPadding 64 32 = free.toByteArray ∧ 96 ≤ returned.size ∧
    10 ≤ awReturned.toNat ∧ awReturned.toNat * 32 < UInt256.size ∧
    96 ≤ free.toNat ∧ free.toNat + 95 < UInt256.size ∧
    free.toNat - returned.size < USize.size := by
  dsimp only
  let base := auctionSettleAuctionDynMload64 mem aw
  let rounded := UInt256.land (UInt256.add (UInt256.ofNat out.size) ⟨31⟩)
    (UInt256.lnot ⟨31⟩)
  have hcap : 2 ^ 64 + 31 < UInt256.size := by native_decide
  have hround : rounded.toNat = auctionRoundedMemoryNat out.size :=
    auctionRoundedMemoryWord_toNat (by omega)
  have hroundLe := auctionRoundedMemoryNat_le out.size
  have hfreeBound : base.toNat + auctionRoundedMemoryNat out.size < UInt256.size := by
    change base.toNat + 2 ^ 64 + 128 < UInt256.size at hbaseBound
    omega
  have hfree : (UInt256.ofNat (base.toNat + auctionRoundedMemoryNat out.size)).toNat =
      base.toNat + auctionRoundedMemoryNat out.size := UInt256.toNat_ofNat_of_lt hfreeBound
  have hword : UInt256.add base rounded =
      UInt256.ofNat (base.toNat + auctionRoundedMemoryNat out.size) := by
    apply u256_inj
    change (base + rounded).toNat = _
    rw [uadd_toNat, hround, hfree, Nat.mod_eq_of_lt hfreeBound]
  have hm := auctionWethDecodedMemory_properties (amount := amount) (owner := owner)
    hmem hbase (by omega) hgap hout (by omega)
  rw [auctionSafeTransferDecodedAw_eq (by omega) hcover]
  refine ⟨hfree, ?_, ?_, haw, hawSize, ?_, ?_, ?_⟩
  · exact hm.2.2.trans (congrArg UInt256.toByteArray hword)
  · have h := hm.1
    omega
  · rw [hfree]
    change 256 ≤ base.toNat at hbase
    omega
  · rw [hfree]
    change base.toNat + 2 ^ 64 + 128 < UInt256.size at hbaseBound
    omega
  · rw [hfree]
    have h := hm.1
    have hU : USize.size = 2 ^ 64 := by native_decide
    rw [hU]
    dsimp only [base]
    omega

end Auction
