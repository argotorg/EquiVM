import Benchmarks.Auction.CreateAuctionErrorCopyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def auctionCreateErrorRoundedWord (off len : Nat) : UInt256 :=
  UInt256.land (UInt256.lnot ⟨31⟩)
    (((UInt256.ofNat off + UInt256.ofNat len) + ⟨32⟩) + ⟨31⟩)

theorem auctionCreateErrorRoundedWord_toNat {off len : Nat}
    (hsum : off + len + 63 < UInt256.size) :
    (auctionCreateErrorRoundedWord off len).toNat = errorStringRoundedAllocNat off len :=
  errorStringRoundedAllocWord_toNat hsum

theorem auctionCreateErrorNewFree_toNat {free : UInt256} {off len : Nat}
    (hfree : free.toNat < 2 ^ 68) (hoff : off ≤ ABI.solcMaxU64) (hlen : len ≤ ABI.solcMaxU64) :
    (free + auctionCreateErrorRoundedWord off len).toNat =
      free.toNat + errorStringRoundedAllocNat off len := by
  have hsum : off + len + 63 < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoff hlen ⊢
    omega
  have hround : errorStringRoundedAllocNat off len ≤ off + len + 63 := Nat.and_le_right
  have hbound : free.toNat + errorStringRoundedAllocNat off len < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoff hlen ⊢
    omega
  rw [uadd_toNat, auctionCreateErrorRoundedWord_toNat hsum, Nat.mod_eq_of_lt hbound]

theorem auctionCreateErrorAllocationWithinU64 {free : UInt256} {off len : Nat}
    (hfree : free.toNat < 2 ^ 68) (hoff : off ≤ ABI.solcMaxU64) (hlen : len ≤ ABI.solcMaxU64)
    (halloc : free.toNat + errorStringRoundedAllocNat off len ≤ ABI.solcMaxU64) :
    UInt256.gt (free + auctionCreateErrorRoundedWord off len) ⟨0xffffffffffffffff⟩ = ⟨0⟩ := by
  apply ugt_zero
  change (free + auctionCreateErrorRoundedWord off len).toNat ≤ ABI.solcMaxU64
  rwa [auctionCreateErrorNewFree_toNat hfree hoff hlen]

theorem auctionCreateErrorAllocationExceedsU64 {free : UInt256} {off len : Nat}
    (hfree : free.toNat < 2 ^ 68) (hoff : off ≤ ABI.solcMaxU64) (hlen : len ≤ ABI.solcMaxU64)
    (halloc : ABI.solcMaxU64 < free.toNat + errorStringRoundedAllocNat off len) :
    UInt256.gt (free + auctionCreateErrorRoundedWord off len) ⟨0xffffffffffffffff⟩ = ⟨1⟩ := by
  apply ugt_one
  change ABI.solcMaxU64 < (free + auctionCreateErrorRoundedWord off len).toNat
  rwa [auctionCreateErrorNewFree_toNat hfree hoff hlen]

theorem auctionCreateErrorAllocationNoWrap {free : UInt256} {off len : Nat}
    (hfree : free.toNat < 2 ^ 68) (hoff : off ≤ ABI.solcMaxU64) (hlen : len ≤ ABI.solcMaxU64) :
    UInt256.lt (free + auctionCreateErrorRoundedWord off len) free = ⟨0⟩ := by
  apply ult_zero
  change free.toNat ≤ (free + auctionCreateErrorRoundedWord off len).toNat
  rw [auctionCreateErrorNewFree_toNat hfree hoff hlen]
  exact Nat.le_add_right _ _

theorem auctionCreateErrorPayloadEnd_toNat {free : UInt256} {off len : Nat}
    (hfree : free.toNat < 2 ^ 68) (hoff : off ≤ ABI.solcMaxU64) (hlen : len ≤ ABI.solcMaxU64) :
    (((free + UInt256.ofNat off) + UInt256.ofNat len) + ⟨32⟩).toNat =
      free.toNat + off + len + 32 := by
  have hbound : free.toNat + off + len + 32 < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoff hlen ⊢
    omega
  rw [uadd_toNat, uadd_toNat, uadd_toNat,
    UInt256.toNat_ofNat_of_lt (by omega : off < UInt256.size),
    UInt256.toNat_ofNat_of_lt (by omega : len < UInt256.size),
    show (⟨32⟩ : UInt256).toNat = 32 by rfl,
    Nat.mod_eq_of_lt (by omega : free.toNat + off < UInt256.size),
    Nat.mod_eq_of_lt (by omega : free.toNat + off + len < UInt256.size),
    Nat.mod_eq_of_lt hbound]

theorem auctionCreateErrorCopiedEnd_toNat {free : UInt256} {size : Nat}
    (hfree : free.toNat < 2 ^ 68) (hlong : 68 ≤ size) (hsize : size < 2 ^ 64) :
    ((free + UInt256.ofNat size) + UInt256.lnot (⟨3⟩ : UInt256)).toNat =
      free.toNat + size - 4 := by
  have hbound : free.toNat + size < UInt256.size := by
    norm_num [UInt256.size]
    omega
  have hnot3 : (UInt256.lnot (⟨3⟩ : UInt256)).toNat = UInt256.size - 4 := by decide
  rw [uadd_toNat, uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : size < UInt256.size),
    Nat.mod_eq_of_lt hbound, hnot3]
  have hsum : free.toNat + size + (UInt256.size - 4) =
      UInt256.size + (free.toNat + size - 4) := by
    have hcap : 4 ≤ UInt256.size := by decide
    omega
  rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : free.toNat + size - 4 < UInt256.size)]

theorem auctionCreateErrorPayloadWithin {free : UInt256} {off len size : Nat}
    (hfree : free.toNat < 2 ^ 68) (hlong : 68 ≤ size) (hsize : size < 2 ^ 64)
    (hoff : off ≤ ABI.solcMaxU64) (hlen : len ≤ ABI.solcMaxU64)
    (hbound : off + len + 36 ≤ size) :
    UInt256.gt (((free + UInt256.ofNat off) + UInt256.ofNat len) + ⟨32⟩)
      ((free + UInt256.ofNat size) + UInt256.lnot (⟨3⟩ : UInt256)) = ⟨0⟩ := by
  apply ugt_zero
  rw [auctionCreateErrorPayloadEnd_toNat hfree hoff hlen,
    auctionCreateErrorCopiedEnd_toNat hfree hlong hsize]
  omega

theorem auctionCreateErrorPayloadExceeds {free : UInt256} {off len size : Nat}
    (hfree : free.toNat < 2 ^ 68) (hlong : 68 ≤ size) (hsize : size < 2 ^ 64)
    (hoff : off ≤ ABI.solcMaxU64) (hlen : len ≤ ABI.solcMaxU64)
    (hbound : size < off + len + 36) :
    UInt256.gt (((free + UInt256.ofNat off) + UInt256.ofNat len) + ⟨32⟩)
      ((free + UInt256.ofNat size) + UInt256.lnot (⟨3⟩ : UInt256)) = ⟨1⟩ := by
  apply ugt_one
  rw [auctionCreateErrorPayloadEnd_toNat hfree hoff hlen,
    auctionCreateErrorCopiedEnd_toNat hfree hlong hsize]
  omega

end Auction
