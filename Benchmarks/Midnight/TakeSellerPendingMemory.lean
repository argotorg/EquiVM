import Benchmarks.Midnight.TakeSellerPendingSource

/-! Saved buyer and seller pending-fee amounts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSellerPendingInitMemory (mem : ByteArray) (buyerFee : UInt256) : ByteArray :=
  writeWord (writeWord mem 224 buyerFee) 160 ⟨0⟩

def takeSellerPendingMemory (mem : ByteArray) (buyerFee sellerFee : UInt256) : ByteArray :=
  writeWord (takeSellerPendingInitMemory mem buyerFee) 160 sellerFee

theorem takeSellerPendingInitMemory_size (mem : ByteArray) (buyerFee : UInt256) :
    mem.size ≤ (takeSellerPendingInitMemory mem buyerFee).size := by
  simp only [takeSellerPendingInitMemory, writeWord_sparse_size]
  omega

theorem takeSellerPendingInitMemory_load {mem : ByteArray} (buyerFee read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hb : read.toNat + 32 ≤ 224 ∨ 256 ≤ read.toNat)
    (hs : read.toNat + 32 ≤ 160 ∨ 192 ≤ read.toNat) :
    memLoad read (takeSellerPendingInitMemory mem buyerFee) = memLoad read mem := by
  rw [takeSellerPendingInitMemory, memLoad_writeWord_preserved _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hs, memLoad_writeWord_preserved _ _ _ _ hin hb]

theorem takeSellerPendingMemory_load {mem : ByteArray} (buyerFee sellerFee read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hb : read.toNat + 32 ≤ 224 ∨ 256 ≤ read.toNat)
    (hs : read.toNat + 32 ≤ 160 ∨ 192 ≤ read.toNat) :
    memLoad read (takeSellerPendingMemory mem buyerFee sellerFee) = memLoad read mem := by
  rw [takeSellerPendingMemory, memLoad_writeWord_preserved _ _ _ _
    (hin.trans (takeSellerPendingInitMemory_size mem buyerFee)) hs,
    takeSellerPendingInitMemory_load _ _ hin hb hs]

theorem takeSellerPendingMemory_buyer (mem : ByteArray) (buyerFee sellerFee : UInt256) :
    memLoad (UInt256.ofNat 224) (takeSellerPendingMemory mem buyerFee sellerFee) = buyerFee := by
  rw [takeSellerPendingMemory, memLoad_writeWord_preserved _ _ (UInt256.ofNat 224) _
    (by simp only [takeSellerPendingInitMemory, writeWord_sparse_size]; change 256 ≤ _; omega)
    (Or.inr (by decide)), takeSellerPendingInitMemory,
    memLoad_writeWord_preserved _ _ (UInt256.ofNat 224) _
      (by rw [writeWord_sparse_size]; change 256 ≤ _; omega) (Or.inr (by decide))]
  exact memLoad_writeWord mem (UInt256.ofNat 224) buyerFee

theorem takeSellerPendingMemory_seller (mem : ByteArray) (buyerFee sellerFee : UInt256) :
    memLoad (UInt256.ofNat 160) (takeSellerPendingMemory mem buyerFee sellerFee) = sellerFee :=
  memLoad_writeWord _ _ _

theorem takeSellerPendingMemory_offer {mem : ByteArray} {buyerFee sellerFee : UInt256}
    {marketPtr arrayPtr callbackPtr root : UInt256} {offer : OfferData}
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takeSellerPendingMemory mem buyerFee sellerFee) ⟨832⟩
      marketPtr arrayPtr callbackPtr root offer :=
  ((ho.writeWord_below (off := 224) buyerFee (by decide)).writeWord_below
    (off := 160) ⟨0⟩ (by decide)).writeWord_below (off := 160) sellerFee (by decide)

end Benchmarks.Midnight
