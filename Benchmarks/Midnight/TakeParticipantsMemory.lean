import Benchmarks.Midnight.TakeParticipantsSource

/-! The two saved participant addresses preserve the surrounding take frame. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeParticipantsInitMemory (mem : ByteArray) : ByteArray :=
  writeWord (writeWord mem 576 ⟨0⟩) 448 ⟨0⟩

def takeParticipantsMemory (mem : ByteArray) (offer : OfferData) (taker : UInt256) : ByteArray :=
  writeWord (writeWord (takeParticipantsInitMemory mem) 576 (takeBuyer offer taker))
    448 (takeSeller offer taker)

theorem takeParticipantsInitMemory_size (mem : ByteArray) :
    mem.size ≤ (takeParticipantsInitMemory mem).size := by
  simp only [takeParticipantsInitMemory, writeWord_sparse_size]
  omega

theorem takeParticipantsMemory_size (mem : ByteArray) (offer : OfferData) (taker : UInt256) :
    mem.size ≤ (takeParticipantsMemory mem offer taker).size := by
  simp only [takeParticipantsMemory, takeParticipantsInitMemory, writeWord_sparse_size]
  omega

theorem takeParticipantsInitMemory_load {mem : ByteArray} (read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hb : read.toNat + 32 ≤ 576 ∨ 608 ≤ read.toNat)
    (hs : read.toNat + 32 ≤ 448 ∨ 480 ≤ read.toNat) :
    memLoad read (takeParticipantsInitMemory mem) = memLoad read mem := by
  rw [takeParticipantsInitMemory, memLoad_writeWord_preserved _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hs, memLoad_writeWord_preserved _ _ _ _ hin hb]

theorem takeParticipantsMemory_load {mem : ByteArray} (offer : OfferData) (taker read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hb : read.toNat + 32 ≤ 576 ∨ 608 ≤ read.toNat)
    (hs : read.toNat + 32 ≤ 448 ∨ 480 ≤ read.toNat) :
    memLoad read (takeParticipantsMemory mem offer taker) = memLoad read mem := by
  have hi := hin.trans (takeParticipantsInitMemory_size mem)
  rw [takeParticipantsMemory, memLoad_writeWord_preserved _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hs, memLoad_writeWord_preserved _ _ _ _ hi hb,
    takeParticipantsInitMemory_load _ hin hb hs]

theorem takeParticipantsMemory_buyer (mem : ByteArray) (offer : OfferData) (taker : UInt256) :
    memLoad (UInt256.ofNat 576) (takeParticipantsMemory mem offer taker) = takeBuyer offer taker := by
  rw [takeParticipantsMemory, memLoad_writeWord_preserved _ _ (UInt256.ofNat 576) _
    (by rw [writeWord_sparse_size]; change 608 ≤ _; omega) (Or.inr (by decide))]
  exact memLoad_writeWord _ _ _

theorem takeParticipantsMemory_seller (mem : ByteArray) (offer : OfferData) (taker : UInt256) :
    memLoad (UInt256.ofNat 448) (takeParticipantsMemory mem offer taker) = takeSeller offer taker :=
  memLoad_writeWord _ _ _

theorem takeParticipantsInitMemory_offer {mem : ByteArray}
    {marketPtr arrayPtr callbackPtr root : UInt256} {offer : OfferData}
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takeParticipantsInitMemory mem) ⟨832⟩ marketPtr arrayPtr callbackPtr root offer :=
  (ho.writeWord_below (off := 576) ⟨0⟩ (by decide)).writeWord_below (off := 448) ⟨0⟩ (by decide)

theorem takeParticipantsMemory_offer {mem : ByteArray}
    {marketPtr arrayPtr callbackPtr root taker : UInt256} {offer : OfferData}
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takeParticipantsMemory mem offer taker) ⟨832⟩ marketPtr arrayPtr callbackPtr root
      offer :=
  ((takeParticipantsInitMemory_offer ho).writeWord_below (off := 576) (takeBuyer offer taker)
    (by decide)).writeWord_below (off := 448) (takeSeller offer taker) (by decide)

end Benchmarks.Midnight
