import Benchmarks.Midnight.TakePositionsMemory

/-! The memory layout just before the conditional buyer update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takePositionPrepareMemory (mem : ByteArray) (offer : OfferData) (id taker : UInt256) :
    ByteArray :=
  takePositionsMemory (takeParticipantsMemory mem offer taker) id
    (takeBuyer offer taker) (takeSeller offer taker)

theorem takePositionPrepareMemory_size (mem : ByteArray) (offer : OfferData) (id taker : UInt256) :
    mem.size ≤ (takePositionPrepareMemory mem offer id taker).size :=
  (takeParticipantsMemory_size mem offer taker).trans
    (takePositionsMemory_prefix _ _ _ _ 0).size

theorem takePositionPrepareMemory_load {mem : ByteArray} (offer : OfferData)
    (id taker read : UInt256) (hlo : 64 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size)
    (hb : read.toNat + 32 ≤ 576 ∨ 608 ≤ read.toNat)
    (hs : read.toNat + 32 ≤ 448 ∨ 480 ≤ read.toNat) :
    memLoad read (takePositionPrepareMemory mem offer id taker) = memLoad read mem := by
  rw [takePositionPrepareMemory, takePositionsMemory_load _ _ _ read hlo
    (hin.trans (takeParticipantsMemory_size mem offer taker)),
    takeParticipantsMemory_load _ _ _ hin hb hs]

theorem takePositionPrepareMemory_buyer {mem : ByteArray} (offer : OfferData) (id taker : UInt256)
    (hm : 608 ≤ mem.size) :
    memLoad (UInt256.ofNat 576) (takePositionPrepareMemory mem offer id taker) =
      takeBuyer offer taker := by
  rw [takePositionPrepareMemory, takePositionsMemory_load _ _ _ (UInt256.ofNat 576)
    (by decide) (hm.trans (takeParticipantsMemory_size mem offer taker)),
    takeParticipantsMemory_buyer]

theorem takePositionPrepareMemory_seller {mem : ByteArray} (offer : OfferData) (id taker : UInt256)
    (hm : 480 ≤ mem.size) :
    memLoad (UInt256.ofNat 448) (takePositionPrepareMemory mem offer id taker) =
      takeSeller offer taker := by
  rw [takePositionPrepareMemory, takePositionsMemory_load _ _ _ (UInt256.ofNat 448)
    (by decide) (hm.trans (takeParticipantsMemory_size mem offer taker)),
    takeParticipantsMemory_seller]

theorem takePositionPrepareMemory_offer {mem : ByteArray}
    {offer : OfferData} {marketPtr arrayPtr callbackPtr root id taker : UInt256}
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takePositionPrepareMemory mem offer id taker) ⟨832⟩ marketPtr arrayPtr callbackPtr
      root offer :=
  (takeParticipantsMemory_offer ho).preserve (takePositionsMemory_prefix _ _ _ _ root.toNat)

end Benchmarks.Midnight
