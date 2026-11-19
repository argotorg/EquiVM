import Benchmarks.Midnight.TakeConsumptionMode
import Benchmarks.Midnight.TakeConsumptionValues

/-! The consumed mapping's scratch hashes preserve the take frame and offer heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem consumedHashMemory_size (mem : ByteArray) (group user : UInt256)
    (hm : 64 ≤ mem.size) : (consumedHashMemory mem group user).size = mem.size := by
  rw [consumedHashMemory, twoWordHashMem_size_of_ge_64 _ _ (by
    rw [twoWordHashMem_size_of_ge_64 _ _ hm]; exact hm), twoWordHashMem_size_of_ge_64 _ _ hm]

theorem consumedHashMemory_load {mem : ByteArray} (group user read : UInt256)
    (hlo : 64 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size) :
    memLoad read (consumedHashMemory mem group user) = memLoad read mem := by
  rw [consumedHashMemory, memLoad_twoWordHashMem _ _ _ hlo (by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hin),
    memLoad_twoWordHashMem _ _ _ hlo hin]

theorem consumedHashMemory_prefix (mem : ByteArray) (group user : UInt256) (limit : Nat) :
    MemoryPrefix mem (consumedHashMemory mem group user) limit :=
  (twoWordHashMem_prefix _ _ _ _).trans (twoWordHashMem_prefix _ _ _ _)

def takeConsumedWord (σ : AccountMap) (I : ExecutionEnv) (offer : OfferData) : UInt256 :=
  UInt256.land (solcSlotWordAt (consumedSlot offer.group (UInt256.ofNat offer.maker.val)) σ I)
    uint128Mask

def takeConsumptionReadMemory (mem : ByteArray) (offer : OfferData) : ByteArray :=
  consumedHashMemory (writeWord mem 480 ⟨0⟩) offer.group (UInt256.ofNat offer.maker.val)

def takeConsumptionMemory (mem : ByteArray) (offer : OfferData) (value : UInt256) : ByteArray :=
  writeWord (takeConsumptionReadMemory mem offer) 480 value

theorem takeConsumptionReadMemory_size (mem : ByteArray) (offer : OfferData) :
    mem.size ≤ (takeConsumptionReadMemory mem offer).size := by
  rw [takeConsumptionReadMemory, consumedHashMemory_size _ _ _ (by
    rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
  omega

theorem takeConsumptionReadMemory_load {mem : ByteArray} (offer : OfferData) (read : UInt256)
    (hlo : 64 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ 480 ∨ 512 ≤ read.toNat) :
    memLoad read (takeConsumptionReadMemory mem offer) = memLoad read mem := by
  rw [takeConsumptionReadMemory, consumedHashMemory_load _ _ _ hlo
    (by rw [writeWord_sparse_size]; omega), memLoad_writeWord_preserved _ _ _ _ hin hd]

theorem takeConsumptionReadMemory_offer {mem : ByteArray}
    {marketPtr arrayPtr callbackPtr root : UInt256} {offer : OfferData}
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takeConsumptionReadMemory mem offer) ⟨832⟩ marketPtr arrayPtr callbackPtr root
      offer :=
  (ho.writeWord_below (off := 480) ⟨0⟩ (by decide)).preserve
    (consumedHashMemory_prefix _ _ _ _)

theorem takeConsumptionMemory_load {mem : ByteArray} (offer : OfferData) (value read : UInt256)
    (hlo : 64 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ 480 ∨ 512 ≤ read.toNat) :
    memLoad read (takeConsumptionMemory mem offer value) = memLoad read mem := by
  rw [takeConsumptionMemory, memLoad_writeWord_preserved _ _ _ _
    (hin.trans (takeConsumptionReadMemory_size ..)) hd,
    takeConsumptionReadMemory_load _ _ hlo hin hd]

theorem takeConsumptionMemory_value (mem : ByteArray) (offer : OfferData) (value : UInt256) :
    memLoad (UInt256.ofNat 480) (takeConsumptionMemory mem offer value) = value :=
  memLoad_writeWord _ _ _

theorem takeConsumptionMemory_offer {mem : ByteArray}
    {marketPtr arrayPtr callbackPtr root value : UInt256} {offer : OfferData}
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takeConsumptionMemory mem offer value) ⟨832⟩ marketPtr arrayPtr callbackPtr root
      offer :=
  (takeConsumptionReadMemory_offer ho).writeWord_below value (by decide)

end Benchmarks.Midnight
