import Benchmarks.Midnight.TakeAmountsRuntime

/-! The two amount slots preserve the offer heap and all disjoint saved words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem takeAmountMemory_size (mem : ByteArray) (off : Nat) (amount : UInt256) :
    mem.size ≤ (takeAmountMemory mem off amount).size := by
  simp only [takeAmountMemory, writeWord_sparse_size]
  omega

theorem takeAmountMemory_load {mem : ByteArray} (off : Nat) (amount read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ off ∨ off + 32 ≤ read.toNat) :
    memLoad read (takeAmountMemory mem off amount) = memLoad read mem := by
  rw [takeAmountMemory, memLoad_writeWord_preserved _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hd, memLoad_writeWord_preserved _ _ _ _ hin hd]

theorem takeAmountMemory_self (mem : ByteArray) (off : UInt256) (amount : UInt256) :
    memLoad off (takeAmountMemory mem off.toNat amount) = amount :=
  memLoad_writeWord _ _ _

theorem takeAmountMemory_offer {mem : ByteArray} {marketPtr arrayPtr callbackPtr root : UInt256}
    {offer : OfferData} {off : Nat}
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hlo : off + 32 ≤ 832) (amount : UInt256) :
    OfferStored (takeAmountMemory mem off amount) ⟨832⟩ marketPtr arrayPtr callbackPtr root offer :=
  (ho.writeWord_below ⟨0⟩ hlo).writeWord_below amount hlo

def takeAmountsMemory (mem : ByteArray) (bought sold : UInt256) : ByteArray :=
  takeAmountMemory (takeAmountMemory mem 256 bought) 416 sold

theorem takeAmountsMemory_load {mem : ByteArray} (bought sold read : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hb : read.toNat + 32 ≤ 256 ∨ 288 ≤ read.toNat)
    (hs : read.toNat + 32 ≤ 416 ∨ 448 ≤ read.toNat) :
    memLoad read (takeAmountsMemory mem bought sold) = memLoad read mem := by
  rw [takeAmountsMemory, takeAmountMemory_load _ _ _
    (hin.trans (takeAmountMemory_size ..)) hs, takeAmountMemory_load _ _ _ hin hb]

theorem takeAmountsMemory_bought (mem : ByteArray) (bought sold : UInt256) :
    memLoad (UInt256.ofNat 256) (takeAmountsMemory mem bought sold) = bought := by
  rw [takeAmountsMemory, takeAmountMemory_load _ _ _
    (by simp only [takeAmountMemory, writeWord_sparse_size]; change 288 ≤ _; omega)
    (Or.inl (by decide))]
  exact takeAmountMemory_self mem (UInt256.ofNat 256) bought

theorem takeAmountsMemory_sold (mem : ByteArray) (bought sold : UInt256) :
    memLoad (UInt256.ofNat 416) (takeAmountsMemory mem bought sold) = sold :=
  takeAmountMemory_self _ (UInt256.ofNat 416) sold

end Benchmarks.Midnight
