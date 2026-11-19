import Benchmarks.Midnight.TakePricingSource
import Benchmarks.Midnight.SettlementFunding
import Reasoning.ExternalCall

/-! Source/runtime correspondence for take's price, maturity, and settlement fee. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takePricingMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  twoWordHashMem id ⟨1⟩ (writeWord mem 800 ⟨0⟩)

theorem takePricingMemory_prefix (mem : ByteArray) (id : UInt256) :
    MemoryPrefix mem (takePricingMemory mem id) 800 :=
  (memoryPrefix_writeWord mem 800 800 ⟨0⟩ (Or.inl le_rfl)).trans
    (twoWordHashMem_prefix _ _ _ _)

theorem takePricingMemory_offer {mem : ByteArray} {marketPtr arrayPtr callbackPtr root id : UInt256}
    {offer : OfferData} (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takePricingMemory mem id) ⟨832⟩ marketPtr arrayPtr callbackPtr root offer :=
  (ho.writeWord_below (off := 800) ⟨0⟩ (by decide)).preserve (twoWordHashMem_prefix _ _ _ _)

theorem takePricingMemory_load {mem : ByteArray} (id read : UInt256)
    (hlo : 64 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size)
    (hdisj : read.toNat + 32 ≤ 800 ∨ 832 ≤ read.toNat) :
    memLoad read (takePricingMemory mem id) = memLoad read mem := by
  rw [takePricingMemory, memLoad_twoWordHashMem _ _ _ hlo
    (by rw [writeWord_sparse_size]; omega), memLoad_writeWord_preserved _ _ _ _ hin hdisj]

theorem midnightTakePricing {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr root id units taker slot ratifierPtr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hstack : R.length + 22 ≤ 1024)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11413⟩ (ratifierPtr :: slot :: R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (takeTransition.body.drop 17) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    (let fee := settlementFeeValue (marketFeeWord evm id) (takeTimeToMaturity I offer)
     ABlock config evm frame (takeTransition.body.drop 17) (takePricingFrame frame I offer fee)
       (takeTransition.body.drop 20) ∧
     TakeSourceFrame (takePricingFrame frame I offer fee) offer id units taker receiver callback
       ratifierData data ∧
     ∃ aw' k' C', MemoryFunding credit (takePricingMemory mem id) aw' C' ∧
       RD midnightBytecode I g s0 ⟨11556⟩
         (fee :: UInt256.ofNat 11591 :: tickPriceWord offer.tick.toNat :: slot :: ratifierPtr ::
           takeTimeToMaturity I offer :: R) (takePricingMemory mem id) aw' rdata σ k' C') := by
  have hword : marketFeeWord evm id =
      solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I := by
    simpa only [marketFeeWord] using hs.storageRead (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
  rcases midnightTakePriceGuard (by simp only [List.length_cons]; omega) ho hroot ha rd with
    ⟨hbad, hr⟩ | ⟨hbound, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨takePricingSourceRevert hf.contract hf.offerValue hf.idValue (Or.inl hbad), hr⟩
  · obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakePricePrepare (by omega) ho hroot hid ha1 rd1
    have hm : 64 ≤ (writeWord mem 800 ⟨0⟩).size := by rw [writeWord_sparse_size]; omega
    by_cases hz : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩
    · exact Or.inl ⟨takePricingSourceRevert hf.contract hf.offerValue hf.idValue (Or.inr hz),
        settlementInternalTraceRevert (by simp only [List.length_cons]; omega) hm
          (by rwa [← hword]) rd2⟩
    · obtain ⟨aw3, k3, C3, ha3, rd3⟩ := settlementInternalTrace_funded
        (by simp only [List.length_cons]; omega) hm (by jump_dest) (by rwa [← hword]) ha2 rd2
      have hx := takePricingSource hf.contract hf.offerValue hf.idValue hbound hz
      rw [hs.env] at hx
      rw [← hword] at rd3
      exact Or.inr ⟨hx, hf.pricing I, aw3, k3, C3, ha3, rd3⟩

end Benchmarks.Midnight
