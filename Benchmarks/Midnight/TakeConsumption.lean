import Benchmarks.Midnight.TakeConsumptionRuntime
import Benchmarks.Midnight.TakeConsumptionSource

/-! Source/runtime correspondence for the consumed counter's increment and cap check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem takeConsumedCap_lt128 {offer : OfferData} (hc : OfferCanonical offer) :
    (takeConsumedCap offer).toNat < 2^128 := by
  unfold takeConsumedCap
  split
  · exact hc.maxUnits
  · exact hc.maxAssets

theorem TakeConsumptionSafe.lt128 {old units bought sold : UInt256} {offer : OfferData}
    (hsafe : TakeConsumptionSafe old offer units bought sold) (hc : OfferCanonical offer) :
    (old + takeConsumedDelta offer units bought sold).toNat < 2^128 := by
  have hfit := lt_of_le_of_lt hsafe (takeConsumedCap offer).val.isLt
  have hadd : (old + takeConsumedDelta offer units bought sold).toNat =
      old.toNat + (takeConsumedDelta offer units bought sold).toNat := addWord_toNat _ _ hfit
  rw [hadd]
  exact lt_of_le_of_lt hsafe (takeConsumedCap_lt128 hc)

theorem midnightTakeConsumption {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr root id units taker bought sold : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hstack : R.length + 5 ≤ 1024)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hc : OfferCanonical offer) (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hu : calldataWord I.calldata 68 = units)
    (hbm : memLoad (UInt256.ofNat 256) mem = bought)
    (hsm : memLoad (UInt256.ofNat 416) mem = sold)
    (hstate : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11681⟩ R mem aw rdata σ k C) :
    (ExecBlock config frame evm (takeTransition.body.drop 25) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    (let old := takeConsumedStored evm offer
     let value := old + takeConsumedDelta offer units bought sold
     value.toNat < 2^128 ∧
     ABlock config evm frame (takeTransition.body.drop 25)
       (takeConsumptionFrame frame old offer units bought sold) (takeTransition.body.drop 27) ∧
     TakeSourceFrame (takeConsumptionFrame frame old offer units bought sold) offer id units taker
       receiver callback ratifierData data ∧
     ∃ aw' k' C', MemoryFunding credit (takeConsumptionMemory mem offer value) aw' C' ∧
       RD midnightBytecode I g s0 ⟨11826⟩ R
         (takeConsumptionMemory mem offer value) aw' rdata σ k' C') := by
  have hword : takeConsumedStored evm offer = takeConsumedWord σ I offer := by
    unfold takeConsumedStored consumedStored takeConsumedWord
    rw [hstate.storageRead]
    rfl
  have hx := midnightTakeConsumptionRuntime hstack ho hc hroot hu hbm hsm ha rd
  rw [← hword] at hx
  rcases hx with ⟨hbad, hr⟩ | ⟨hsafe, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨takeConsumptionSourceRevert hf hb hs hbad, hr⟩
  · exact Or.inr ⟨hsafe.lt128 hc, takeConsumptionSource hf hb hs hsafe, hf.consumption,
      aw1, k1, C1, ha1, rd1⟩

end Benchmarks.Midnight
