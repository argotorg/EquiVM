import Benchmarks.Midnight.TakeContinuousRead
import Benchmarks.Midnight.TakeBuyerPendingRuntime

/-! Join the source pending-fee calculation to its checked runtime arithmetic. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightTakeBuyerPending {gasCredit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw id units taker debt credit buyerSlot time buyerDebt sellerSlot decrease ratifierPtr
      increase : UInt256} {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hs : SourceState s0 I evm.accountMap evm) (ha : MemoryFunding gasCredit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12118⟩
      ([debt, UInt256.ofNat 12138, UInt256.ofNat 12144, takePendingScale, UInt256.ofNat 12150,
        credit, buyerSlot, time, buyerDebt, sellerSlot, solcMappingSlot ⟨1⟩ id, decrease,
        ratifierPtr, increase] ++ R) mem aw rdata evm.accountMap k C) :
    (ExecBlock config frame evm (takeTransition.body.drop 38) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    (let rate := marketContinuousFee (marketFeeWord evm id)
     let value := takeBuyerPendingValue rate time increase
     let frame' := takeBuyerPendingFrame frame rate time increase
     value.toNat < 2^128 ∧
     ABlock config evm frame (takeTransition.body.drop 38) frame' (takeTransition.body.drop 40) ∧
     TakeSourceFrame frame' offer id units taker receiver callback ratifierData data ∧
     ∃ k' C', MemoryFunding gasCredit mem aw C' ∧
       RD midnightBytecode I g s0 ⟨12150⟩
         ([value, credit, buyerSlot, debt, buyerDebt, sellerSlot, solcMappingSlot ⟨1⟩ id,
           decrease, ratifierPtr, increase] ++ R) mem aw rdata evm.accountMap k' C') := by
  have hword : marketFeeWord evm id =
      solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) evm.accountMap I := by
    simpa only [marketFeeWord] using hs.storageRead (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
  obtain ⟨k1, C1, hC1, rd1⟩ := midnightTakeContinuousRead_mono (by omega) rd
  rw [← hword] at rd1
  rcases midnightTakeBuyerPendingRuntime hstack rd1 with ⟨hbad, hr⟩ | ⟨hgood, k2, C2, hC2, rd2⟩
  · exact Or.inl ⟨takeBuyerPendingSourceRevert hf.contract hm ht hi hbad, hr⟩
  · exact Or.inr ⟨hgood.2.2, takeBuyerPendingSource hf.contract hm ht hi hgood,
      hf.buyerPending, k2, C2, ha.mono (hC1.trans hC2), rd2⟩

end Benchmarks.Midnight
