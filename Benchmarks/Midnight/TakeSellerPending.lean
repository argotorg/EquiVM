import Benchmarks.Midnight.TakeSellerPendingRuntime

/-! Source/runtime correspondence for the seller's proportional pending-fee reduction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightTakeSellerPending {gasCredit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw id units taker seller buyerFee buyerSlot debt buyerDebt sellerSlot marketSlot
      decrease : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hmem : 384 ≤ mem.size)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hp : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hd : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hcanon : seller.toNat < EVM.addressModulus)
    (hw : memLoad (UInt256.ofNat 352) mem =
      EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id seller))
    (hle : decrease.toNat ≤ (positionFieldWord evm id seller 0).toNat)
    (ha : MemoryFunding gasCredit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12150⟩
      ([buyerFee, positionFieldWord evm id seller 0, buyerSlot, debt, buyerDebt, sellerSlot,
        marketSlot, decrease] ++ R) mem aw rdata evm.accountMap k C) :
    let credit := positionFieldWord evm id seller 0
    let pending := positionFieldWord evm id seller 1
    let value := takeSellerPendingValue credit pending decrease
    let frame' := takeSellerPendingFrame frame credit pending decrease
    let mem' := takeSellerPendingMemory mem buyerFee value
    value.toNat < 2^128 ∧
    ABlock config evm frame (takeTransition.body.drop 40) frame' (takeTransition.body.drop 42) ∧
    TakeSourceFrame frame' offer id units taker receiver callback ratifierData data ∧
    ∃ aw' k' C', MemoryFunding gasCredit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨12187⟩
        ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease] ++ R)
        mem' aw' rdata evm.accountMap k' C' := by
  obtain ⟨hbound, aw1, k1, C1, ha1, rd1⟩ :=
    midnightTakeSellerPendingRuntime hstack hmem hw hle ha rd
  exact ⟨hbound, takeSellerPendingSource hf.contract hp hd hcanon hle, hf.sellerPending,
    aw1, k1, C1, ha1, rd1⟩

end Benchmarks.Midnight
