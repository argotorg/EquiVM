import Benchmarks.Midnight.TakeCreditChangesRuntime

/-! Source/runtime correspondence for the three trade deltas. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightTakeCreditChanges {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw id buyer seller marketSlot ratifierPtr time units taker : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hse : frame.locals.get? "sellerPos" = some (.storageRef (positionRef id seller) positionType))
    (hbc : buyer.toNat < EVM.addressModulus) (hsc : seller.toNat < EVM.addressModulus)
    (hs : SourceState s0 I evm.accountMap evm) (hu : calldataWord I.calldata 68 = units)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12026⟩
      (positionSlot id seller :: marketSlot :: positionSlot id buyer :: ratifierPtr :: time :: R)
      mem aw rdata evm.accountMap k C) :
    let frame' := takeCreditChangesFrame frame evm id buyer seller units
    let mem' := takeCreditChangesMemory mem
      (solcSlotWordAt (positionSlot id seller) evm.accountMap I)
    ABlock config evm frame (takeTransition.body.drop 35) frame' (takeTransition.body.drop 38) ∧
    TakeSourceFrame frame' offer id units taker receiver callback ratifierData data ∧
    ∃ aw' k' C', MemoryFunding credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨12118⟩
        ([takeSellerDebtIncrease evm id seller units, UInt256.ofNat 12138, UInt256.ofNat 12144,
          UInt256.ofNat 1000000000000000000, UInt256.ofNat 12150,
          positionFieldWord evm id seller 0, positionSlot id buyer, time,
          low128 (healthPositionWord evm id buyer), positionSlot id seller, marketSlot,
          takeSellerCreditDecrease evm id seller units, ratifierPtr,
          takeBuyerCreditIncrease evm id buyer units] ++ R)
        mem' aw' rdata evm.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeCreditChangesRuntime hstack hu ha rd
  rw [← positionCreditSourceWord hs, ← positionDebtSourceWord hs] at rd1
  exact ⟨takeCreditChangesSource hf hb hse hbc hsc, hf.creditChanges, aw1, k1, C1, ha1, rd1⟩

end Benchmarks.Midnight
