import Benchmarks.Midnight.TakeMaturityGuard
import Benchmarks.Midnight.TakeReduceRead
import Reasoning.ExternalCall

/-! Both trade restrictions agree between source and runtime, including reverts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeTradeGuards {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr root id units taker buyerSlot debt buyerDebt sellerSlot
      marketSlot decrease ratifierPtr increase : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat))
    (hs : SourceState s0 I evm.accountMap evm)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12187⟩
      ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
      mem aw rdata evm.accountMap k C) :
    (ExecBlock config frame evm (takeTransition.body.drop 42) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    (TakeMaturityAllowed I offer debt ∧ TakeReduceAllowed offer increase debt ∧
      ABlock config evm frame (takeTransition.body.drop 42) frame (takeTransition.body.drop 44) ∧
      ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
        RD midnightBytecode I g s0 ⟨12234⟩
          ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
          mem aw' rdata evm.accountMap k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  rcases midnightTakeMaturityGuard (by simp only [List.length_cons]; omega) ho hoffer ha rd with
    ⟨hbad, hr⟩ | ⟨hm, aw1, k1, C1, ha1, rd1⟩
  · refine Or.inl ⟨takeTradeGuardsSourceRevert hf.offerValue hi hd ?_, hr⟩
    simpa only [hs.env] using (fun h ↦ hbad h.1 :
      ¬ (TakeMaturityAllowed I offer debt ∧ TakeReduceAllowed offer increase debt))
  · obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakeReduceRead hstack ho hoffer ha1 rd1
    rw [takeReduceGuardWord_eq] at rd2
    simp only [List.cons_append, List.nil_append] at rd2
    by_cases hreduce : TakeReduceAllowed offer increase debt
    · rw [if_pos hreduce] at rd2
      have rd3 := midnightBlocks.midnight_block_12228_fallthrough
        (by simp only [List.length_cons]; omega) (by decide) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
      exact Or.inr ⟨hm, hreduce, takeTradeGuardsSource hf.offerValue hi hd
        (by simpa only [hs.env] using hm) hreduce, _, _, _, ha3, rd3⟩
    · rw [if_neg hreduce] at rd2
      have rd3 := midnightBlocks.midnight_block_12228_taken
        (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd2
      simp only [midnightBlocks.midnight_block_12228_taken_stack] at rd3
      exact Or.inl ⟨takeTradeGuardsSourceRevert hf.offerValue hi hd (fun h ↦ hreduce h.2),
        midnightBlocks.midnight_block_14387 (by simp only [List.length_cons]; omega) rd3⟩

end Benchmarks.Midnight
