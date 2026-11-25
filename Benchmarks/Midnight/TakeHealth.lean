import Benchmarks.Midnight.TakeHealthSource
import Benchmarks.Midnight.HealthInternalBudget
import Benchmarks.Midnight.FundingBudget

variable {fork : Ethereum.Fork}

/-! The optional final health call, its requirement, and take's ABI return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeHealth {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root market arrayPtr heap id seller locked
      bought sold : UInt256} {offer : OfferData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hfork : fork ≥ .osaka)
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hfOffer : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hfId : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfSeller : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hfLocked : frame.locals.get? "locked" = some (wordToElem .bool locked))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hm : MarketStored mem market arrayPtr heap offer.market) (hheap : heap.toNat ≤ root.toNat)
    (hroot : root.toNat + 4096 < 2^64) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hmarket : memLoad (memLoad (UInt256.ofNat 384) mem) mem = market)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (ha : MemoryFunding credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨13359⟩ (locked :: R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 73) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 73)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode g s0 evm'.accountMap (wordArrayBytes [bought, sold]) := by
  have he := takeHealthCondition_eval (evm := evm) hfLocked
  rw [takeHealth_shape]
  by_cases hz : locked = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_13359_taken (by omega)
      (by rw [hz]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (ha.mono (by omega))
    have rd2 := midnightBlocks.midnight_block_13407 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_13407_stack, hmarket, hid, hseller] at rd2
    have hargs := takeHealthArgs_eval (evm := evm) hfOffer hfId hfSeller
    have hlookup : lookupCallable? frame.contract "isHealthy_body" =
        some healthFunction.toCallable := by rw [hc]; rfl
    have hcond : evalExpr? config frame evm takeHealthCondition = .ok (.bool true) := by
      simpa only [decide_eq_true hz] using he
    rcases midnightHealthInternal_budget frame.immutables hstack hfork hcanon hroot hheap
        hfree hm hs (by jump_dest) ha2.budget rd2 with
      ⟨hx, hr⟩ | ⟨evm1, σ1, childFrame, mem1, out1, root1, aw1, k1, C1, value,
        hx, hs1, hm1, hfree1, hheap1, hroot1, hlo1, hhi1, hmod1, hp1, ha1, rd3⟩
    · refine Or.inl ⟨ExecBlock.consRevert (ExecStmt.iteTrue hcond (ExecBlock.consRevert ?_)), hr⟩
      apply internalCallFunctionRevert hargs hlookup rfl
      simpa only [healthCallFrame, hc] using hx
    · have hcall : ExecStmt fork config frame evm takeHealthStmt
          (.ok (takeHealthFrame frame value) evm1) := by
        apply internalCallFunctionReturn (callee := healthFunction)
          (locals := healthArguments offer.market id seller) (value := some [.bool value])
          hargs hlookup rfl
        simpa only [healthCallFrame, hc] using hx
      have rd4 := midnightBlocks.midnight_block_13429 (by simp only [List.length_cons]; omega)
        (by jump_dest) rd3
      cases value with
      | false =>
        have rd5 := midnightBlocks.midnight_block_13366_taken (by omega)
          (by decide) (by jump_dest) rd4
        have hr := midnightBlocks.midnight_block_13392 (R := R) (by omega) rd5
        exact Or.inl ⟨ExecBlock.consRevert (ExecStmt.iteTrue hcond
          (ExecBlock.consNormal hcall (ExecBlock.consRevert
            (ExecStmt.requireFalse (takeHealthGuard frame evm1 false))))), hr⟩
      | true =>
        have rd5 := midnightBlocks.midnight_block_13366_fallthrough (by omega) (by decide) rd4
        have hr := midnightTakeReturn (R := R) (by omega) hroot1 (by omega)
          (hsize.trans hp1.size) hfree1
          ((hp1.load (UInt256.ofNat 256) (by decide) (by change 288 ≤ root.toNat; omega)
            (by change 288 ≤ mem.size; omega)).trans hbought)
          ((hp1.load (UInt256.ofNat 416) (by decide) (by change 448 ≤ root.toNat; omega)
            (by change 448 ≤ mem.size; omega)).trans hsold) rd5
        rw [hs1.accounts] at hr
        refine Or.inr ⟨takeHealthFrame frame true, evm1,
          ExecBlock.consNormal (ExecStmt.iteTrue hcond
            (ExecBlock.consNormal hcall (ExecBlock.consNormal
              (ExecStmt.requireTrue (takeHealthGuard frame evm1 true)) ExecBlock.nil)))
            (ExecBlock.consReturn (takeReturnSource ?_ ?_)), hr⟩
        · exact (store_get_ne _ _ (by decide)).trans hfBought
        · exact (store_get_ne _ _ (by decide)).trans hfSold
  · have rd1 := midnightBlocks.midnight_block_13359_fallthrough (by omega)
      (isZero_eq_zero_of_ne hz) rd
    have rd2 := midnightBlocks.midnight_block_13366_fallthrough (by omega)
      (isZero_eq_zero_of_ne hz) rd1
    have hr := midnightTakeReturn (R := R) (by omega) (by omega) hlo hsize hfree hbought hsold rd2
    rw [hs.accounts] at hr
    exact Or.inr ⟨frame, evm, ExecBlock.consNormal
      (ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using he) ExecBlock.nil)
      (ExecBlock.consReturn (takeReturnSource hfBought hfSold)), hr⟩

end Benchmarks.Midnight
