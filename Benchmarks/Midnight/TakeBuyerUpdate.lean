import Benchmarks.Midnight.TakeBuyerUpdateValues

variable {fork : Ethereum.Fork}

/-! The conditional buyer update joins the source call to its runtime trace. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeBuyerUpdate {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr offerRoot root id buyer units taker saved sellerSlot
      buyerSlot : UInt256} {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 30 ≤ 1024) (hcanon : buyer.toNat < EVM.addressModulus)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat buyer.toNat)))
    (hp : frame.locals.get? "buyerPos" = some (.storageRef (positionRef id buyer) positionType))
    (hcredit : frame.locals.get? "__c9" = some (.bool (hasCreditValue evm id buyer)))
    (hs : SourceState s0 I evm.accountMap evm)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr offerRoot offer)
    (hrootlo : 96 ≤ root.toNat) (hroot : root.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = buyer)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0
      (takeBuyerUpdatePC (positionFieldWord evm id buyer 0)
        (low128 (healthPositionWord evm id buyer)) units)
      (sellerSlot :: saved :: buyerSlot :: R) mem aw rdata evm.accountMap k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 32) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 32) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (let frame' := takeBuyerUpdateFrame frame evm offer id buyer units
     let evm' := takeBuyerUpdateState evm offer id buyer units
     let mem' := takeBuyerUpdateMemory mem root evm offer id buyer units
     ExecStmt fork config frame evm takeBuyerUpdateStmt (.ok frame' evm') ∧
     TakeSourceFrame frame' offer id units taker receiver callback ratifierData data ∧
     SourceState s0 I evm'.accountMap evm' ∧ MemoryPrefix mem mem' root.toNat ∧
     memLoad (UInt256.ofNat 64) mem' = root ∧
     ∃ aw' k' C', MemoryFunding credit mem' aw' C' ∧
       RD fork midnightBytecode I g s0 ⟨11966⟩ (sellerSlot :: saved :: buyerSlot :: R)
         mem' aw' rdata evm'.accountMap k' C') := by
  have he := evalTakeBuyerUpdateCondition hcanon hp hf.units hcredit
  have hf' := hf.buyerUpdate (buyer := buyer) (evm := evm)
  by_cases hn : TakeBuyerUpdateNeeded evm id buyer units
  · have he' : evalExpr? config frame evm takeBuyerUpdateCondition = .ok (.bool true) := by
      simpa only [decide_eq_true hn] using he
    simp only [takeBuyerUpdatePC, if_pos hn] at rd
    have hm : memLoad (⟨832⟩ : UInt256) mem = marketPtr :=
      ho.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
    have rd1 := midnightBlocks.midnight_block_14492
      (by simp only [List.length_cons]; omega) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_14492_stack, hoffer, hm, hid, hbuyer] at rd1 ha1
    rcases midnightPositionUpdateCall (name := "__c10") (ret := UInt256.ofNat 14513)
        (R := sellerSlot :: saved :: buyerSlot :: R) (ptr := marketPtr) (id := id) (user := buyer)
        (m := offer.market)
        (by simp only [List.length_cons]; omega) hcanon hf.contract
        (evalTakePositionUpdateArgs hf.offerValue hf.idValue hb) hs ho.market
        hrootlo hroot hfree (by jump_dest) ha1 rd1 with
      ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨hx, hs2, hm2, hfree2, aw2, k2, C2, ha2, rd2⟩
    · refine Or.inl ⟨?_, hr⟩
      rw [takeBuyerUpdate_shape]
      exact ExecBlock.consRevert (ExecStmt.iteTrue he' (ExecBlock.consRevert hx))
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      rw [takeBuyerUpdate_shape]
      exact ExecBlock.consStatic (ExecStmt.iteTrue he' (ExecBlock.consStatic hx))
    · have rd3 := midnightBlocks.midnight_block_14513
        (by simp only [List.length_cons]; omega) (by jump_dest) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
      simp only [midnightBlocks.midnight_block_14513_stack] at rd3
      simp only [takeBuyerUpdateFrame, takeBuyerUpdateState, takeBuyerUpdateMemory, if_pos hn]
        at hf' ⊢
      exact Or.inr (Or.inr ⟨ExecStmt.iteTrue he' (ExecBlock.consNormal hx ExecBlock.nil), hf',
        hs2, hm2, hfree2, _, _, _, ha3, rd3⟩)
  · have he' : evalExpr? config frame evm takeBuyerUpdateCondition = .ok (.bool false) := by
      simpa only [decide_eq_false hn] using he
    simp only [takeBuyerUpdatePC, if_neg hn] at rd
    simp only [takeBuyerUpdateFrame, takeBuyerUpdateState, takeBuyerUpdateMemory, if_neg hn]
      at hf' ⊢
    exact Or.inr (Or.inr ⟨ExecStmt.iteFalse he' ExecBlock.nil, hf', hs,
      MemoryPrefix.refl mem root.toNat, hfree, aw, k, C, ha, rd⟩)

end Benchmarks.Midnight
