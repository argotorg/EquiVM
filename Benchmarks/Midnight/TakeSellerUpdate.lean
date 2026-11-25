import Benchmarks.Midnight.TakeSellerUpdateSource
import Benchmarks.Midnight.TakeSellerCreditRead

variable {fork : Ethereum.Fork}

/-! The seller update reads credit from the state left by the buyer update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeSellerUpdate {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr offerRoot root id seller units taker : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 27 ≤ 1024) (hcanon : seller.toNat < EVM.addressModulus)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hseller : frame.locals.get? "seller" =
      some (.address (AccountAddress.ofNat seller.toNat)))
    (hs : SourceState s0 I evm.accountMap evm)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr offerRoot offer)
    (hrootlo : 96 ≤ root.toNat) (hroot : root.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hsellerMem : memLoad (UInt256.ofNat 448) mem = seller)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11966⟩ R mem aw rdata evm.accountMap k C) :
    (ExecBlock fork config frame evm (takeTransition.body.drop 33) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 33) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (let frame' := takeSellerUpdateFrame frame evm offer id seller
     let evm' := takeSellerUpdateState evm offer id seller
     let mem' := takeSellerUpdateMemory mem root evm offer id seller
     ExecBlock fork config frame evm takeSellerUpdateBody (.ok frame' evm') ∧
     TakeSourceFrame frame' offer id units taker receiver callback ratifierData data ∧
     SourceState s0 I evm'.accountMap evm' ∧ MemoryPrefix mem mem' root.toNat ∧
     memLoad (UInt256.ofNat 64) mem' = root ∧
     ∃ aw' k' C', MemoryFunding credit mem' aw' C' ∧
       RD fork midnightBytecode I g s0 ⟨12026⟩ R mem' aw' rdata evm'.accountMap k' C') := by
  have hmem : 1312 ≤ mem.size := by
    have hw := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hw
    omega
  have hload (off : UInt256) (hlo : 64 ≤ off.toNat) (hhi : off.toNat + 32 ≤ mem.size) :
      memLoad off (positionReadMemory mem id seller) = memLoad off mem :=
    positionReadMemory_load id seller off hlo hhi
  have hfree1 := (hload (UInt256.ofNat 64) (by decide) (by change 96 ≤ mem.size; omega)).trans
    hfree
  have hoffer1 := (hload (UInt256.ofNat 384) (by decide)
    (by change 416 ≤ mem.size; omega)).trans hoffer
  have hid1 := (hload (UInt256.ofNat 512) (by decide)
    (by change 544 ≤ mem.size; omega)).trans hid
  have hseller1 := (hload (UInt256.ofNat 448) (by decide)
    (by change 480 ≤ mem.size; omega)).trans hsellerMem
  have ho1 := ho.preserve (positionReadMemory_prefix mem id seller offerRoot.toNat)
  have hm1 : memLoad (⟨832⟩ : UInt256) (positionReadMemory mem id seller) = marketPtr :=
    ho1.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
  have hprefix := positionReadMemory_prefix mem id seller root.toNat
  have hxCredit := takeSellerCreditSource (fork := fork) (evm := evm) hf.contract hf.idValue hseller hcanon
  have hfCredit := hf.sellerCredit (evm := evm) (seller := seller)
  have hsellerCredit := (takeSellerCreditFrame_get frame evm id seller "seller"
    (by decide)).trans hseller
  have he := evalTakeSellerUpdateCondition frame evm id seller
  have hf' := hf.sellerUpdate (evm := evm) (seller := seller)
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeSellerCreditRead (by omega) (by omega)
    hid hsellerMem hcanon ha rd
  rw [takeHasCreditWord_source hs] at rd1
  by_cases hz : positionFieldWord evm id seller 0 = ⟨0⟩
  · simp only [if_pos hz] at rd1
    have he' : evalExpr? config (takeSellerCreditFrame frame evm id seller) evm
        (.var "__c11") = .ok (.bool false) := by
      simpa only [decide_eq_true hz, Bool.not_true] using he
    have rd2 := midnightBlocks.midnight_block_12021_fallthrough (by omega) rfl rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_12021_fallthrough_stack] at rd2
    simp only [takeSellerUpdateFrame, takeSellerUpdateState, takeSellerUpdateMemory, if_pos hz]
      at hf' ⊢
    exact Or.inr (Or.inr ⟨ExecBlock.consNormal hxCredit
      (ExecBlock.consNormal (ExecStmt.iteFalse he' ExecBlock.nil) ExecBlock.nil),
      hf', hs, hprefix, hfree1, _, _, _, ha2, rd2⟩)
  · simp only [if_neg hz] at rd1
    have he' : evalExpr? config (takeSellerCreditFrame frame evm id seller) evm
        (.var "__c11") = .ok (.bool true) := by
      simpa only [decide_eq_false hz, Bool.not_false] using he
    have rd2 := midnightBlocks.midnight_block_12021_taken (by omega) (by decide)
      (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_12021_taken_stack] at rd2
    have rd3 := midnightBlocks.midnight_block_14463 (by omega) (by jump_dest) rd2
    have ha3 := memoryFundingAt (credit := credit) rd3 (by memory_fund ha2)
    simp only [midnightBlocks.midnight_block_14463_stack, hoffer1, hm1, hid1, hseller1]
      at rd3 ha3
    rcases midnightPositionUpdateCall (name := "__c12") (ret := UInt256.ofNat 14484)
        (R := R) (ptr := marketPtr) (id := id) (user := seller) (m := offer.market)
        hstack hcanon hfCredit.contract
        (evalTakePositionUpdateArgs hfCredit.offerValue hfCredit.idValue hsellerCredit)
        hs ho1.market hrootlo hroot hfree1 (by jump_dest) ha3 rd3 with
      ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨hx, hs4, hm4, hfree4, aw4, k4, C4, ha4, rd4⟩
    · refine Or.inl ⟨?_, hr⟩
      rw [takeSellerUpdate_shape]
      exact ExecBlock.consNormal hxCredit
        (ExecBlock.consRevert (ExecStmt.iteTrue he' (ExecBlock.consRevert hx)))
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      rw [takeSellerUpdate_shape]
      exact ExecBlock.consNormal hxCredit
        (ExecBlock.consStatic (ExecStmt.iteTrue he' (ExecBlock.consStatic hx)))
    · have rd5 := midnightBlocks.midnight_block_14484 (by omega) (by jump_dest) rd4
      have ha5 := memoryFundingAt (credit := credit) rd5 (by memory_fund ha4)
      simp only [midnightBlocks.midnight_block_14484_stack] at rd5
      simp only [takeSellerUpdateFrame, takeSellerUpdateState, takeSellerUpdateMemory, if_neg hz]
        at hf' ⊢
      exact Or.inr (Or.inr ⟨ExecBlock.consNormal hxCredit
        (ExecBlock.consNormal (ExecStmt.iteTrue he' (ExecBlock.consNormal hx ExecBlock.nil))
          ExecBlock.nil), hf', hs4, hprefix.trans hm4, hfree4, _, _, _, ha5, rd5⟩)

end Benchmarks.Midnight
