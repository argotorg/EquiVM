import Benchmarks.Midnight.TakeGate

/-! Both optional entry gates, preserving the trade locals, heap, and storage. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem takeGateFrame_get {frame frame' : Frame}
    (hf : frame' = frame ∨ frame' = takeGateAllowedFrame frame ⟨1⟩)
    (name : Ident) (hn : name ≠ "allowed") : frame'.locals.get? name = frame.locals.get? name := by
  rcases hf with rfl | rfl
  · rfl
  · exact store_get_ne _ _ (by simpa using hn.symm)

theorem TakeSourceFrame.gateChoice {frame frame' : Frame} {offer : OfferData}
    {id units taker : UInt256} {receiver callback : AccountAddress} {ratifierData data : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hchoice : frame' = frame ∨ frame' = takeGateAllowedFrame frame ⟨1⟩) :
    TakeSourceFrame frame' offer id units taker receiver callback ratifierData data := by
  rcases hchoice with rfl | rfl
  · exact hf
  · exact hf.enterGate

set_option maxRecDepth 10000

theorem midnightTakeGates {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {offer : OfferData} {mem rdata : ByteArray}
    {aw root marketPtr arrayPtr callbackPtr offerRoot id units taker buyerSlot debt buyerDebt
      sellerSlot marketSlot decrease ratifierPtr increase saved : UInt256}
    {buyer seller receiver callback : AccountAddress} {ratifierData data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (hroot : root.toNat + 68 < 2^64) (hlower : 608 ≤ root.toNat) (hm : 608 ≤ mem.size)
    (hextent : offerRoot.toNat ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = UInt256.ofNat buyer.val)
    (hseller : memLoad (UInt256.ofNat 448) mem = UInt256.ofNat seller.val)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (hb : frame.locals.get? "buyer" = some (.address buyer))
    (hsel : frame.locals.get? "seller" = some (.address seller))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerDebtIncrease" = some (.int debt.toNat))
    (hs : SourceState s0 I σ evm)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr offerRoot offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12234⟩
      ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase,
        saved] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (takeTransition.body.drop 44) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' rdata' : ByteArray)
      (root' aw' : UInt256) (k' C' : Nat),
      (∀ result, ExecBlock config frame' evm' (takeTransition.body.drop 46) result →
        ExecBlock config frame evm (takeTransition.body.drop 44) result) ∧
      TakeSourceFrame frame' offer id units taker receiver callback ratifierData data ∧
      (∀ name, name ≠ "allowed" → frame'.locals.get? name = frame.locals.get? name) ∧
      SourceState s0 I σ' evm' ∧ accountStorageStateEq evm.accountMap evm'.accountMap ∧
      MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ root'.toNat ∧ root'.toNat ≤ root.toNat + 64 ∧
      root'.toNat % 32 = root.toNat % 32 ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ MemoryFunding credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨12316⟩
        ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase,
          saved] ++ R) mem' aw' rdata' σ' k' C' := by
  rcases midnightTakeGate .credit hstack (by omega) hlower hm hfree hbuyer hf.offerValue
      hb hi hs ho hoffer ha rd with
    ⟨hx, hr⟩ | ⟨frame1, evm1, σ1, mem1, data1, root1, aw1, k1, C1,
      hx1, hframe1, hs1, hstorage1, hp1, hlo1, hhi1, halign1, hfree1, ha1, rd1⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [takeGates_shape]
    exact ExecBlock.consRevert hx
  · have hf1 := hf.gateChoice hframe1
    have hm1 : 608 ≤ mem1.size := hm.trans hp1.size
    have hsell1 : memLoad (UInt256.ofNat 448) mem1 = UInt256.ofNat seller.val := by
      rw [hp1.load (UInt256.ofNat 448) (by decide) (by change 480 ≤ root.toNat; omega)
        (by change 480 ≤ mem.size; omega), hseller]
    have hoffer1 : memLoad (UInt256.ofNat 384) mem1 = ⟨832⟩ := by
      rw [hp1.load (UInt256.ofNat 384) (by decide) (by change 416 ≤ root.toNat; omega)
        (by change 416 ≤ mem.size; omega), hoffer]
    have hsel1 := (takeGateFrame_get hframe1 "seller" (by decide)).trans hsel
    have hd1 := (takeGateFrame_get hframe1 "sellerDebtIncrease" (by decide)).trans hd
    rcases midnightTakeGate .debt hstack (by omega) (by omega) hm1 hfree1 hsell1
        hf1.offerValue hsel1 hd1 hs1 (ho.preserve (hp1.mono hextent)) hoffer1 ha1 rd1 with
      ⟨hx, hr⟩ | ⟨frame2, evm2, σ2, mem2, data2, root2, aw2, k2, C2,
        hx2, hframe2, hs2, hstorage2, hp2, hlo2, hhi2, halign2, hfree2, ha2, rd2⟩
    · refine Or.inl ⟨?_, hr⟩
      rw [takeGates_shape]
      exact ExecBlock.consNormal hx1 (ExecBlock.consRevert hx)
    · refine Or.inr ⟨frame2, evm2, σ2, mem2, data2, root2, aw2, k2, C2,
        ?_, hf1.gateChoice hframe2, ?_, hs2,
        accountStorageStateEq_trans hstorage1 hstorage2, hp1.trans (hp2.mono hlo1),
        by omega, by omega, halign2.trans halign1, hfree2, ha2, rd2⟩
      · intro result hx
        rw [takeGates_shape]
        exact ExecBlock.consNormal hx1 (ExecBlock.consNormal hx2 hx)
      · intro name hn
        exact (takeGateFrame_get hframe2 name hn).trans (takeGateFrame_get hframe1 name hn)

end Benchmarks.Midnight
