import Benchmarks.Midnight.TakeTradeGuardsFinish
import Benchmarks.Midnight.TakeSellerPending

/-! The seller fee calculation followed by trade restrictions and all subsequent steps. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem takeSellerPendingFrame_get {frame : Frame} {credit pending decrease : UInt256}
    (name : Ident) (hn : name ∉ ["sellerPendingFeeDecrease", "decrease", "checkedDecrease"]) :
    (takeSellerPendingFrame frame credit pending decrease).locals.get? name =
      frame.locals.get? name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  unfold takeSellerPendingFrame
  split
  · exact store_get_ne _ _ (by simpa using (Ne.symm hn.1))
  · exact (store_get_ne _ _ (by simpa using (Ne.symm hn.1))).trans
      ((store_get_ne _ _ (by simpa using (Ne.symm hn.2.2))).trans
        ((store_get_ne _ _ (by simpa using (Ne.symm hn.2.1))).trans
          (store_get_ne _ _ (by simpa using (Ne.symm hn.1)))))

theorem midnightTakeSellerFeeFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee bought sold consumed increase decrease buyerDebt sellerDebt saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (hbuyerCanon : buyer.toNat < EVM.addressModulus)
    (hsellerCanon : seller.toNat < EVM.addressModulus)
    (hbuyerFee128 : buyerFee.toNat < 2^128)
    (hconsumed128 : consumed.toNat < 2^128)
    (hfBuyerPos : frame.locals.get? "buyerPos" =
      some (.storageRef (positionRef id buyer) positionType))
    (hfSellerPos : frame.locals.get? "sellerPos" =
      some (.storageRef (positionRef id seller) positionType))
    (hfSellerDebt : frame.locals.get? "sellerDebtIncrease" = some (.int sellerDebt.toNat))
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (hfBuyer : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat buyer.toNat)))
    (hfSeller : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hfConsumed : frame.locals.get? "newConsumed" = some (.int consumed.toNat))
    (hfBuyerFee : frame.locals.get? "buyerPendingFeeIncrease" = some (.int buyerFee.toNat))
    (hfIncrease : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hfDecrease : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hused : root.toNat ≤ mem.size)
    (hdLower : 256 ≤ takerPtr.toNat) (hratLower : 256 ≤ ratifierPtr.toNat)
    (hheap : offerRoot.toNat ≤ root.toNat) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hrat : MemoryByteString mem ratifierPtr ratifierData)
    (hratBelow : ratifierPtr.toNat + 32 + paddedSize ratifierData.size ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 256 < UInt256.size)
    (hbuyerDebt : buyerDebt = low128 (healthPositionWord evm id buyer))
    (hcreditIncrease : increase = takeBuyerCreditIncrease evm id buyer units)
    (ha : MemoryFunding credit mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (halign : root.toNat % 32 = 0)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = buyer)
    (hconsumed : memLoad (UInt256.ofNat 480) mem = consumed)
    (hpacked : memLoad (UInt256.ofNat 352) mem =
      EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id seller))
    (hdecrease : decrease.toNat ≤ (positionFieldWord evm id seller 0).toNat)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12150⟩
      ([buyerFee, positionFieldWord evm id seller 0, positionSlot id buyer,
        sellerDebt, buyerDebt, positionSlot id seller,
        solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 40) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 40) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 40)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  have hs' : SourceState s0 I evm.accountMap evm := by rw [← hs.accounts]; exact hs
  rw [hs.accounts] at rd
  obtain ⟨hfee128, source1, hf1, aw1, k1, C1, ha1, rd1⟩ := midnightTakeSellerPending
    (R := [ratifierPtr, increase, saved] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) hf hfSellerPos hfDecrease hsellerCanon hpacked hdecrease ha rd
  let sellerFee := takeSellerPendingValue (positionFieldWord evm id seller 0)
    (positionFieldWord evm id seller 1) decrease
  let frame1 := takeSellerPendingFrame frame (positionFieldWord evm id seller 0)
    (positionFieldWord evm id seller 1) decrease
  let mem1 := takeSellerPendingMemory mem buyerFee sellerFee
  have hget (name : Ident) (hn : name ∉ ["sellerPendingFeeDecrease", "decrease", "checkedDecrease"]) :
      frame1.locals.get? name = frame.locals.get? name := takeSellerPendingFrame_get name hn
  have hfSellerFee : frame1.locals.get? "sellerPendingFeeDecrease" = some (.int sellerFee.toNat) := by
    dsimp only [frame1, sellerFee, takeSellerPendingFrame, takeSellerPendingValue]
    split <;> exact wordLocal_get ..
  have hread (off : UInt256) (hh : off.toNat + 32 ≤ 832)
      (hbf : off.toNat + 32 ≤ 224 ∨ 256 ≤ off.toNat)
      (hsf : off.toNat + 32 ≤ 160 ∨ 192 ≤ off.toNat) :
      memLoad off mem1 = memLoad off mem := takeSellerPendingMemory_load _ _ _ (by omega) hbf hsf
  have hsize1 : mem.size ≤ mem1.size := by
    simp only [mem1, takeSellerPendingMemory, takeSellerPendingInitMemory, writeWord_sparse_size]
    omega
  have hdPad : paddedSize data.size < 2^64 := by omega
  have hrPad : paddedSize ratifierData.size < 2^64 := by omega
  have hd1 : MemoryByteString mem1 takerPtr data :=
    ((hd.writeWord_below (off := 224) buyerFee hdLower hdPad).writeWord_below
      (off := 160) ⟨0⟩ (by omega) hdPad).writeWord_below _ (by omega) hdPad
  have hr1 : MemoryByteString mem1 ratifierPtr ratifierData :=
    ((hrat.writeWord_below (off := 224) buyerFee hratLower hrPad).writeWord_below
      (off := 160) ⟨0⟩ (by omega) hrPad).writeWord_below _ (by omega) hrPad
  rcases midnightTakeTradeGuardsFinish (frame := frame1) hstack hfork hgas hc hf1
      hbuyerCanon hsellerCanon hbuyerFee128 hfee128 hconsumed128
      ((hget _ (by decide)).trans hfBuyerPos) ((hget _ (by decide)).trans hfSellerPos)
      ((hget _ (by decide)).trans hfSellerDebt) ((hget _ (by decide)).trans hfMarket)
      ((hget _ (by decide)).trans hfBuyer) ((hget _ (by decide)).trans hfSeller)
      ((hget _ (by decide)).trans hfBought) ((hget _ (by decide)).trans hfSold)
      ((hget _ (by decide)).trans hfConsumed) ((hget _ (by decide)).trans hfBuyerFee)
      hfSellerFee ((hget _ (by decide)).trans hfIncrease) ((hget _ (by decide)).trans hfDecrease)
      (takeSellerPendingMemory_offer ho) (hused.trans hsize1) (by omega) (by omega)
      hheap hlo (hsize.trans hsize1) hd1 hbelow hr1 hratBelow hb hbuyerDebt hcreditIncrease ha1
      ((hread _ (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hfree)
      ((hread _ (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hzero) halign
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hoffer)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans htaker)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hid)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hseller)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hbought)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hsold)
      (takeSellerPendingMemory_seller ..)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hreceiver)
      ((hread _ (by decide) (Or.inl (by decide)) (Or.inr (by decide))).trans hcallback)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hbuyer)
      (takeSellerPendingMemory_buyer ..)
      ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hconsumed)
      hunits hs' rd1 with
    hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
