import Benchmarks.Midnight.TakeSellerFeeFinish
import Benchmarks.Midnight.TakeBuyerPending

/-! Both pending-fee calculations followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeFeesFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      time bought sold consumed increase decrease buyerDebt sellerDebt saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (hbuyerCanon : buyer.toNat < EVM.addressModulus)
    (hsellerCanon : seller.toNat < EVM.addressModulus)
    (hconsumed128 : consumed.toNat < 2^128)
    (hfTime : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
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
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12118⟩
      ([sellerDebt, ⟨12138⟩, ⟨12144⟩, takePendingScale, ⟨12150⟩,
        positionFieldWord evm id seller 0, positionSlot id buyer, time, buyerDebt,
        positionSlot id seller,
        solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 38) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 38) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 38)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  have hs' : SourceState s0 I evm.accountMap evm := by rw [← hs.accounts]; exact hs
  rw [hs.accounts] at rd
  rcases midnightTakeBuyerPending (R := saved :: R)
      (by simp only [List.length_cons]; omega) hf hfMarket hfTime hfIncrease hs' ha rd with
    ⟨hx, hr⟩ | ⟨hfee128, source1, hf1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hr⟩))
  · let frame1 := takeBuyerPendingFrame frame (marketContinuousFee (marketFeeWord evm id))
      time increase
    have hget (name : Ident) (hn : name ≠ "buyerPendingFeeIncrease") (hn' : name ≠ "__c15") :
        frame1.locals.get? name = frame.locals.get? name :=
      (store_get_ne _ _ (by simpa using hn.symm)).trans
        (store_get_ne _ _ (by simpa using hn'.symm))
    rcases midnightTakeSellerFeeFinish (frame := frame1) hstack hfork hgas hc hf1
        hbuyerCanon hsellerCanon hfee128 hconsumed128
        ((hget _ (by decide) (by decide)).trans hfBuyerPos)
        ((hget _ (by decide) (by decide)).trans hfSellerPos)
        ((hget _ (by decide) (by decide)).trans hfSellerDebt)
        ((hget _ (by decide) (by decide)).trans hfMarket)
        ((hget _ (by decide) (by decide)).trans hfBuyer)
        ((hget _ (by decide) (by decide)).trans hfSeller)
        ((hget _ (by decide) (by decide)).trans hfBought)
        ((hget _ (by decide) (by decide)).trans hfSold)
        ((hget _ (by decide) (by decide)).trans hfConsumed) (wordLocal_get ..)
        ((hget _ (by decide) (by decide)).trans hfIncrease)
        ((hget _ (by decide) (by decide)).trans hfDecrease)
        ho hused hdLower hratLower hheap hlo hsize hd hbelow hrat hratBelow hb
        hbuyerDebt hcreditIncrease ha1 hfree hzero halign hoffer htaker hid hseller hbought hsold
        hreceiver hcallback hbuyer hconsumed hpacked hdecrease hunits hs' rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
