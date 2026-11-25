import Benchmarks.Midnight.TakeSellerFinish
import Benchmarks.Midnight.TakeSellerPendingWrite

variable {fork : Ethereum.Fork}

/-! The buyer credit and seller pending-fee writes followed by the remaining trade writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeCreditFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee sellerFee bought sold consumed increase decrease sellerDebt saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (hbuyerCanon : buyer.toNat < EVM.addressModulus)
    (hsellerCanon : seller.toNat < EVM.addressModulus)
    (hbuyerFee128 : buyerFee.toNat < 2^128) (hsellerFee128 : sellerFee.toNat < 2^128)
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
    (hfSellerFee : frame.locals.get? "sellerPendingFeeDecrease" = some (.int sellerFee.toNat))
    (hfIncrease : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hfDecrease : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hroot : root.toNat < 2^64)
    (hdLower : 160 ≤ takerPtr.toNat) (hratLower : 160 ≤ ratifierPtr.toNat)
    (hheap : offerRoot.toNat ≤ root.toNat) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hrat : MemoryByteString mem ratifierPtr ratifierData)
    (hratBelow : ratifierPtr.toNat + 32 + paddedSize ratifierData.size ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 128 < UInt256.size)
    (hperm : I.perm = true) (ha : MemoryFunding credit mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (halign : root.toNat % 32 = 0)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hfee : memLoad (UInt256.ofNat 160) mem = sellerFee)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = buyer)
    (hbuyerFee : memLoad (UInt256.ofNat 224) mem = buyerFee)
    (hconsumed : memLoad (UInt256.ofNat 480) mem = consumed)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12386⟩
      ([positionSlot id buyer, sellerDebt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask,
        positionSlot id seller, solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 49) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 49)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightTakeBuyerCredit (R := saved :: R)
      (by simp only [List.length_cons]; omega) hf.contract hfBuyerPos hfIncrease
      hbuyerCanon hperm hs ha rd with
    ⟨hx, hr⟩ | ⟨σ1, k1, C1, hi128, source1, hs1, ha1, rd1⟩
  · exact Or.inr (Or.inl ⟨hx, hr⟩)
  · let frame1 := takeBuyerCreditWriteFrame frame increase
    have hf1 : TakeSourceFrame frame1 offer id units taker initialReceiver initialCallback
        ratifierData data := hf.insert "__c22" (.int increase.toNat) (by decide)
    have hget (name : Ident) (hn : name ≠ "__c22") :
        frame1.locals.get? name = frame.locals.get? name :=
      store_get_ne _ _ (by simpa using hn.symm)
    rw [hfee] at rd1
    rcases midnightTakeSellerPendingWrite (frame := frame1)
        (R := [solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        ((hget _ (by decide)).trans hfSellerPos)
        ((hget _ (by decide)).trans hfSellerFee) hsellerCanon hsellerFee128 hperm hs1 ha1 rd1 with
      ⟨hx, hr⟩ | ⟨σ2, k2, C2, source2, hs2, ha2, rd2⟩
    · exact Or.inr (Or.inl ⟨source1 _ hx, hr⟩)
    · rcases midnightTakeSellerFinish (frame := frame1) hstack hfork hgas hc hf1
          hbuyerCanon hsellerCanon hbuyerFee128 hsellerFee128 hconsumed128 hi128
          ((hget _ (by decide)).trans hfSellerPos)
          ((hget _ (by decide)).trans hfSellerDebt)
          ((hget _ (by decide)).trans hfMarket)
          ((hget _ (by decide)).trans hfBuyer) ((hget _ (by decide)).trans hfSeller)
          ((hget _ (by decide)).trans hfBought) ((hget _ (by decide)).trans hfSold)
          ((hget _ (by decide)).trans hfConsumed) ((hget _ (by decide)).trans hfBuyerFee)
          ((hget _ (by decide)).trans hfSellerFee) ((hget _ (by decide)).trans hfIncrease)
          ((hget _ (by decide)).trans hfDecrease)
          ho hroot hdLower hratLower hheap hlo hsize hd hbelow hrat hratBelow hb hperm ha2
          hfree hzero halign hoffer htaker hid hseller hbought hsold hfee hreceiver hcallback
          hbuyer hbuyerFee hconsumed hunits hs2 rd2 with
        hoog | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨source1 _ (source2 _ hx), hr⟩)
      · exact Or.inr (Or.inr ⟨frame2, evm2, source1 _ (source2 _ hx), hr⟩)

end Benchmarks.Midnight
