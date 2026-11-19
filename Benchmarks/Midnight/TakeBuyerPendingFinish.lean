import Benchmarks.Midnight.TakeCreditFinish

/-! The buyer pending-fee write and all remaining trade steps. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeBuyerPendingFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee sellerFee bought sold consumed increase decrease sellerDebt saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
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
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨20456⟩
      ([positionFieldWord evm id buyer 1, buyerFee, ⟨4216⟩, ⟨12386⟩,
        positionSlot id buyer, sellerDebt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask,
        positionSlot id seller, solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 48) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 48)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightTakeBuyerPendingWrite
      (R := [sellerDebt, ⟨12505⟩, ⟨2⟩, ⟨12517⟩, uint128Mask, positionSlot id seller,
        solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hfBuyerPos hfBuyerFee hbuyerCanon hbuyerFee128 hperm hs ha rd with
    ⟨hx, hr⟩ | ⟨σ1, k1, C1, source1, hs1, ha1, rd1⟩
  · exact Or.inr (Or.inl ⟨hx, hr⟩)
  · rcases midnightTakeCreditFinish hstack hfork hgas hc hf hbuyerCanon hsellerCanon
        hbuyerFee128 hsellerFee128 hconsumed128 hfBuyerPos hfSellerPos hfSellerDebt hfMarket
        hfBuyer hfSeller hfBought hfSold hfConsumed hfBuyerFee hfSellerFee hfIncrease hfDecrease
        ho hroot hdLower hratLower hheap hlo hsize hd hbelow hrat hratBelow hb hperm ha1
        hfree hzero halign hoffer htaker hid hseller hbought hsold hfee hreceiver hcallback
        hbuyer hbuyerFee hconsumed hunits hs1 rd1 with
      hoog | ⟨hx, hr⟩ | ⟨frame1, evm1, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1 _ hx, hr⟩)
    · exact Or.inr (Or.inr ⟨frame1, evm1, source1 _ hx, hr⟩)

end Benchmarks.Midnight
