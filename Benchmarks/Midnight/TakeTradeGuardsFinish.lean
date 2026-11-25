import Benchmarks.Midnight.TakeGatesFinish
import Benchmarks.Midnight.TakeTradeGuards

variable {fork : Ethereum.Fork}

/-! Trade restrictions, both entry gates, and the entire accounting/payment suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeTradeGuardsFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee sellerFee bought sold consumed increase decrease buyerDebt sellerDebt saved : UInt256}
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
    (hused : root.toNat ≤ mem.size)
    (hdLower : 160 ≤ takerPtr.toNat) (hratLower : 160 ≤ ratifierPtr.toNat)
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
    (hfee : memLoad (UInt256.ofNat 160) mem = sellerFee)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = buyer)
    (hbuyerFee : memLoad (UInt256.ofNat 224) mem = buyerFee)
    (hconsumed : memLoad (UInt256.ofNat 480) mem = consumed)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12187⟩
      ([positionSlot id buyer, sellerDebt, buyerDebt, positionSlot id seller,
        solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 42) .staticViolation ∧
      RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 42) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 42)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  have hs' : SourceState s0 I evm.accountMap evm := by
    rw [← hs.accounts]
    exact hs
  rw [hs.accounts] at rd
  rcases midnightTakeTradeGuards (R := saved :: R) (by simp only [List.length_cons]; omega)
      hf hfIncrease hfSellerDebt hs' ho hoffer ha rd with
    ⟨hx, hr⟩ | ⟨_, _, source1, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hr⟩))
  · rcases midnightTakeGatesFinish hstack hfork hgas hc hf hbuyerCanon hsellerCanon
        hbuyerFee128 hsellerFee128 hconsumed128 hfBuyerPos hfSellerPos hfSellerDebt hfMarket
        hfBuyer hfSeller hfBought hfSold hfConsumed hfBuyerFee hfSellerFee hfIncrease hfDecrease
        ho (hused.trans ha1.covered) hdLower hratLower hheap hlo hsize hd hbelow hrat hratBelow hb
        hbuyerDebt hcreditIncrease ha1 hfree hzero halign hoffer htaker hid hseller hbought hsold
        hfee hreceiver hcallback hbuyer hbuyerFee hconsumed hunits hs' rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame1, evm1, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame1, evm1, source1.run hx, hr⟩))

end Benchmarks.Midnight
