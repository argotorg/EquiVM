import Benchmarks.Midnight.TakeWrites
import Benchmarks.Midnight.TakeGates

/-! Entry gates preserve all trade inputs before the accounting writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeGatesFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee sellerFee bought sold consumed increase decrease buyerDebt sellerDebt saved : UInt256}
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
    (hcover : root.toNat ≤ 32 * aw.toNat)
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
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12234⟩
      ([positionSlot id buyer, sellerDebt, buyerDebt, positionSlot id seller,
        solcMappingSlot ⟨1⟩ id, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 44) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 44) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 44)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightMemoryPaid_headroom rd ha.accounting.paid hgas hcover with hoog | hroom
  · exact Or.inl hoog
  have hbuyerWord := addressWord_eq_ofNat_address hbuyerCanon
  have hsellerWord := addressWord_eq_ofNat_address hsellerCanon
  rcases midnightTakeGates (R := R) (by omega) (by omega) (by omega) (by omega) hheap
      hfree (hbuyer.trans hbuyerWord.symm) (hseller.trans hsellerWord.symm)
      hf hfBuyer hfSeller hfIncrease hfSellerDebt hs ho hoffer ha rd with
    ⟨hx, hr⟩ | ⟨frame1, evm1, σ1, mem1, out1, root1, aw1, k1, C1,
      source1, hf1, hget, hs1, hstorage, hp, hlo1, hhi1, halign1, hfree1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hr⟩))
  · have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem := hp.load off hl (by omega) (by omega)
    have hposition : healthPositionWord evm1 id buyer = healthPositionWord evm id buyer := by
      unfold healthPositionWord
      rw [hs1.env, hs.env]
      exact (accountStorageStateEq_storage_getD hstorage I.codeOwner _ ⟨0⟩).symm
    have hdebt1 : buyerDebt = low128 (healthPositionWord evm1 id buyer) := by
      rw [hposition]
      exact hbuyerDebt
    have hincrease1 : increase = takeBuyerCreditIncrease evm1 id buyer units := by
      unfold takeBuyerCreditIncrease
      rw [hposition]
      exact hcreditIncrease
    rcases midnightTakeWrites (frame := frame1) hstack hfork hgas hc hf1
        hbuyerCanon hsellerCanon hbuyerFee128 hsellerFee128 hconsumed128
        ((hget _ (by decide)).trans hfBuyerPos) ((hget _ (by decide)).trans hfSellerPos)
        ((hget _ (by decide)).trans hfSellerDebt) ((hget _ (by decide)).trans hfMarket)
        ((hget _ (by decide)).trans hfBuyer) ((hget _ (by decide)).trans hfSeller)
        ((hget _ (by decide)).trans hfBought) ((hget _ (by decide)).trans hfSold)
        ((hget _ (by decide)).trans hfConsumed) ((hget _ (by decide)).trans hfBuyerFee)
        ((hget _ (by decide)).trans hfSellerFee) ((hget _ (by decide)).trans hfIncrease)
        ((hget _ (by decide)).trans hfDecrease)
        (ho.preserve (hp.mono hheap)) (by omega) hdLower hratLower (by omega) (by omega)
        (hsize.trans hp.size) (hd.preserve hp hbelow) (by omega)
        (hrat.preserve hp hratBelow) (by omega) (by omega) hdebt1 hincrease1 ha1
        hfree1 ((hread _ (by decide) (by decide)).trans hzero) (halign1.trans halign)
        ((hread _ (by decide) (by decide)).trans hoffer)
        ((hread _ (by decide) (by decide)).trans htaker)
        ((hread _ (by decide) (by decide)).trans hid)
        ((hread _ (by decide) (by decide)).trans hseller)
        ((hread _ (by decide) (by decide)).trans hbought)
        ((hread _ (by decide) (by decide)).trans hsold)
        ((hread _ (by decide) (by decide)).trans hfee)
        ((hread _ (by decide) (by decide)).trans hreceiver)
        ((hread _ (by decide) (by decide)).trans hcallback)
        ((hread _ (by decide) (by decide)).trans hbuyer)
        ((hread _ (by decide) (by decide)).trans hbuyerFee)
        ((hread _ (by decide) (by decide)).trans hconsumed) hunits hs1 rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1 _ hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1 _ hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame2, evm2, source1 _ hx, hr⟩))

end Benchmarks.Midnight
