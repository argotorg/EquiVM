import Benchmarks.Midnight.TakeFinish
import Benchmarks.Midnight.TakeRecipients

/-! Recipient selection followed by offer encoding and the remaining take steps. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeAfterAccounting {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee sellerFee bought sold consumed increase decrease saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (hbuyerCanon : buyer.toNat < EVM.addressModulus)
    (hsellerCanon : seller.toNat < EVM.addressModulus)
    (hbuyerFee128 : buyerFee.toNat < 2^128) (hsellerFee128 : sellerFee.toNat < 2^128)
    (hi128 : increase.toNat < 2^128) (hd128 : decrease.toNat < 2^128)
    (hfBuyer : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat buyer.toNat)))
    (hfSeller : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hfConsumed : frame.locals.get? "newConsumed" = some (.int consumed.toNat))
    (hfBuyerFee : frame.locals.get? "buyerPendingFeeIncrease" = some (.int buyerFee.toNat))
    (hfSellerFee : frame.locals.get? "sellerPendingFeeDecrease" = some (.int sellerFee.toNat))
    (hfIncrease : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hfDecrease : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hle : sold.toNat ≤ bought.toNat)
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
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12719⟩
      ([offer.buy, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 60) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 60)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  have hbuyerWord := addressWord_eq_ofNat_address hbuyerCanon
  obtain ⟨aw1, k1, C1, hx1, ha1, rd1⟩ := midnightTakeRecipients
    (R := saved :: R) (by simp only [List.length_cons]; omega) hc hf hfBuyer ho hoffer
    hcallback (hbuyer.trans hbuyerWord.symm) hreceiver hs ha rd
  let frame1 := takeRecipientsFrame frame offer initialCallback
    (AccountAddress.ofNat buyer.toNat) I.source initialReceiver
  let mem1 := takeReceiverMemory mem offer initialReceiver
  have hget (name : Ident) (hn : name ∉ ["buyerCallback", "sellerCallback", "payer", "receiver"]) :
      frame1.locals.get? name = frame.locals.get? name := takeRecipientsFrame_get name hn
  have hread (off : UInt256) (hh : off.toNat + 32 ≤ 832)
      (hne : off.toNat + 32 ≤ 128 ∨ 160 ≤ off.toNat) :
      memLoad off mem1 = memLoad off mem :=
    takeReceiverMemory_load offer initialReceiver off (by omega) hne
  have hdPad : paddedSize data.size < 2^64 := by omega
  have hrPad : paddedSize ratifierData.size < 2^64 := by omega
  have hd1 : MemoryByteString mem1 takerPtr data :=
    (hd.writeWord_below (off := 128) ⟨0⟩ hdLower hdPad).writeWord_below _ hdLower hdPad
  have hr1 : MemoryByteString mem1 ratifierPtr ratifierData :=
    (hrat.writeWord_below (off := 128) ⟨0⟩ hratLower hrPad).writeWord_below _ hratLower hrPad
  have hfReceiver1 : frame1.locals.get? "receiver" =
      some (.address (takeReceiver offer initialReceiver)) := store_get_self _ _ _
  have hfPayer1 : frame1.locals.get? "payer" =
      some (.address (takePayer offer initialCallback (AccountAddress.ofNat buyer.toNat) I.source)) :=
    (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
  have hfBuyerCallback1 : frame1.locals.get? "buyerCallback" =
      some (.address (takeBuyerCallback offer initialCallback)) :=
    (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
  have hfSellerCallback1 : frame1.locals.get? "sellerCallback" =
      some (.address (takeSellerCallback offer initialCallback)) :=
    (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
      (store_get_self _ _ _))
  rcases midnightTakeFinish (frame := frame1) hstack hfork hgas hc hf.recipients
      hbuyerCanon hsellerCanon hbuyerFee128 hsellerFee128 hi128 hd128
      ((hget _ (by decide)).trans hfBuyer) ((hget _ (by decide)).trans hfSeller)
      ((hget _ (by decide)).trans hfBought) ((hget _ (by decide)).trans hfSold)
      ((hget _ (by decide)).trans hfConsumed) ((hget _ (by decide)).trans hfBuyerFee)
      ((hget _ (by decide)).trans hfSellerFee) ((hget _ (by decide)).trans hfIncrease)
      ((hget _ (by decide)).trans hfDecrease)
      hfReceiver1 hfPayer1 hfBuyerCallback1 hfSellerCallback1 hle
      (takeReceiverMemory_offer initialReceiver ho) hheap hlo
      (by rw [takeReceiverMemory_size mem offer initialReceiver (by omega)]; exact hsize)
      hd1 hbelow hr1 hratBelow hb hperm ha1
      ((hread _ (by decide) (Or.inl (by decide))).trans hfree)
      ((hread _ (by decide) (Or.inl (by decide))).trans hzero) halign
      ((hread _ (by decide) (Or.inr (by decide))).trans hoffer)
      ((hread _ (by decide) (Or.inr (by decide))).trans htaker)
      ((hread _ (by decide) (Or.inr (by decide))).trans hid)
      ((hread _ (by decide) (Or.inr (by decide))).trans hseller)
      (takeReceiverMemory_receiver ..)
      ((hread _ (by decide) (Or.inr (by decide))).trans hbought)
      ((hread _ (by decide) (Or.inr (by decide))).trans hsold)
      ((hread _ (by decide) (Or.inr (by decide))).trans hfee)
      ((hread _ (by decide) (Or.inr (by decide))).trans hbuyer)
      ((hread _ (by decide) (Or.inr (by decide))).trans hbuyerFee) hunits hs rd1 with
    hoog | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨hx1.run hx, hr⟩)
  · exact Or.inr (Or.inr ⟨frame2, evm2, hx1.run hx, hr⟩)

end Benchmarks.Midnight
