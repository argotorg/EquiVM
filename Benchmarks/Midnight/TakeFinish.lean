import Benchmarks.Midnight.TakeAfterLock
import Benchmarks.Midnight.TakeEncodeOffer
import Benchmarks.Midnight.TakeEventSource
import Benchmarks.Midnight.TakeLock

variable {fork : Ethereum.Fork}

/-! Offer encoding, the trade event, and the lock followed by the completed take suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee sellerFee bought sold consumed increase decrease saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback receiver buyerCallback sellerCallback payer :
      AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
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
    (hfReceiver : frame.locals.get? "receiver" = some (.address receiver))
    (hfPayer : frame.locals.get? "payer" = some (.address payer))
    (hfBuyerCallback : frame.locals.get? "buyerCallback" = some (.address buyerCallback))
    (hfSellerCallback : frame.locals.get? "sellerCallback" = some (.address sellerCallback))
    (hle : sold.toNat ≤ bought.toNat)
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
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
    (hreceiver : memLoad (UInt256.ofNat 128) mem = UInt256.ofNat receiver.val)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hfee : memLoad (UInt256.ofNat 160) mem = sellerFee)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = buyer)
    (hbuyerFee : memLoad (UInt256.ofNat 224) mem = buyerFee)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12792⟩
      ([decrease, increase, ratifierPtr, UInt256.ofNat sellerCallback.val,
        UInt256.ofNat payer.val, UInt256.ofNat buyerCallback.val, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 64) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 64)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightTakeEncodeOffer (g := Sat256.ofUInt256 g)
      (by change R.length + 33 ≤ 1024; exact hstack)
      ho hc hheap hb hoffer hfree hgas ha rd with
    hoog | ⟨hroom, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl hoog
  · let root1 := root + UInt256.ofNat (offerBytesSize offer + 32)
    let mem1 := offerBytesMemory mem root callbackPtr offer
    have hn1 : root1.toNat = root.toNat + offerBytesSize offer + 32 := by
      dsimp [root1]
      rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]
      omega
    have hpad : paddedSize offer.callbackData.size < 2^64 := by
      have h1 := ho.extent
      have h2 := ho.bound
      omega
    have hcbBelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat :=
      ho.extent.trans hheap
    have hp1 : MemoryPrefix mem mem1 root.toNat :=
      offerBytesMemory_prefix offer ho.callback hpad hcbBelow hb
    have hread1 (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem := hp1.load off hl (by omega) (by omega)
    have hfree1 : memLoad (UInt256.ofNat 64) mem1 = root1 :=
      offerBytesMemory_free ..
    obtain ⟨eventMem, aw2, k2, C2, hp2, ha2, rd2⟩ := midnightTakeEventTrace
      (R := saved :: R) (by simp only [List.length_cons]; omega) hi128 hd128
      (by rw [hn1]; omega) (by rw [hn1]; omega)
      (by have hh := hp1.size; omega) (hrat.preserve hp1 hratBelow)
      (by rw [hn1]; omega) hfree1
      ((hread1 _ (by decide) (by decide)).trans hid)
      ((hread1 _ (by decide) (by decide)).trans hseller) hsellerCanon hperm ha1 rd1
    let frame1 := takeEncodedOfferFrame frame offer
    have hget1 (name : Ident) (hn : name ≠ "encodedOffer") :
        frame1.locals.get? name = frame.locals.get? name :=
      store_get_ne _ _ (by simpa using hn.symm)
    have hf1 : TakeSourceFrame frame1 offer id units taker initialReceiver initialCallback
        ratifierData data := hf.insert "encodedOffer" (.bytes (offerBytes offer)) (by decide)
    have hevent := takeEventArgs_eval (evm := evm) hf1 (store_get_self _ _ _)
      ((hget1 _ (by decide)).trans hfBought) ((hget1 _ (by decide)).trans hfSold)
      ((hget1 _ (by decide)).trans hfConsumed) ((hget1 _ (by decide)).trans hfBuyerFee)
      ((hget1 _ (by decide)).trans hfSellerFee) ((hget1 _ (by decide)).trans hfIncrease)
      ((hget1 _ (by decide)).trans hfDecrease) ((hget1 _ (by decide)).trans hfReceiver)
      ((hget1 _ (by decide)).trans hfPayer) hi128 hd128
    have hcbCanon : (UInt256.ofNat buyerCallback.val).toNat < EVM.addressModulus :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) buyerCallback.isLt
    obtain ⟨σ3, aw3, k3, C3, sourceLock, hs3, ha3, rd3⟩ := midnightTakeLock
      (frame := frame1) (R := saved :: R) (by simp only [List.length_cons]; omega)
      hf1.contract hsellerCanon hf1.idValue ((hget1 _ (by decide)).trans hfSeller)
      (by rw [hn1]; omega) (by rw [hn1]; change _ < 2^256; omega)
      hcbCanon hperm hs ha2 rd2
    let mem3 := dynamicLockMemory eventMem root1 id seller
    let root3 := root1 + UInt256.ofNat 128
    let frame3 := takeLockFrame frame1 evm id seller
    have hn3 : root3.toNat = root1.toNat + 128 :=
      uadd_word_ofNat_toNat _ _ (by rw [hn1]; change _ < 2^256; omega)
    have hp3 : MemoryPrefix mem mem3 root.toNat :=
      hp1.trans ((hp2.trans (dynamicLockMemory_prefix eventMem root1 id seller)).mono
        (by rw [hn1]; omega))
    have hread3 (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem3 = memLoad off mem := hp3.load off hl (by omega) (by omega)
    have hget3 (name : Ident) (hn : name ≠ "wasLocked") (hn' : name ≠ "encodedOffer") :
        frame3.locals.get? name = frame.locals.get? name :=
      (store_get_ne _ _ (by simpa using hn.symm)).trans (hget1 name hn')
    have hused3 : root3.toNat ≤ mem3.size := by
      rw [hn3]
      dsimp only [mem3]
      rw [dynamicLockMemory, writeWord_sparse_size, dynamicLockHashMemory_size]
      omega
    have halign3 : root3.toNat % 32 = 0 := by
      rw [hn3, hn1]
      unfold offerBytesSize offerEncodedSize offerCallbackOffset paddedSize
      omega
    have hrCanon : (UInt256.ofNat receiver.val).toNat < EVM.addressModulus :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) receiver.isLt
    have hreceiverRound : AccountAddress.ofNat (UInt256.ofNat receiver.val).toNat = receiver := by
      rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
      exact accountAddress_roundtrip receiver
    have sourcePrefix result
        (hx : ExecBlock fork config frame3 (lockExchangeState evm liquidationLockBase id seller true)
          (takeTransition.body.drop 67) result) :
        ExecBlock fork config frame evm (takeTransition.body.drop 64) result := by
      apply (takeEncodeOfferSource hc hf.offerValue).run
      rw [takeEvent_shape]
      exact ExecBlock.consNormal (ExecStmt.emit (by rw [hs.env]; exact hperm) hevent)
        (sourceLock result hx)
    rcases midnightTakeAfterLock (frame := frame3) (by omega) hfork hgas hf.contract
        hsellerCanon hrCanon hsellerFee128 hbuyerCanon hbuyerFee128
        ((hget3 _ (by decide) (by decide)).trans hfBuyer)
        ((hget3 _ (by decide) (by decide)).trans hfBuyerFee)
        ((hget3 _ (by decide) (by decide)).trans hfBuyerCallback)
        ((hget3 _ (by decide) (by decide)).trans hf.offerValue)
        ((hget3 _ (by decide) (by decide)).trans hf.idValue)
        ((hget3 _ (by decide) (by decide)).trans hfSeller)
        (by rw [hreceiverRound]; exact (hget3 _ (by decide) (by decide)).trans hfReceiver)
        (by exact store_get_self _ _ _)
        ((hget3 _ (by decide) (by decide)).trans hfBought)
        ((hget3 _ (by decide) (by decide)).trans hfSold)
        ((hget3 _ (by decide) (by decide)).trans hfSellerFee)
        ((hget3 _ (by decide) (by decide)).trans hf.units)
        ((hget3 _ (by decide) (by decide)).trans hf.data)
        ((hget3 _ (by decide) (by decide)).trans hfPayer) hle
        ((hget3 _ (by decide) (by decide)).trans hfSellerCallback)
        (ho.preserve (hp3.mono hheap)) (by rw [hn3, hn1]; omega)
        (by rw [hn3, hn1]; omega) (hsize.trans hp3.size)
        (hd.preserve hp3 hbelow) (by rw [hn3, hn1]; omega) hperm ha3
        (dynamicLockMemory_free ..) ((hread3 _ (by decide) (by decide)).trans hzero)
        hused3 halign3
        ((hread3 _ (by decide) (by decide)).trans hoffer)
        ((hread3 _ (by decide) (by decide)).trans htaker)
        ((hread3 _ (by decide) (by decide)).trans hid)
        ((hread3 _ (by decide) (by decide)).trans hseller)
        ((hread3 _ (by decide) (by decide)).trans hreceiver)
        ((hread3 _ (by decide) (by decide)).trans hbought)
        ((hread3 _ (by decide) (by decide)).trans hsold)
        ((hread3 _ (by decide) (by decide)).trans hfee)
        ((hread3 _ (by decide) (by decide)).trans hbuyer)
        ((hread3 _ (by decide) (by decide)).trans hbuyerFee) hunits hs3 rd3 with
      hoog | ⟨hx, hr⟩ | ⟨frame4, evm4, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨sourcePrefix _ hx, hr⟩)
    · exact Or.inr (Or.inr ⟨frame4, evm4, sourcePrefix _ hx, hr⟩)

end Benchmarks.Midnight
