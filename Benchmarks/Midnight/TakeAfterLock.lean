import Benchmarks.Midnight.TakePayments
import Benchmarks.Midnight.TakeBuyCallback

variable {fork : Ethereum.Fork}

/-! The buyer callback followed by both payments and the remaining take suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem takeAfterLock_shape : takeTransition.body.drop 67 =
    takeTransition.body[67]! :: takeTransition.body.drop 68 := rfl

theorem midnightTakeAfterLock {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data : ByteArray} {aw root market arrayPtr callbackPtr offerRoot
      takerPtr id units seller receiver fee buyer buyerFee wasLocked saved bought sold : UInt256}
    {offer : OfferData} {callback buyerCallback payer : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 30 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hfee128 : fee.toNat < 2^128)
    (hbuyerCanon : buyer.toNat < EVM.addressModulus) (hbuyerFee128 : buyerFee.toNat < 2^128)
    (hfBuyer : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat buyer.toNat)))
    (hfBuyerFee : frame.locals.get? "buyerPendingFeeIncrease" = some (.int buyerFee.toNat))
    (hfBuyerCallback : frame.locals.get? "buyerCallback" = some (.address buyerCallback))
    (hfOffer : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hfId : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfSeller : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hfReceiver : frame.locals.get? "receiver" =
      some (.address (AccountAddress.ofNat receiver.toNat)))
    (hfWasLocked : frame.locals.get? "wasLocked" = some (wordToElem .bool wasLocked))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hfFee : frame.locals.get? "sellerPendingFeeDecrease" = some (.int fee.toNat))
    (hfUnits : frame.locals.get? "units" = some (.int units.toNat))
    (hfData : frame.locals.get? "takerCallbackData" = some (.bytes data))
    (hfPayer : frame.locals.get? "payer" = some (.address payer))
    (hle : sold.toNat ≤ bought.toNat)
    (hfCallback : frame.locals.get? "sellerCallback" = some (.address callback))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hheap : offerRoot.toNat ≤ root.toNat) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hperm : I.perm = true) (ha : MemoryFunding credit mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hused : root.toNat ≤ mem.size) (halign : root.toNat % 32 = 0)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hreceiver : memLoad (UInt256.ofNat 128) mem = receiver)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hfee : memLoad (UInt256.ofNat 160) mem = fee)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = buyer)
    (hbuyerFee : memLoad (UInt256.ofNat 224) mem = buyerFee)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 (if UInt256.ofNat buyerCallback.val = ⟨0⟩ then ⟨13252⟩ else ⟨13774⟩)
      ([UInt256.ofNat buyerCallback.val, UInt256.ofNat callback.val, UInt256.ofNat payer.val, wasLocked, saved] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 67) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 67)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  rcases midnightTakeBuyCallback hstack ho hheap hused (by omega) hlo (by omega)
      hd hbelow hoffer htaker hfree hid hbought hunits hbuyerFee hbuyer hbuyerFee128 hbuyerCanon
      hfOffer hfData hfId hfBought hfUnits hfBuyerFee hfBuyer hfBuyerCallback ha hs rd with
    hoog | ⟨hx, hr⟩ | ⟨frame1, evm1, σ1, mem1, out1, root1, aw1, ignored1, k1, C1,
      hx1, hc1, hf1, hs1, hp1, hr1, hused1, hfree1, ha1, rd1⟩
  · exact Or.inl hoog
  · refine Or.inr (Or.inl ⟨?_, hr⟩)
    rw [takeAfterLock_shape]
    exact ExecBlock.consRevert hx
  · rcases midnightMemoryPaid_small rd1 ha1.accounting.paid hgas with hoog | haw1
    · exact Or.inl hoog
    have hn32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hlo1 : root.toNat ≤ root1.toNat := by rcases hr1 with rfl | rfl <;> omega
    have hhi1 : root1.toNat ≤ root.toNat + 32 := by rcases hr1 with rfl | rfl <;> omega
    have hmod1 : root1.toNat % 32 = 0 := by rcases hr1 with rfl | rfl <;> omega
    have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem := hp1.load off hl (by omega) (by omega)
    have hcredit1 : transferHeapCredit root1 ≤ credit := by
      rw [transferHeapCredit_small (by
        have hc := hused1.trans ha1.covered
        omega)]
      exact Nat.zero_le _
    have hh1 : TransferHeap mem1 aw1 root1 C1 :=
      ⟨by have hh := hp1.size; omega, by omega, hfree1,
        (hread _ (by decide) (by decide)).trans hzero,
        hused1.trans ha1.covered, hmod1, ha1.weaken hcredit1⟩
    rcases midnightTakePayments (frame := frame1) (by omega) hfork hgas (hc1.trans hc)
        hcanon hrcanon hfee128
        ((hf1 _ (by decide) (by decide)).trans hfOffer)
        ((hf1 _ (by decide) (by decide)).trans hfId)
        ((hf1 _ (by decide) (by decide)).trans hfSeller)
        ((hf1 _ (by decide) (by decide)).trans hfReceiver)
        ((hf1 _ (by decide) (by decide)).trans hfWasLocked)
        ((hf1 _ (by decide) (by decide)).trans hfBought)
        ((hf1 _ (by decide) (by decide)).trans hfSold)
        ((hf1 _ (by decide) (by decide)).trans hfFee)
        ((hf1 _ (by decide) (by decide)).trans hfUnits)
        ((hf1 _ (by decide) (by decide)).trans hfData)
        ((hf1 _ (by decide) (by decide)).trans hfPayer) hle
        ((hf1 _ (by decide) (by decide)).trans hfCallback)
        (ho.preserve (hp1.mono hheap)) (by omega) (by omega) (hsize.trans hp1.size)
        (hd.preserve hp1 hbelow) (by omega) hperm hh1
        ((hread _ (by decide) (by decide)).trans hoffer)
        ((hread _ (by decide) (by decide)).trans htaker)
        ((hread _ (by decide) (by decide)).trans hid)
        ((hread _ (by decide) (by decide)).trans hseller)
        ((hread _ (by decide) (by decide)).trans hreceiver)
        ((hread _ (by decide) (by decide)).trans hbought)
        ((hread _ (by decide) (by decide)).trans hsold)
        ((hread _ (by decide) (by decide)).trans hfee) hunits hs1 rd1 with
      hoog | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      rw [takeAfterLock_shape]
      exact ExecBlock.consNormal hx1 hx
    · refine Or.inr (Or.inr ⟨frame2, evm2, ?_, hr⟩)
      rw [takeAfterLock_shape]
      exact ExecBlock.consNormal hx1 hx

end Benchmarks.Midnight
