import Benchmarks.Midnight.TakeCleanup
import Benchmarks.Midnight.TakeSellCallback

variable {fork : Ethereum.Fork}

/-! The complete suffix after the two token transfers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem takeAfterTransfers_shape : takeTransition.body.drop 70 =
    takeTransition.body[70]! :: takeTransition.body.drop 71 := rfl

theorem midnightTakeAfterTransfers {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data : ByteArray} {aw root market arrayPtr callbackPtr offerRoot
      takerPtr id units seller receiver fee wasLocked saved bought sold : UInt256}
    {offer : OfferData} {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 28 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hfee128 : fee.toNat < 2^128)
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
    (hfCallback : frame.locals.get? "sellerCallback" = some (.address callback))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hheap : offerRoot.toNat ≤ root.toNat) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hperm : I.perm = true) (hh : TransferHeap mem aw root C)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hreceiver : memLoad (UInt256.ofNat 128) mem = receiver)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hfee : memLoad (UInt256.ofNat 160) mem = fee)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨13329⟩
      ([UInt256.ofNat callback.val, solcAddrMask, wasLocked, saved] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 70) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 70)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap (wordArrayBytes [bought, sold]) := by
  rcases midnightMemoryPaid_headroom rd hh.funding.accounting.paid hgas hh.covered with
    hoog | hroom
  · exact Or.inl hoog
  rcases midnightTakeSellCallback hstack ho hheap (by omega) hlo (by omega)
      hd hbelow hoffer htaker hh.free hid hsold hunits hfee hseller hreceiver hrcanon hfee128
      hcanon hfOffer hfData hfId hfSold hfUnits hfFee hfSeller hfReceiver hfCallback
      hh.funding hs rd with
    hoog | ⟨hx, hr⟩ | ⟨frame1, evm1, σ1, mem1, out1, root1, aw1, ignored, k1, C1,
      hx1, hc1, hf1, hs1, hp1, hr1, hfree1, ha1, rd1⟩
  · exact Or.inl hoog
  · refine Or.inr (Or.inl ⟨?_, hr⟩)
    rw [takeAfterTransfers_shape]
    exact ExecBlock.consRevert hx
  · have hn32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hlo1 : root.toNat ≤ root1.toNat := by rcases hr1 with rfl | rfl <;> omega
    have hhi1 : root1.toNat ≤ root.toNat + 32 := by rcases hr1 with rfl | rfl <;> omega
    have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem := hp1.load off hl (by omega) (by omega)
    rcases midnightTakeCleanup (R := saved :: R) (by simp only [List.length_cons]; omega)
        hfork (hc1.trans hc) hcanon
        ((hf1 _ (by decide) (by decide)).trans hfOffer)
        ((hf1 _ (by decide) (by decide)).trans hfId)
        ((hf1 _ (by decide) (by decide)).trans hfSeller)
        ((hf1 _ (by decide) (by decide)).trans hfWasLocked)
        ((hf1 _ (by decide) (by decide)).trans hfBought)
        ((hf1 _ (by decide) (by decide)).trans hfSold)
        (ho.preserve (hp1.mono hheap)) (by omega) (by omega) (by omega)
        (hsize.trans hp1.size) hperm hfree1
        ((hread _ (by decide) (by decide)).trans hoffer)
        ((hread _ (by decide) (by decide)).trans hid)
        ((hread _ (by decide) (by decide)).trans hseller)
        ((hread _ (by decide) (by decide)).trans hbought)
        ((hread _ (by decide) (by decide)).trans hsold) ha1 hs1 rd1 with
      ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      rw [takeAfterTransfers_shape]
      exact ExecBlock.consNormal hx1 hx
    · refine Or.inr (Or.inr ⟨frame2, evm2, ?_, hr⟩)
      rw [takeAfterTransfers_shape]
      exact ExecBlock.consNormal hx1 hx

end Benchmarks.Midnight
