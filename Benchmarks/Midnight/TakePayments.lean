import Benchmarks.Midnight.TakeAfterTransfers

/-! Both token payments followed by the optional seller callback and cleanup. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakePayments {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data : ByteArray} {aw root market arrayPtr callbackPtr offerRoot
      takerPtr id units seller receiver fee wasLocked saved ignored bought sold : UInt256}
    {offer : OfferData} {callback payer : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 28 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
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
    (hfPayer : frame.locals.get? "payer" = some (.address payer))
    (hle : sold.toNat ≤ bought.toNat)
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
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨13252⟩
      ([ignored, UInt256.ofNat callback.val, UInt256.ofNat payer.val, wasLocked, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 68) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 68)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap (wordArrayBytes [bought, sold]) := by
  have hrword : UInt256.ofNat (AccountAddress.ofNat receiver.toNat).val = receiver :=
    addressWord_eq_ofNat_address hrcanon
  have hreceiver' : memLoad (UInt256.ofNat 128) mem =
      UInt256.ofNat (AccountAddress.ofNat receiver.toNat).val := hreceiver.trans hrword.symm
  rcases midnightTakeTransfers (R := wasLocked :: saved :: R)
      (by simp only [List.length_cons]; omega) hc hfOffer hfPayer hfReceiver hfBought hfSold hle
      ho hheap hlo (by omega) hoffer hbought hsold hreceiver' hh hgas hfork hs rd with
    hoog | ⟨hx, hr⟩ | ⟨evm1, σ1, mem1, out1, root1, aw1, k1, C1,
      hsource1, hs1, hp1, hlo1, hh1, rd1⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨hx, hr⟩)
  · let frame1 := resumeAfterInternalCall (resumeAfterInternalCall frame "__c28" none) "__c29" none
    have hget (name : Ident) (hn : name ≠ "__c28") (hn' : name ≠ "__c29") :
        frame1.locals.get? name = frame.locals.get? name :=
      (store_get_ne _ _ (by simpa using hn'.symm)).trans
        (store_get_ne _ _ (by simpa using hn.symm))
    have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem := hp1.load off hl (by omega) (by omega)
    rcases midnightTakeAfterTransfers (frame := frame1) hstack hfork hgas hc hcanon hrcanon hfee128
        ((hget _ (by decide) (by decide)).trans hfOffer)
        ((hget _ (by decide) (by decide)).trans hfId)
        ((hget _ (by decide) (by decide)).trans hfSeller)
        ((hget _ (by decide) (by decide)).trans hfReceiver)
        ((hget _ (by decide) (by decide)).trans hfWasLocked)
        ((hget _ (by decide) (by decide)).trans hfBought)
        ((hget _ (by decide) (by decide)).trans hfSold)
        ((hget _ (by decide) (by decide)).trans hfFee)
        ((hget _ (by decide) (by decide)).trans hfUnits)
        ((hget _ (by decide) (by decide)).trans hfData)
        ((hget _ (by decide) (by decide)).trans hfCallback)
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
    · exact Or.inr (Or.inl ⟨hsource1 _ hx, hr⟩)
    · exact Or.inr (Or.inr ⟨frame2, evm2, hsource1 _ hx, hr⟩)

end Benchmarks.Midnight
