import Benchmarks.Midnight.TakeAfterAccounting
import Benchmarks.Midnight.TakeAccounting

variable {fork : Ethereum.Fork}

/-! The last two accounting writes and the complete event/payment suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeCommit {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      buyerFee sellerFee bought sold consumed increase decrease saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (hbuyerCanon : buyer.toNat < EVM.addressModulus)
    (hsellerCanon : seller.toNat < EVM.addressModulus)
    (hbuyerFee128 : buyerFee.toNat < 2^128) (hsellerFee128 : sellerFee.toNat < 2^128)
    (hconsumed128 : consumed.toNat < 2^128)
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
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨19447⟩
      ([bought, sold, ⟨12598⟩, decrease, ratifierPtr, increase, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 58) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock fork config frame evm (takeTransition.body.drop 58)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightTakeAccounting (R := [decrease, ratifierPtr, increase, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hf.contract hf.claimableFee hf.consumed hf.offerValue hfBought hfSold hfConsumed
      hconsumed128 hperm ho hoffer hconsumed hs ha rd with
    ⟨hx, hr⟩ | ⟨σ1, aw1, k1, C1, hle, source1, hs1, ha1, rd1⟩
  · exact Or.inr (Or.inl ⟨hx, hr⟩)
  · let mem1 := takeAccountingMemory mem offer
    have hp : MemoryPrefix mem mem1 root.toNat :=
      (twoWordHashMem_prefix ..).trans (consumedHashMemory_prefix ..)
    have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem := hp.load off hl (by omega) (by omega)
    have hfree1 : memLoad (UInt256.ofNat 64) mem1 = root := by
      dsimp only [mem1]
      rw [takeAccountingMemory, consumedHashMemory_load _ _ _ (by decide) (by
        rw [takeSettlementMemory, twoWordHashMem_size_of_ge_64 _ _ (by omega)]
        change 96 ≤ mem.size
        omega), takeSettlementMemory, memLoad_twoWordHashMem _ _ _ (by decide) (by
        change 96 ≤ mem.size
        omega), hfree]
    rcases midnightTakeAfterAccounting hstack hfork hgas hc hf hbuyerCanon hsellerCanon
        hbuyerFee128 hsellerFee128 hi128 hd128 hfBuyer hfSeller hfBought hfSold hfConsumed
        hfBuyerFee hfSellerFee hfIncrease hfDecrease hle
        (ho.preserve (hp.mono hheap)) hroot hdLower hratLower hheap hlo (hsize.trans hp.size)
        (hd.preserve hp hbelow) hbelow (hrat.preserve hp hratBelow) hratBelow hb hperm ha1
        hfree1 ((hread _ (by decide) (by decide)).trans hzero) halign
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
        ((hread _ (by decide) (by decide)).trans hbuyerFee) hunits hs1 rd1 with
      hoog | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1 _ hx, hr⟩)
    · exact Or.inr (Or.inr ⟨frame2, evm2, source1 _ hx, hr⟩)

end Benchmarks.Midnight
