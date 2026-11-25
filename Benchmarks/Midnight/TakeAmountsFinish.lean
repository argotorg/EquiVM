import Benchmarks.Midnight.TakeConsumptionFinish
import Benchmarks.Midnight.TakeAmounts

variable {fork : Ethereum.Fork}

/-! Asset calculations followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeAmountsFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker
      time buyerPrice sellerPrice saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (htCanon : taker.toNat < EVM.addressModulus)
    (hfTime : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (hfBuyerPrice : frame.locals.get? "buyerPrice" = some (.int buyerPrice.toNat))
    (hfSellerPrice : frame.locals.get? "sellerPrice" = some (.int sellerPrice.toNat))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hused : root.toNat ≤ mem.size)
    (hdLower : 608 ≤ takerPtr.toNat) (hratLower : 608 ≤ ratifierPtr.toNat)
    (hheap : offerRoot.toNat ≤ root.toNat) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hrat : MemoryByteString mem ratifierPtr ratifierData)
    (hratBelow : ratifierPtr.toNat + 32 + paddedSize ratifierData.size ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 256 < UInt256.size)
    (ha : MemoryFunding credit mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (halign : root.toNat % 32 = 0)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (htakerWord : memLoad (UInt256.ofNat 544) mem = taker)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨11591⟩
      ([buyerPrice, sellerPrice, solcMappingSlot ⟨1⟩ id, ratifierPtr, time, saved] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 22) .staticViolation ∧
      RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 22) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (bought sold : UInt256) (frame' : Frame) (evm' : State),
      ExecBlock fork config frame evm (takeTransition.body.drop 22)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  rcases midnightTakeAmounts (R := [solcMappingSlot ⟨1⟩ id, ratifierPtr, time, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hf hfBuyerPrice hfSellerPrice ho hoffer hunits ha rd with
    ⟨hx, hr⟩ | ⟨source1, hf1, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hr⟩))
  · let bought := takeAmount offer.buy units buyerPrice
    let sold := takeAmount offer.buy units sellerPrice
    let frame1 := takeAmountsFrame frame offer.buy units buyerPrice sellerPrice
    let mem1 := takeAmountsMemory mem bought sold
    have hget (name : Ident) (h1 : name ≠ "sellerAssets") (h2 : name ≠ "sold")
        (h3 : name ≠ "buyerAssets") (h4 : name ≠ "bought") :
        frame1.locals.get? name = frame.locals.get? name :=
      (store_get_ne _ _ (by simpa using h1.symm)).trans
        ((store_get_ne _ _ (by simpa using h2.symm)).trans
          (takeAmountsBuyerFrame_get _ _ _ _ _ h3 h1 h4))
    have hfBought : frame1.locals.get? "buyerAssets" = some (.int bought.toNat) :=
      (store_get_ne _ _ (by decide)).trans
        ((store_get_ne _ _ (by decide)).trans (wordLocal_get ..))
    have hfSold : frame1.locals.get? "sellerAssets" = some (.int sold.toNat) := wordLocal_get ..
    have hread (off : UInt256) (hh : off.toNat + 32 ≤ 832)
        (hb : off.toNat + 32 ≤ 256 ∨ 288 ≤ off.toNat)
        (hs : off.toNat + 32 ≤ 416 ∨ 448 ≤ off.toNat) :
        memLoad off mem1 = memLoad off mem :=
      takeAmountsMemory_load _ _ _ (hh.trans hsize) hb hs
    have hsize1 : mem.size ≤ mem1.size :=
      (takeAmountMemory_size mem 256 bought).trans (takeAmountMemory_size _ 416 sold)
    have hbytes {ptr : UInt256} {bytes : ByteArray}
        (hx : MemoryByteString mem ptr bytes) (hl : 608 ≤ ptr.toNat)
        (hb : ptr.toNat + 32 + paddedSize bytes.size ≤ root.toNat) :
        MemoryByteString mem1 ptr bytes := by
      have hpad : paddedSize bytes.size < 2^64 := by omega
      exact (((hx.writeWord_below (off := 256) ⟨0⟩ (by omega) hpad).writeWord_below
        (off := 256) bought (by omega) hpad).writeWord_below
        (off := 416) ⟨0⟩ (by omega) hpad).writeWord_below sold (by omega) hpad
    rcases midnightTakeConsumptionFinish (frame := frame1) hstack hfork hgas hc hf1 htCanon
        ((hget _ (by decide) (by decide) (by decide) (by decide)).trans hfTime)
        ((hget _ (by decide) (by decide) (by decide) (by decide)).trans hfMarket)
        hfBought hfSold
        (takeAmountMemory_offer (takeAmountMemory_offer ho (by decide) bought) (by decide) sold)
        (hused.trans hsize1) hdLower hratLower hheap hlo (hsize.trans hsize1)
        (hbytes hd hdLower hbelow) hbelow (hbytes hrat hratLower hratBelow) hratBelow hb ha1
        ((hread _ (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hfree)
        ((hread _ (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hzero) halign
        ((hread _ (by decide) (Or.inr (by decide)) (Or.inl (by decide))).trans hoffer)
        ((hread _ (by decide) (Or.inr (by decide)) (Or.inl (by decide))).trans htaker)
        ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans hid)
        (takeAmountsMemory_bought ..)
        (takeAmountsMemory_sold ..)
        ((hread _ (by decide) (Or.inr (by decide)) (Or.inl (by decide))).trans hreceiver)
        ((hread _ (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans hcallback)
        ((hread _ (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans htakerWord)
        hunits hs rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨bought, sold, frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
