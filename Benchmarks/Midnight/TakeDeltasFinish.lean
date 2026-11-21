import Benchmarks.Midnight.TakeFeesFinish
import Benchmarks.Midnight.TakeCreditChanges

/-! Credit and debt deltas followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeDeltasFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker buyer seller
      time bought sold consumed saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (hbuyerCanon : buyer.toNat < EVM.addressModulus)
    (hsellerCanon : seller.toNat < EVM.addressModulus)
    (hconsumed128 : consumed.toNat < 2^128)
    (hfTime : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hfBuyerPos : frame.locals.get? "buyerPos" =
      some (.storageRef (positionRef id buyer) positionType))
    (hfSellerPos : frame.locals.get? "sellerPos" =
      some (.storageRef (positionRef id seller) positionType))
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (hfBuyer : frame.locals.get? "buyer" = some (.address (AccountAddress.ofNat buyer.toNat)))
    (hfSeller : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hfConsumed : frame.locals.get? "newConsumed" = some (.int consumed.toNat))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hused : root.toNat ≤ mem.size)
    (hdLower : 384 ≤ takerPtr.toNat) (hratLower : 384 ≤ ratifierPtr.toNat)
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
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (hbuyer : memLoad (UInt256.ofNat 576) mem = buyer)
    (hconsumed : memLoad (UInt256.ofNat 480) mem = consumed)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨12026⟩
      ([positionSlot id seller, solcMappingSlot ⟨1⟩ id, positionSlot id buyer,
        ratifierPtr, time, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 35) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 35) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 35)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  have hs' : SourceState s0 I evm.accountMap evm := by rw [← hs.accounts]; exact hs
  rw [hs.accounts] at rd
  obtain ⟨source1, hf1, aw1, k1, C1, ha1, rd1⟩ := midnightTakeCreditChanges
    (R := saved :: R) (by simp only [List.length_cons]; omega)
    hf hfBuyerPos hfSellerPos hbuyerCanon hsellerCanon hs' hunits ha rd
  let frame1 := takeCreditChangesFrame frame evm id buyer seller units
  let word := solcSlotWordAt (positionSlot id seller) evm.accountMap I
  let mem1 := takeCreditChangesMemory mem word
  have hget (name : Ident)
      (h1 : name ≠ "sellerDebtIncrease") (h2 : name ≠ "sellerCreditDecrease")
      (h3 : name ≠ "buyerCreditIncrease") :
      frame1.locals.get? name = frame.locals.get? name :=
    (store_get_ne _ _ (by simpa using h1.symm)).trans
      ((store_get_ne _ _ (by simpa using h2.symm)).trans
        (store_get_ne _ _ (by simpa using h3.symm)))
  have hread (off : UInt256) (hin : off.toNat + 32 ≤ 832)
      (hdisj : off.toNat + 32 ≤ 352 ∨ 384 ≤ off.toNat) :
      memLoad off mem1 = memLoad off mem :=
    memLoad_writeWord_preserved _ _ _ _ (hin.trans hsize) hdisj
  have hsize1 : mem.size ≤ mem1.size := by
    simp only [mem1, takeCreditChangesMemory, writeWord_sparse_size]; omega
  have hd1 : MemoryByteString mem1 takerPtr data :=
    hd.writeWord_below word hdLower (by omega)
  have hr1 : MemoryByteString mem1 ratifierPtr ratifierData :=
    hrat.writeWord_below word hratLower (by omega)
  have hpacked : memLoad (UInt256.ofNat 352) mem1 =
      EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id seller) := by
    change memLoad (UInt256.ofNat 352) (writeWord mem 352 word) = _
    exact (memLoad_writeWord mem (UInt256.ofNat 352) word).trans (hs'.storageRead _).symm
  rcases midnightTakeFeesFinish (frame := frame1) hstack hfork hgas hc hf1
      hbuyerCanon hsellerCanon hconsumed128
      ((hget _ (by decide) (by decide) (by decide)).trans hfTime)
      ((hget _ (by decide) (by decide) (by decide)).trans hfBuyerPos)
      ((hget _ (by decide) (by decide) (by decide)).trans hfSellerPos)
      (wordLocal_get ..)
      ((hget _ (by decide) (by decide) (by decide)).trans hfMarket)
      ((hget _ (by decide) (by decide) (by decide)).trans hfBuyer)
      ((hget _ (by decide) (by decide) (by decide)).trans hfSeller)
      ((hget _ (by decide) (by decide) (by decide)).trans hfBought)
      ((hget _ (by decide) (by decide) (by decide)).trans hfSold)
      ((hget _ (by decide) (by decide) (by decide)).trans hfConsumed)
      ((store_get_ne _ _ (by decide)).trans
        ((store_get_ne _ _ (by decide)).trans (wordLocal_get ..)))
      ((store_get_ne _ _ (by decide)).trans (wordLocal_get ..))
      (ho.writeWord_below word (by decide)) (hused.trans hsize1) (by omega) (by omega)
      hheap hlo (hsize.trans hsize1) hd1 hbelow hr1 hratBelow hb rfl rfl ha1
      ((hread _ (by decide) (Or.inl (by decide))).trans hfree)
      ((hread _ (by decide) (Or.inl (by decide))).trans hzero) halign
      ((hread _ (by decide) (Or.inr (by decide))).trans hoffer)
      ((hread _ (by decide) (Or.inl (by decide))).trans htaker)
      ((hread _ (by decide) (Or.inr (by decide))).trans hid)
      ((hread _ (by decide) (Or.inr (by decide))).trans hseller)
      ((hread _ (by decide) (Or.inl (by decide))).trans hbought)
      ((hread _ (by decide) (Or.inr (by decide))).trans hsold)
      ((hread _ (by decide) (Or.inl (by decide))).trans hreceiver)
      ((hread _ (by decide) (Or.inl (by decide))).trans hcallback)
      ((hread _ (by decide) (Or.inr (by decide))).trans hbuyer)
      ((hread _ (by decide) (Or.inr (by decide))).trans hconsumed)
      hpacked (wordMin_le_right _ _) hunits hs' rd1 with
    hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
