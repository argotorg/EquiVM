import Benchmarks.Midnight.TakePositionsFinish
import Benchmarks.Midnight.TakeConsumption

/-! Offer consumption followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeConsumptionFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker
      time bought sold saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (htCanon : taker.toNat < EVM.addressModulus)
    (hfTime : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
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
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (htakerWord : memLoad (UInt256.ofNat 544) mem = taker)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨11681⟩
      ([solcMappingSlot ⟨1⟩ id, ratifierPtr, time, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 25) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 25) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 25)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  rcases midnightTakeConsumption (R := [solcMappingSlot ⟨1⟩ id, ratifierPtr, time, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hf hfBought hfSold ho hc hoffer hunits hbought hsold hs ha rd with
    ⟨hx, hr⟩ | ⟨hconsumed128, source1, hf1, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hr⟩))
  · let consumed := takeConsumedStored evm offer + takeConsumedDelta offer units bought sold
    let frame1 := takeConsumptionFrame frame (takeConsumedStored evm offer) offer units bought sold
    let mem1 := takeConsumptionMemory mem offer consumed
    have hget (name : Ident) (hn : name ≠ "newConsumed") :
        frame1.locals.get? name = frame.locals.get? name :=
      (store_get_ne _ _ (by simpa using hn.symm)).trans
        (store_get_ne _ _ (by simpa using hn.symm))
    have hread (off : UInt256) (hl : 64 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832)
        (hd : off.toNat + 32 ≤ 480 ∨ 512 ≤ off.toNat) :
        memLoad off mem1 = memLoad off mem :=
      takeConsumptionMemory_load _ _ _ hl (hh.trans hsize) hd
    have hsize1 : mem.size ≤ mem1.size :=
      (takeConsumptionReadMemory_size mem offer).trans (by
        change (takeConsumptionReadMemory mem offer).size ≤ (writeWord _ 480 consumed).size
        rw [writeWord_sparse_size]; exact Nat.le_max_left _ _)
    have hbytes {ptr : UInt256} {bytes : ByteArray}
        (hx : MemoryByteString mem ptr bytes) (hl : 608 ≤ ptr.toNat)
        (hb : ptr.toNat + 32 + paddedSize bytes.size ≤ root.toNat) :
        MemoryByteString mem1 ptr bytes := by
      have hpad : paddedSize bytes.size < 2^64 := by omega
      exact ((hx.writeWord_below (off := 480) ⟨0⟩ (by omega) hpad).preserve
        (consumedHashMemory_prefix _ _ _ root.toNat) hb).writeWord_below consumed (by omega) hpad
    rcases midnightTakePositionsFinish (frame := frame1) hstack hfork hgas hc hf1
        htCanon hconsumed128
        ((hget _ (by decide)).trans hfTime) ((hget _ (by decide)).trans hfMarket)
        ((hget _ (by decide)).trans hfBought) ((hget _ (by decide)).trans hfSold)
        (wordLocal_get ..)
        (takeConsumptionMemory_offer ho) (hused.trans hsize1) hdLower hratLower
        hheap hlo (hsize.trans hsize1) (hbytes hd hdLower hbelow) hbelow
        (hbytes hrat hratLower hratBelow) hratBelow hb ha1
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hfree)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hzero) halign
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hoffer)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans htaker)
        ((hread _ (by decide) (by decide) (Or.inr (by decide))).trans hid)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hbought)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hsold)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hreceiver)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hcallback)
        (takeConsumptionMemory_value ..)
        ((hread _ (by decide) (by decide) (Or.inr (by decide))).trans htakerWord)
        hunits hs rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
