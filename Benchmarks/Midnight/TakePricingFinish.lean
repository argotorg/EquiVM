import Benchmarks.Midnight.TakeSpreadFinish

/-! Pricing and settlement fee followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakePricingFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker
      saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (htCanon : taker.toNat < EVM.addressModulus)
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hused : root.toNat ≤ mem.size)
    (hdLower : 832 ≤ takerPtr.toNat) (hratLower : 832 ≤ ratifierPtr.toNat)
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
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨11413⟩
      ([ratifierPtr, solcMappingSlot ⟨1⟩ id, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 17) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 17) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (bought sold : UInt256) (frame' : Frame) (evm' : State),
      ExecBlock config frame evm (takeTransition.body.drop 17)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  rcases midnightTakePricing (R := saved :: R) (by simp only [List.length_cons]; omega)
      hf ho hoffer hid hs ha rd with
    ⟨hx, hr⟩ | ⟨source1, hf1, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hr⟩))
  · let fee := settlementFeeValue (marketFeeWord evm id) (takeTimeToMaturity I offer)
    let frame1 := takePricingFrame frame I offer fee
    let mem1 := takePricingMemory mem id
    have hfMarket1 : frame1.locals.get? "_marketState" =
        some (.storageRef (marketStateRef id) marketStateType) :=
      (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans
        ((store_get_ne _ _ (by decide)).trans hfMarket))
    have hread (off : UInt256) (hl : 64 ≤ off.toNat) (hh : off.toNat + 32 ≤ 800) :
        memLoad off mem1 = memLoad off mem :=
      takePricingMemory_load _ _ hl (by omega) (Or.inl hh)
    have hsize1 : mem.size ≤ mem1.size := (takePricingMemory_prefix mem id).size
    have hbytes {ptr : UInt256} {bytes : ByteArray}
        (hx : MemoryByteString mem ptr bytes) (hl : 832 ≤ ptr.toNat)
        (hb : ptr.toNat + 32 + paddedSize bytes.size ≤ root.toNat) :
        MemoryByteString mem1 ptr bytes :=
      (hx.writeWord_below (off := 800) ⟨0⟩ hl (by omega)).preserve
        (twoWordHashMem_prefix _ _ _ root.toNat) hb
    rcases midnightTakeSpreadFinish (frame := frame1) hstack hfork hgas hc hf1 htCanon
        ((store_get_ne _ _ (by decide)).trans (wordLocal_get ..)) hfMarket1
        ((store_get_ne _ _ (by decide)).trans
          ((store_get_ne _ _ (by decide)).trans (wordLocal_get ..)))
        (wordLocal_get ..)
        (takePricingMemory_offer ho) (hused.trans hsize1) (by omega) (by omega)
        hheap hlo (hsize.trans hsize1) (hbytes hd hdLower hbelow) hbelow
        (hbytes hrat hratLower hratBelow) hratBelow hb ha1
        ((hread _ (by decide) (by decide)).trans hfree)
        ((hread _ (by decide) (by decide)).trans hzero) halign
        ((hread _ (by decide) (by decide)).trans hoffer)
        ((hread _ (by decide) (by decide)).trans htaker)
        ((hread _ (by decide) (by decide)).trans hid)
        ((hread _ (by decide) (by decide)).trans hreceiver)
        ((hread _ (by decide) (by decide)).trans hcallback)
        ((hread _ (by decide) (by decide)).trans htakerWord)
        hunits hs rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨bought, sold, frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨bought, sold, frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
