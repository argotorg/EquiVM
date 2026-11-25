import Benchmarks.Midnight.TakeAmountsFinish
import Benchmarks.Midnight.TakeSpreadSource

variable {fork : Ethereum.Fork}

/-! Price spread followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeSpreadFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker
      time price fee saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (htCanon : taker.toNat < EVM.addressModulus)
    (hfTime : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (hfPrice : frame.locals.get? "offerPrice" = some (.int price.toNat))
    (hfFee : frame.locals.get? "_settlementFee" = some (.int fee.toNat))
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
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨11556⟩
      ([fee, ⟨11591⟩, price, solcMappingSlot ⟨1⟩ id, ratifierPtr, time, saved] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 20) .staticViolation ∧
      RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 20) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (bought sold : UInt256) (frame' : Frame) (evm' : State),
      ExecBlock fork config frame evm (takeTransition.body.drop 20)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightTakeSpread (R := [solcMappingSlot ⟨1⟩ id, ratifierPtr, time, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      ho hoffer ha rd with
    ⟨hbad, hr⟩ | ⟨hsafe, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl
      ⟨takeSpreadSourceRevert hf.offerValue hfPrice hfFee hbad, hr⟩))
  · have source1 := takeSpreadSource (fork := fork) (evm := evm) hf.offerValue hfPrice hfFee hsafe
    let frame1 := takeSpreadFrame frame offer.buy price fee
    have hget (name : Ident) (hb : name ≠ "buyerPrice") (hs : name ≠ "sellerPrice") :
        frame1.locals.get? name = frame.locals.get? name :=
      (store_get_ne _ _ (by simpa using hb.symm)).trans
        (store_get_ne _ _ (by simpa using hs.symm))
    rcases midnightTakeAmountsFinish (frame := frame1) hstack hfork hgas hc hf.spread htCanon
        ((hget _ (by decide) (by decide)).trans hfTime)
        ((hget _ (by decide) (by decide)).trans hfMarket)
        (wordLocal_get ..) ((store_get_ne _ _ (by decide)).trans (wordLocal_get ..))
        ho hused hdLower hratLower hheap hlo hsize hd hbelow hrat hratBelow hb ha1
        hfree hzero halign hoffer htaker hid hreceiver hcallback htakerWord hunits hs rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨bought, sold, frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨bought, sold, frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
