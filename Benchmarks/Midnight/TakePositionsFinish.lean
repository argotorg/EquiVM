import Benchmarks.Midnight.TakeDeltasFinish
import Benchmarks.Midnight.TakePositionUpdates

/-! Position preparation and updates followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakePositionsFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker
      time bought sold consumed saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (htCanon : taker.toNat < EVM.addressModulus)
    (hconsumed128 : consumed.toNat < 2^128)
    (hfTime : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hfConsumed : frame.locals.get? "newConsumed" = some (.int consumed.toNat))
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
    (hconsumed : memLoad (UInt256.ofNat 480) mem = consumed)
    (htakerWord : memLoad (UInt256.ofNat 544) mem = taker)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨11826⟩
      ([solcMappingSlot ⟨1⟩ id, ratifierPtr, time, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 27) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 27) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (takeTransition.body.drop 27)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  have hs' : SourceState s0 I evm.accountMap evm := by rw [← hs.accounts]; exact hs
  rw [hs.accounts] at rd
  rcases midnightTakePositionUpdates (R := [ratifierPtr, time, saved] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      htCanon hf hs' ho hlo (by omega) hheap hfree hoffer hid htakerWord hunits ha rd with
    ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨source1, hf1, hs1, hp, hfree1, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hx, hr⟩))
  · exact Or.inr (Or.inl ⟨hx, hr⟩)
  · let frame1 := takePositionUpdatesFrame frame evm offer id units taker
    let evm1 := takePositionUpdatesState evm offer id units taker
    let mem0 := takePositionPrepareMemory mem offer id taker
    let mem1 := takePositionUpdatesMemory mem root evm offer id units taker
    have hsize0 : mem.size ≤ mem0.size := takePositionPrepareMemory_size ..
    have hsize1 : mem.size ≤ mem1.size := hsize0.trans hp.size
    have hget (name : Ident)
        (h1 : name ≠ "__c10") (h2 : name ≠ "__c11") (h3 : name ≠ "__c12")
        (h4 : name ≠ "__c9") (h5 : name ≠ "buyerPos") (h6 : name ≠ "sellerPos")
        (h7 : name ≠ "seller") (h8 : name ≠ "buyer") :
        frame1.locals.get? name = frame.locals.get? name :=
      (takePositionUpdatesFrame_get _ _ _ _ _ _ _ h1 h2 h3).trans
        ((takePositionReadFrame_get _ _ _ _ _ _ h4 h5 h6).trans
          ((store_get_ne _ _ (by simpa using h7.symm)).trans
            (store_get_ne _ _ (by simpa using h8.symm))))
    have hload (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem0 :=
      hp.load off hl (hh.trans hlo) (hh.trans (hsize.trans hsize0))
    have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832)
        (hbuyer : off.toNat + 32 ≤ 576 ∨ 608 ≤ off.toNat)
        (hseller : off.toNat + 32 ≤ 448 ∨ 480 ≤ off.toNat) :
        memLoad off mem1 = memLoad off mem :=
      (hload off hl hh).trans (takePositionPrepareMemory_load _ _ _ _
        (by omega) (hh.trans hsize) hbuyer hseller)
    have hbytes {ptr : UInt256} {bytes : ByteArray}
        (hx : MemoryByteString mem ptr bytes) (hl : 608 ≤ ptr.toNat)
        (hb : ptr.toNat + 32 + paddedSize bytes.size ≤ root.toNat) :
        MemoryByteString mem1 ptr bytes := by
      have hpad : paddedSize bytes.size < 2^64 := by omega
      have h0 : MemoryByteString (takeParticipantsMemory mem offer taker) ptr bytes :=
        (((hx.writeWord_below (off := 576) ⟨0⟩ hl hpad).writeWord_below
          (off := 448) ⟨0⟩ (by omega) hpad).writeWord_below
          (off := 576) (takeBuyer offer taker) hl hpad).writeWord_below
          (off := 448) (takeSeller offer taker) (by omega) hpad
      exact (h0.preserve (takePositionsMemory_prefix _ _ _ _ root.toNat) hb).preserve hp hb
    rcases midnightTakeDeltasFinish (frame := frame1) hstack hfork hgas hc hf1
        (takeBuyer_canonical htCanon) (takeSeller_canonical htCanon) hconsumed128
        ((hget _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans hfTime)
        (takePositionUpdatesFrame_buyerPos ..) (takePositionUpdatesFrame_sellerPos ..)
        ((hget _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans hfMarket)
        ((takePositionUpdatesFrame_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
          (takePositionPrepareFrame_buyer ..))
        ((takePositionUpdatesFrame_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
          (takePositionPrepareFrame_seller ..))
        ((hget _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans hfBought)
        ((hget _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans hfSold)
        ((hget _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans hfConsumed)
        ((takePositionPrepareMemory_offer ho).preserve (hp.mono hheap))
        (hused.trans hsize1) (by omega) (by omega) hheap hlo (hsize.trans hsize1)
        (hbytes hd hdLower hbelow) hbelow (hbytes hrat hratLower hratBelow) hratBelow hb ha1
        hfree1
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide))).trans hzero) halign
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide))).trans hoffer)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide))).trans htaker)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inr (by decide))).trans hid)
        ((hload _ (by decide) (by decide)).trans
          (takePositionPrepareMemory_seller _ _ _ (by omega)))
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide))).trans hbought)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide))).trans hsold)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide))).trans hreceiver)
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inl (by decide))).trans hcallback)
        ((hload _ (by decide) (by decide)).trans
          (takePositionPrepareMemory_buyer _ _ _ (by omega)))
        ((hread _ (by decide) (by decide) (Or.inl (by decide))
          (Or.inr (by decide))).trans hconsumed)
        hunits hs1 rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1 _ hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1 _ hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame2, evm2, source1 _ hx, hr⟩))

end Benchmarks.Midnight
