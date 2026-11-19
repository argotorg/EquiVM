import Benchmarks.Midnight.TakeRatifierAuthFinish
import Benchmarks.Midnight.TakeOfferChecksRuntime
import Benchmarks.Midnight.TakeLossGuard

/-! Market alias and offer guards followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeChecksFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker
      saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (htCanon : taker.toNat < EVM.addressModulus)
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hused : root.toNat ≤ mem.size + 31)
    (hdLower : 832 ≤ takerPtr.toNat) (hratLower : 832 ≤ ratifierPtr.toNat)
    (hheap : offerRoot.toNat ≤ root.toNat) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hrat : MemoryByteString mem ratifierPtr ratifierData)
    (hratBelow : ratifierPtr.toNat + 32 + paddedSize ratifierData.size ≤ root.toNat)
    (ha : MemoryFunding credit mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (halign : root.toNat % 32 = 0)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (htakerWord : memLoad (UInt256.ofNat 544) mem = taker)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨10969⟩
      ([id, ratifierPtr, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 5) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 5) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (bought sold : UInt256) (frame' : Frame) (evm' : State),
      ExecBlock config frame evm (takeTransition.body.drop 5)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases memoryAccounting_headroom rd ha.accounting hgas with hoog | hroom
  · exact Or.inl hoog
  let frame1 := takeMarketAliasFrame frame id
  have hf1 : TakeSourceFrame frame1 offer id units taker initialReceiver initialCallback
      ratifierData data := hf.insert "_marketState" _ (by decide)
  have hm1 : frame1.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := store_get_self ..
  have source0 := takeMarketAliasPrefix (evm := evm) hf
  have hword : marketLossWord evm id = UInt256.shiftRight
      (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128) := by
    unfold marketLossWord
    rw [hs.storageRead]
    rfl
  have hguard := midnightTakeLossGuard (R := saved :: R)
    (by simp only [List.length_cons]; omega) ha rd
  rw [← hword] at hguard
  rcases hguard with ⟨hbad, hr⟩ | ⟨hloss, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨source0.run (takeLossRevert hm1 hbad), hr⟩))
  · let mem1 := takeMarketMemory mem id
    have hp := twoWordHashMem_prefix (writeWord mem 512 id) id (UInt256.ofNat 1) root.toNat
    have hsize1 : mem.size ≤ mem1.size :=
      (show mem.size ≤ (writeWord mem 512 id).size by
        rw [writeWord_sparse_size]; exact Nat.le_max_left _ _).trans hp.size
    have hread (off : UInt256) (hl : 64 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832)
        (hd : off.toNat + 32 ≤ 512 ∨ 544 ≤ off.toNat) :
        memLoad off mem1 = memLoad off mem := by
      dsimp only [mem1, takeMarketMemory]
      rw [memLoad_twoWordHashMem _ _ _ hl (by rw [writeWord_sparse_size]; omega)]
      exact memLoad_writeWord_preserved _ _ _ _ (hh.trans hsize) hd
    have hid1 : memLoad (UInt256.ofNat 512) mem1 = id := by
      dsimp only [mem1, takeMarketMemory]
      rw [memLoad_twoWordHashMem _ _ _ (by decide) (by
        rw [writeWord_sparse_size]; change 544 ≤ _; omega)]
      exact memLoad_writeWord mem (UInt256.ofNat 512) id
    have ho1 : OfferStored mem1 ⟨832⟩ market arrayPtr callbackPtr offerRoot offer :=
      (ho.writeWord_below id (by decide)).preserve (hp.mono hheap)
    have hoffer1 := (hread _ (by decide) (by decide) (Or.inl (by decide))).trans hoffer
    have htaker1 := (hread _ (by decide) (by decide) (Or.inr (by decide))).trans htakerWord
    have hreceiver1 := (hread _ (by decide) (by decide) (Or.inl (by decide))).trans hreceiver
    rcases midnightTakeOfferChecksRuntime (R := saved :: R)
        (by simp only [List.length_cons]; omega) hc htCanon ho1 hoffer1 htaker1 hreceiver1
        hloss hs ha1 rd1 with ⟨hbad, hr⟩ | ⟨hchecks, aw2, k2, C2, ha2, rd2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨source0.run
        (takeOfferChecksRevert hm1 hf1.offerValue hf1.taker hf1.receiver htCanon hbad), hr⟩))
    · have source1 := takeOfferChecksSource hm1 hf1.offerValue hf1.taker hf1.receiver
        htCanon hchecks
      have hbytes {ptr : UInt256} {bytes : ByteArray}
          (hx : MemoryByteString mem ptr bytes) (hl : 832 ≤ ptr.toNat)
          (hb : ptr.toNat + 32 + paddedSize bytes.size ≤ root.toNat) :
          MemoryByteString mem1 ptr bytes :=
        (hx.writeWord_below (off := 512) id (by omega) (by omega)).preserve hp hb
      rcases midnightTakeRatifierAuthFinish (frame := frame1) hstack hfork hgas hc hf1
          htCanon hm1 ho1 (hused.trans (Nat.add_le_add_right hsize1 31))
          hdLower hratLower hheap hlo (hsize.trans hsize1) (hbytes hd hdLower hbelow) hbelow
          (hbytes hrat hratLower hratBelow) hratBelow ha2
          ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hfree)
          ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hzero) halign
          hoffer1 ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans htaker)
          hid1 hreceiver1 ((hread _ (by decide) (by decide) (Or.inl (by decide))).trans hcallback)
          htaker1 hunits hs rd2 with
        hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨bought, sold, frame2, evm2, hx, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨source0.run (source1.run hx), hr⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨source0.run (source1.run hx), hr⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨bought, sold, frame2, evm2, source0.run (source1.run hx), hr⟩))

end Benchmarks.Midnight
