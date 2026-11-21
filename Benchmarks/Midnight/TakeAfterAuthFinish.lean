import Benchmarks.Midnight.TakeChecksFinish
import Benchmarks.Midnight.TakeSourceEntry
import Benchmarks.Midnight.TouchMarketInternalCredit
import Benchmarks.Midnight.MarketHeapExtent
import Benchmarks.Midnight.TakeInputMemory

/-! The internal market initialization followed by the complete take suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeAfterAuthFinish {credit : Nat} {origin : State} {g : UInt256}
    {mem rdata ratifierData data : ByteArray}
    {aw callbackPtr ratifierPtr takerPtr root units taker saved : UInt256}
    {offer : OfferData} {receiver callback : AccountAddress} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : origin.executionEnv.fork ≥ .osaka)
    (hgas : midnightGasBound g) (hc : OfferCanonical offer)
    (htCanon : taker.toNat < EVM.addressModulus)
    (hi : TakeInputStored mem callbackPtr ratifierPtr takerPtr root offer ratifierData data)
    (hroot : root.toNat = takeInputSize offer ratifierData data)
    (hused : root.toNat ≤ mem.size) (ha : MemoryFunding credit mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat receiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat callback.val)
    (htakerWord : memLoad (UInt256.ofNat 544) mem = taker)
    (hunits : calldataWord origin.executionEnv.calldata 68 = units)
    (rd : RD midnightBytecode origin.executionEnv (Sat256.ofUInt256 g) origin ⟨10957⟩
      (ratifierPtr :: saved :: R) mem aw rdata origin.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) origin = .error .OutOfGass ∨
    (ExecBlock config (takeExternalFrame origin offer ratifierData units taker receiver callback data)
        origin (takeTransition.body.drop 4) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) origin) ∨
    (ExecBlock config (takeExternalFrame origin offer ratifierData units taker receiver callback data)
        origin (takeTransition.body.drop 4) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) origin) ∨
    ∃ (bought sold : UInt256) (frame' : Frame) (evm' : State),
      ExecBlock config (takeExternalFrame origin offer ratifierData units taker receiver callback data)
        origin (takeTransition.body.drop 4)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) origin evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightMemoryPaid_small rd ha.accounting.paid hgas with hoog | haw
  · exact Or.inl hoog
  have hsmall : root.toNat < 3200000 :=
    lt_of_le_of_lt (hused.trans ha.covered) (by omega)
  have hbound := hi.bound
  have hratEnd := hi.ratifierEnd
  have htakerEnd := hi.takerEnd
  have hmarketEnd := hi.offer.market.extent
  have hofferEnd := hi.offer.extent
  change 1600 ≤ callbackPtr.toNat at hmarketEnd
  have hlo : 832 ≤ root.toNat := by omega
  have hsize : 832 ≤ mem.size := hlo.trans hused
  have hheap : ratifierPtr.toNat ≤ root.toNat := by omega
  have hm := hi.offer.market.mono_root (larger := root) (by omega) hbound
  have hb : root.toNat + 5 * offer.market.encodingSize + 800 < 2^64 := by
    dsimp only [MarketData.encodingSize]
    unfold takeInputSize at hroot
    omega
  have halign : root.toNat % 32 = 0 := by
    rw [hroot]
    unfold takeInputSize paddedSize
    omega
  have hmarket : memLoad (⟨832⟩ : UInt256) mem = ⟨1312⟩ :=
    hi.offer.words.load_word ⟨0, by change 0 < 15; decide⟩ rfl
  have rd0 := midnightBlocks.midnight_block_10957
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  have ha0 := memoryFundingAt (credit := credit) rd0 (by memory_fund ha)
  simp only [midnightBlocks.midnight_block_10957_stack, hoffer, hmarket] at rd0 ha0
  rcases midnightTouchMarketInternal_fundedCredit (g := Sat256.ofUInt256 g) (imms := ∅)
      (evm := origin) (R := ratifierPtr :: saved :: R) (ret := ⟨10969⟩)
      offer.market (by simp only [List.length_cons]; omega) hm hb hused halign hgas ha0
      hfree rfl (by jump_dest) rd0 with
    hoog | ⟨hr, hx⟩ | ⟨hr, hx⟩ |
      ⟨callee, evm1, σ1, out, mem1, root1, aw1, k1, C1, hs1, htouch, hp,
        hrootLo, hrootBound, hrootHi, hfree1, halign1, hused1, ha1, rd1⟩
  · exact Or.inl hoog
  · refine Or.inr (Or.inr (Or.inl ⟨ExecBlock.consRevert ?_, hr⟩))
    exact internalCallFunctionRevert
      (takeTouchArgs origin offer ratifierData units taker receiver callback data) rfl rfl hx
  · refine Or.inr (Or.inl ⟨ExecBlock.consStatic ?_, hr⟩)
    exact ExecStmt.internalCallStatic
      (takeTouchArgs origin offer ratifierData units taker receiver callback data) rfl rfl hx
  · have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem :=
      hp.load off hl (hh.trans hlo) (hh.trans hsize)
    rcases midnightTakeChecksFinish (frame := takeAfterTouchFrame origin offer ratifierData
        units taker receiver callback data) (root := root1) hstack hfork hgas hc
        (takeAfterTouchFrame_spec ..) htCanon
        (hi.offer.preserve (hp.mono hheap)) hused1 (by omega) (by omega)
        (hheap.trans hrootLo) (hlo.trans hrootLo) (hsize.trans hp.size)
        (hi.taker.preserve hp (by omega)) (by omega)
        (hi.ratifier.preserve hp (by omega)) (by omega) ha1 hfree1
        ((hread _ (by decide) (by decide)).trans hzero) halign1
        ((hread _ (by decide) (by decide)).trans hoffer)
        ((hread _ (by decide) (by decide)).trans htaker)
        ((hread _ (by decide) (by decide)).trans hreceiver)
        ((hread _ (by decide) (by decide)).trans hcallback)
        ((hread _ (by decide) (by decide)).trans htakerWord) hunits hs1 rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨bought, sold, frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨takeAfterTouchSource htouch hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨takeAfterTouchSource htouch hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨bought, sold, frame2, evm2, takeAfterTouchSource htouch hx, hr⟩))

end Benchmarks.Midnight
