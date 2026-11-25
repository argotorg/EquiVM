import Benchmarks.Midnight.TakePricingFinish
import Benchmarks.Midnight.RatifierCall

variable {fork : Ethereum.Fork}

/-! Ratifier call followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeRatifierFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata data ratifierData : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot takerPtr ratifierPtr id units taker
      saved : UInt256}
    {offer : OfferData} {initialReceiver initialCallback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : fork ≥ .osaka) (hgas : midnightGasBound g)
    (hc : OfferCanonical offer)
    (hf : TakeSourceFrame frame offer id units taker initialReceiver initialCallback ratifierData data)
    (htCanon : taker.toNat < EVM.addressModulus)
    (hfMarket : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
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
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat initialReceiver.val)
    (hcallback : memLoad (UInt256.ofNat 192) mem = UInt256.ofNat initialCallback.val)
    (htakerWord : memLoad (UInt256.ofNat 544) mem = taker)
    (hunits : calldataWord I.calldata 68 = units)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨11276⟩
      ([ratifierPtr, solcMappingSlot ⟨1⟩ id, saved] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 15) .staticViolation ∧
      RDstatic fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 15) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (bought sold : UInt256) (frame' : Frame) (evm' : State),
      ExecBlock fork config frame evm (takeTransition.body.drop 15)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  rcases midnightMemoryPaid_small rd ha.accounting.paid hgas with hoog | haw
  · exact Or.inl hoog
  have hrootSmall : root.toNat < 3200031 := by
    have hcover := ha.covered
    change mem.size ≤ 32 * aw.toNat at hcover
    omega
  have hcb := ho.extent
  have hma := ho.market.extent
  have hma32 : (arrayPtr + UInt256.ofNat 32).toNat = arrayPtr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hn := ho.market.collaterals.extent (by rw [hma32]; exact hma)
    (by change callbackPtr.toNat < 2^256; omega)
  rw [hma32] at hn
  have hlen : ratifierCalldataSize offer ratifierData < 2^64 := by
    unfold ratifierCalldataSize offerEncodedSize offerCallbackOffset
    omega
  have ht : memLoad (UInt256.ofNat 544) mem =
      UInt256.ofNat (AccountAddress.ofNat taker.toNat).val :=
    htakerWord.trans (addressWord_eq_ofNat_address htCanon).symm
  rcases midnightRatifierCall (R := [solcMappingSlot ⟨1⟩ id, saved] ++ R)
      offer (AccountAddress.ofNat taker.toNat)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by omega) (by omega) ho hc hrat hheap hratBelow (by omega) hlen hfree hoffer ht
      hf.offerValue hf.ratifierData hf.taker hs ha rd with
    ⟨hx, hr⟩ | ⟨evm1, σ1, mem1, out, aw1, k1, C1, source1, hs1, hp, hfree1, hused1, ha1, rd1⟩
  · refine Or.inr (Or.inr (Or.inl ⟨?_, hr⟩))
    rw [ratifierCall_shape]
    exact execBlock_reverted_append hx
  · let frame1 := ratifierCallFrame frame flashLoanMagic
    let root1 := root + UInt256.ofNat 32
    have hroot1 : root1.toNat = root.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hread (off : UInt256) (hl : 96 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off mem1 = memLoad off mem :=
      hp.load off hl (hh.trans hlo) (hh.trans hsize)
    have hsource {result : ExecResult}
        (hx : ExecBlock fork config frame1 evm1 (takeTransition.body.drop 17) result) :
        ExecBlock fork config frame evm (takeTransition.body.drop 15) result := by
      rw [ratifierCall_shape]
      exact execBlock_append_ok source1 hx
    rcases midnightTakePricingFinish (frame := frame1) (root := root1)
        hstack hfork hgas hc (ratifierCallFrame_spec hf _) htCanon
        ((store_get_ne _ _ (by decide)).trans hfMarket)
        (ho.preserve (hp.mono hheap)) (by rw [hroot1]; exact hused1)
        hdLower hratLower (by rw [hroot1]; omega) (by rw [hroot1]; omega)
        (hsize.trans hp.size) (hd.preserve hp hbelow) (by rw [hroot1]; omega)
        (hrat.preserve hp hratBelow) (by rw [hroot1]; omega)
        (by rw [hroot1]; unfold ratifierCalldataSize at hlen; change _ < 2^256; omega)
        ha1 hfree1
        ((hread _ (by decide) (by decide)).trans hzero) (by rw [hroot1]; omega)
        ((hread _ (by decide) (by decide)).trans hoffer)
        ((hread _ (by decide) (by decide)).trans htaker)
        ((hread _ (by decide) (by decide)).trans hid)
        ((hread _ (by decide) (by decide)).trans hreceiver)
        ((hread _ (by decide) (by decide)).trans hcallback)
        ((hread _ (by decide) (by decide)).trans htakerWord)
        hunits hs1 rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨bought, sold, frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hsource hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hsource hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨bought, sold, frame2, evm2, hsource hx, hr⟩))

end Benchmarks.Midnight
