import Benchmarks.Midnight.TakeRatifierFinish
import Benchmarks.Midnight.TakeRatifierAuthorization
import Benchmarks.Midnight.TakeRatifierSource

/-! Ratifier authorization followed by the complete trade suffix. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeRatifierAuthFinish {credit : Nat} {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
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
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨11209⟩
      ([ratifierPtr, solcMappingSlot ⟨1⟩ id, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm (takeTransition.body.drop 14) .staticViolation ∧
      RDstatic midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (ExecBlock config frame evm (takeTransition.body.drop 14) .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (bought sold : UInt256) (frame' : Frame) (evm' : State),
      ExecBlock config frame evm (takeTransition.body.drop 14)
        (.returned frame' evm' (some [.int bought.toNat, .int sold.toNat])) ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap
        (wordArrayBytes [bought, sold]) := by
  have hs' : SourceState s0 I evm.accountMap evm := by rw [← hs.accounts]; exact hs
  rw [hs.accounts] at rd
  rcases midnightTakeRatifierAuthorization
      (R := [ratifierPtr, solcMappingSlot ⟨1⟩ id, saved] ++ R) evm hs.env
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by omega) ho hoffer ha rd with
    ⟨hbad, hr⟩ | ⟨hgood, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inr (Or.inr (Or.inl
      ⟨takeRatifierRevert hf.contract hf.authorization hf.offerValue hbad, hr⟩))
  · have source1 := takeRatifierSource hf.contract hf.authorization hf.offerValue hgood
    have hp := takeRatifierMemory_prefix mem offer root.toNat
    have hread (off : UInt256) (hl : 64 ≤ off.toNat) (hh : off.toNat + 32 ≤ 832) :
        memLoad off (takeRatifierMemory mem offer) = memLoad off mem :=
      takeRatifierMemory_load _ _ _ hl (hh.trans hsize)
    rcases midnightTakeRatifierFinish hstack hfork hgas hc hf htCanon hfMarket
        (ho.preserve (hp.mono hheap)) (hused.trans (Nat.add_le_add_right hp.size 31))
        hdLower hratLower hheap hlo (hsize.trans hp.size) (hd.preserve hp hbelow) hbelow
        (hrat.preserve hp hratBelow) hratBelow ha1
        ((hread _ (by decide) (by decide)).trans hfree)
        ((hread _ (by decide) (by decide)).trans hzero) halign
        ((hread _ (by decide) (by decide)).trans hoffer)
        ((hread _ (by decide) (by decide)).trans htaker)
        ((hread _ (by decide) (by decide)).trans hid)
        ((hread _ (by decide) (by decide)).trans hreceiver)
        ((hread _ (by decide) (by decide)).trans hcallback)
        ((hread _ (by decide) (by decide)).trans htakerWord)
        hunits hs' rd1 with
      hoog | ⟨hx, hr⟩ | ⟨hx, hr⟩ | ⟨bought, sold, frame2, evm2, hx, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨source1.run hx, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨source1.run hx, hr⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨bought, sold, frame2, evm2, source1.run hx, hr⟩))

end Benchmarks.Midnight
