import Benchmarks.Midnight.TakeOfferChecksSource
import Benchmarks.Midnight.TakeRatifierAuthorization
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-! The offer guards share the same memory and source state. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightTakeOfferChecksRuntime {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray}
    {aw market arrayPtr callbackPtr offerRoot id taker ratifierPtr : UInt256}
    {offer : OfferData} {receiver : AccountAddress} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hc : OfferCanonical offer)
    (htCanon : taker.toNat < EVM.addressModulus)
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 544) mem = taker)
    (hreceiver : memLoad (UInt256.ofNat 288) mem = UInt256.ofNat receiver.val)
    (hloss : (marketLossWord evm id).toNat < 2^128 - 1)
    (hs : SourceState s0 I σ evm) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11009⟩
      (ratifierPtr :: solcMappingSlot ⟨1⟩ id :: R) mem aw rdata σ k C) :
    (¬ TakeOfferChecks evm offer id taker receiver ∧ RDrev fork midnightBytecode g s0) ∨
    (TakeOfferChecks evm offer id taker receiver ∧
      ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨11209⟩
          (ratifierPtr :: solcMappingSlot ⟨1⟩ id :: R) mem aw' rdata σ k' C') := by
  rcases midnightTakeCapsGuard (by simp only [List.length_cons]; omega)
      ho hc hoffer ha rd with ⟨hbad, hr⟩ | ⟨hcap, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl ⟨fun h ↦ hbad h.caps, hr⟩
  have hword : marketFeeWord evm id =
      solcSlotWordAt (solcMappingSlot ⟨1⟩ id + UInt256.ofNat 2) σ I := hs.storageRead _
  have hfee := midnightTakeFeeCapGuard (by omega) ho hoffer ha1 rd1
  rw [← hword] at hfee
  rcases hfee with ⟨hbad, hr⟩ | ⟨hfee, aw2, k2, C2, ha2, rd2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.fee, hr⟩
  rcases midnightTakeTickGuard (by simp only [List.length_cons]; omega)
      ho hoffer ha2 rd2 with ⟨hbad, hr⟩ | ⟨hspacing, htick, aw3, k3, C3, ha3, rd3⟩
  · exact Or.inl ⟨fun h ↦ hbad.elim h.spacing (fun hn ↦ hn h.tick), hr⟩
  rcases midnightTakeTimeGuard (by simp only [List.length_cons]; omega)
      ho hoffer ha3 rd3 with ⟨hbad, hr⟩ | ⟨htime, aw4, k4, C4, ha4, rd4⟩
  · exact Or.inl ⟨fun h ↦ hbad (by simpa only [hs.env] using h.time), hr⟩
  rcases midnightTakeSelfGuard (by simp only [List.length_cons]; omega)
      ho hoffer htaker htCanon ha4 rd4 with ⟨hbad, hr⟩ | ⟨hself, aw5, k5, C5, ha5, rd5⟩
  · exact Or.inl ⟨fun h ↦ h.self hbad, hr⟩
  rcases midnightTakeReceiverGuard (by simp only [List.length_cons]; omega)
      ho hoffer hreceiver ha5 rd5 with ⟨hbad, hr⟩ | ⟨hrecv, aw6, k6, C6, ha6, rd6⟩
  · exact Or.inl ⟨fun h ↦ hbad h.receiver, hr⟩
  exact Or.inr ⟨⟨hloss, hcap, hfee, hspacing, htick,
    by simpa only [hs.env] using htime, hself, hrecv⟩, aw6, k6, C6, ha6, rd6⟩

end Benchmarks.Midnight
