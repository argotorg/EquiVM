import Benchmarks.Midnight.TakeConsumptionRead

/-! Runtime consumption check, including overflow and cap failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeConsumptionRuntime {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr root units bought sold : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 5 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hc : OfferCanonical offer) (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hu : calldataWord I.calldata 68 = units)
    (hb : memLoad (UInt256.ofNat 256) mem = bought)
    (hs : memLoad (UInt256.ofNat 416) mem = sold)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11681⟩ R mem aw rdata σ k C) :
    (¬ TakeConsumptionSafe (takeConsumedWord σ I offer) offer units bought sold ∧
      RDrev midnightBytecode g s0) ∨
    (TakeConsumptionSafe (takeConsumedWord σ I offer) offer units bought sold ∧
      ∃ aw' k' C',
        MemoryFunding credit (takeConsumptionMemory mem offer
          (takeConsumedWord σ I offer + takeConsumedDelta offer units bought sold)) aw' C' ∧
        RD midnightBytecode I g s0 ⟨11826⟩ R
          (takeConsumptionMemory mem offer
            (takeConsumedWord σ I offer + takeConsumedDelta offer units bought sold))
          aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ :=
    midnightTakeConsumptionRead hstack ho hc hroot hu hb hs ha rd
  have hm : 416 ≤ mem.size := by
    have hh := ho.words.size
    change 832 + 32 * 15 ≤ mem.size at hh
    omega
  have hroot1 : memLoad (UInt256.ofNat 384) (takeConsumptionReadMemory mem offer) = ⟨832⟩ := by
    rw [takeConsumptionReadMemory_load offer (UInt256.ofNat 384) (by decide) hm
      (Or.inl (by decide)), hroot]
  by_cases hfit : (takeConsumedWord σ I offer).toNat +
      (takeConsumedDelta offer units bought sold).toNat < UInt256.size
  · obtain ⟨k2, C2, hC2, rd2⟩ := midnightCheckedAdd_mono (by omega) hfit (by
      unfold takeConsumptionCheckPC
      split <;> jump_dest) rd1
    have ha2 := ha1.mono hC2
    have hadd : (takeConsumedWord σ I offer + takeConsumedDelta offer units bought sold).toNat =
        (takeConsumedWord σ I offer).toNat +
          (takeConsumedDelta offer units bought sold).toNat := addWord_toNat _ _ hfit
    rcases midnightTakeConsumptionCap (by omega) (takeConsumptionReadMemory_offer ho)
      hc hroot1 ha2 rd2 with ⟨hbad, hr⟩ | ⟨hle, aw3, k3, C3, ha3, rd3⟩
    · exact Or.inl ⟨fun h ↦ hbad (by rw [hadd]; exact h), hr⟩
    · rw [hadd] at hle
      exact Or.inr ⟨hle, aw3, k3, C3, ha3, rd3⟩
  · have hbad : ¬ TakeConsumptionSafe (takeConsumedWord σ I offer) offer units bought sold := by
      intro h
      exact hfit (lt_of_le_of_lt h (takeConsumedCap offer).val.isLt)
    exact Or.inl ⟨hbad, midnightCheckedAddRevert (by omega) (by omega) rd1⟩

end Benchmarks.Midnight
