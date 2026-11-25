import Benchmarks.Midnight.TakeCapsGuard
import Benchmarks.Midnight.SettlementFields

variable {fork : Ethereum.Fork}

/-! The offer's continuous-fee cap, with the shared fee word retained for tick spacing. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def marketContinuousFee (word : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat 112)) (UInt256.ofNat 4294967295)

theorem midnightTakeFeeCapGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root slot ratifierPtr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 6 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11051⟩ (ratifierPtr :: slot :: R) mem aw rdata σ k C) :
    (¬ (marketContinuousFee (solcSlotWordAt (slot + UInt256.ofNat 2) σ I)).toNat ≤
        offer.continuousFeeCap.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    ((marketContinuousFee (solcSlotWordAt (slot + UInt256.ofNat 2) σ I)).toNat ≤
        offer.continuousFeeCap.toNat ∧
      ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨11080⟩
          (solcSlotWordAt (slot + UInt256.ofNat 2) σ I :: ratifierPtr :: slot :: R)
          mem aw' rdata σ k' C') := by
  have hcap : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 448) mem = offer.continuousFeeCap :=
    ho.words.load_offset ⟨14, by change 14 < 15; decide⟩ rfl
  let r0 := rd
  have r1 := r0.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have ha3 := memoryFundingAt (credit := credit) r3 (by memory_fund ha)
  obtain ⟨_, _, hc4, r4⟩ := RD.sloadMono r3 (by native_decide) (by evm_ov)
  have ha4 := ha3.mono hc4
  have r5 := r4.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r8 := r7.shr (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have r15 := r14.lt (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 14968) (by native_decide) (by evm_ov)
  simp only [hroot, hcap] at r16
  by_cases hc : (marketContinuousFee (solcSlotWordAt (slot + UInt256.ofNat 2) σ I)).toNat ≤
      offer.continuousFeeCap.toNat
  · have r17 := r16.jumpiNT (by native_decide) (by
      change UInt256.lt offer.continuousFeeCap
        (marketContinuousFee (solcSlotWordAt (slot + UInt256.ofNat 2) σ I)) = ⟨0⟩
      exact ult_zero hc) (by evm_ov)
    have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11080)) r17 (by native_decide)
    exact Or.inr ⟨hc, _, _, _, by memory_fund ha4, rFinal⟩
  · have hlt := ult_one (a := offer.continuousFeeCap)
      (b := marketContinuousFee (solcSlotWordAt (slot + UInt256.ofNat 2) σ I)) (by omega)
    have r17 := r16.jumpiT (by native_decide) (by
      change UInt256.lt offer.continuousFeeCap
        (marketContinuousFee (solcSlotWordAt (slot + UInt256.ofNat 2) σ I)) ≠ ⟨0⟩
      rw [hlt]; decide) (by jump_dest) (by evm_ov)
    exact Or.inl ⟨hc, midnightBlocks.midnight_block_14968 (by
      simp only [List.length_cons]; omega) r17⟩

end Benchmarks.Midnight
