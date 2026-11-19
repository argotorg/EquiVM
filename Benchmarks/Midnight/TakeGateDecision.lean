import Benchmarks.Midnight.TakeGatePrepare
import Benchmarks.Midnight.TakeGateSource

/-! Runtime evaluation of the gate-address and trade-delta conditions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

def TakeGateKind.startPC : TakeGateKind → UInt256
  | .credit => ⟨12234⟩
  | .debt => ⟨12275⟩

def TakeGateKind.branchPC : TakeGateKind → UInt256
  | .credit => ⟨12261⟩
  | .debt => ⟨12302⟩

def TakeGateKind.joinPC : TakeGateKind → UInt256
  | .credit => ⟨12268⟩
  | .debt => ⟨12309⟩

def TakeGateKind.finishPC : TakeGateKind → UInt256
  | .credit => ⟨12275⟩
  | .debt => ⟨12316⟩

def TakeGateKind.delta (kind : TakeGateKind) (increase debt : UInt256) : UInt256 :=
  match kind with | .credit => increase | .debt => debt

def takeGateSkipWord (offer : OfferData) (delta : UInt256) : UInt256 :=
  if offer.market.enterGate = 0 then ⟨1⟩ else UInt256.isZero delta

theorem takeGateSkipWord_eq (offer : OfferData) (delta : UInt256) :
    takeGateSkipWord offer delta = if TakeGateNeeded offer delta then ⟨0⟩ else ⟨1⟩ := by
  by_cases hg : offer.market.enterGate = 0
  · have hn : ¬ TakeGateNeeded offer delta := fun h ↦ h.1 hg
    rw [takeGateSkipWord, if_pos hg, if_neg hn]
  · rw [takeGateSkipWord, if_neg hg]
    by_cases hd : delta = ⟨0⟩
    · have hn : ¬ TakeGateNeeded offer delta := fun h ↦ h.2 hd
      rw [if_neg hn, hd]
      rfl
    · rw [if_pos ⟨hg, hd⟩, isZero_eq_zero_of_ne hd]

set_option maxRecDepth 10000

theorem midnightTakeGateDecision {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw marketPtr arrayPtr callbackPtr root buyerSlot debt buyerDebt sellerSlot marketSlot
      decrease ratifierPtr increase : UInt256} {offer : OfferData} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (kind : TakeGateKind)
    (hstack : R.length + 12 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 kind.startPC
      ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD midnightBytecode I g s0 kind.branchPC
        ([UInt256.ofNat offer.market.enterGate.val,
          takeGateSkipWord offer (kind.delta increase debt), buyerSlot, debt, buyerDebt,
          sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
        mem aw' rdata σ k' C' := by
  have hm : memLoad (⟨832⟩ : UInt256) mem = marketPtr :=
    ho.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
  have hg : memLoad (memLoad (memLoad (UInt256.ofNat 384) mem) mem + UInt256.ofNat 192) mem =
      UInt256.ofNat offer.market.enterGate.val := by
    rw [hoffer, hm]
    exact ho.market.words.load_offset ⟨6, by change 6 < 8; decide⟩ rfl
  have hc : UInt256.land (UInt256.ofNat offer.market.enterGate.val) solcAddrMask =
      UInt256.ofNat offer.market.enterGate.val := addressWord_val_clean offer.market.enterGate
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hz : offer.market.enterGate = 0
  · have hw : UInt256.ofNat offer.market.enterGate.val = (⟨0⟩ : UInt256) := by rw [hz]; rfl
    cases kind with
    | credit =>
      have rd1 := midnight_block_12234_fallthrough
        (by simp only [List.length_cons]; omega)
        (by rw [hg, addressMask_computed, hc, hw]; decide) rd
      have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
      simp only [midnight_block_12234_fallthrough_stack, hg, addressMask_computed, hw] at rd1
      simp only [takeGateSkipWord, if_pos hz, hw]
      exact ⟨_, _, _, ha1, rd1⟩
    | debt =>
      have rd1 := midnight_block_12275_fallthrough
        (by simp only [List.length_cons]; omega)
        (by rw [hg, addressMask_computed, hc, hw]; decide) rd
      have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
      simp only [midnight_block_12275_fallthrough_stack, hg, addressMask_computed, hw] at rd1
      simp only [takeGateSkipWord, if_pos hz, hw]
      exact ⟨_, _, _, ha1, rd1⟩
  · have hw : UInt256.ofNat offer.market.enterGate.val ≠ (⟨0⟩ : UInt256) := by
      intro h
      apply hz
      apply Fin.ext
      have hv := congrArg UInt256.toNat h
      have hn : (UInt256.ofNat offer.market.enterGate.val).toNat = offer.market.enterGate.val :=
        addressWord_toNat_val offer.market.enterGate
      rw [hn] at hv
      exact hv
    cases kind with
    | credit =>
      have rd1 := midnight_block_12234_taken
        (by simp only [List.length_cons]; omega)
        (by rw [hg, addressMask_computed, hc, isZero_eq_zero_of_ne hw]; decide)
        (by jump_dest) rd
      have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
      simp only [midnight_block_12234_taken_stack, hg, addressMask_computed, hc] at rd1
      have rd2 := midnight_block_14378 (by omega) (by jump_dest) rd1
      have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
      simp only [takeGateSkipWord, if_neg hz]
      exact ⟨_, _, _, ha2, rd2⟩
    | debt =>
      have rd1 := midnight_block_12275_taken
        (by simp only [List.length_cons]; omega)
        (by rw [hg, addressMask_computed, hc, isZero_eq_zero_of_ne hw]; decide)
        (by jump_dest) rd
      have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
      simp only [midnight_block_12275_taken_stack, hg, addressMask_computed, hc] at rd1
      have rd2 := midnight_block_14257 (by simp only [List.length_cons]; omega) (by jump_dest) rd1
      have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
      simp only [takeGateSkipWord, if_neg hz]
      exact ⟨_, _, _, ha2, rd2⟩

end Benchmarks.Midnight
