import Benchmarks.Midnight.TakeGateDecision

/-! Skipping an unnecessary gate and enforcing a decoded gate response. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

theorem midnightTakeGateHead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
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
    (¬ TakeGateNeeded offer (kind.delta increase debt) ∧ ∃ aw' k' C',
      MemoryFunding credit mem aw' C' ∧
      RD midnightBytecode I g s0 kind.finishPC
        ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
        mem aw' rdata σ k' C') ∨
    (TakeGateNeeded offer (kind.delta increase debt) ∧ ∃ aw' k' C',
      MemoryFunding credit mem aw' C' ∧
      RD midnightBytecode I g s0 kind.preparePC
        ([UInt256.ofNat offer.market.enterGate.val, ⟨0⟩, buyerSlot, debt, buyerDebt,
          sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
        mem aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeGateDecision kind hstack ho hoffer ha rd
  rw [takeGateSkipWord_eq] at rd1
  simp only [List.cons_append, List.nil_append] at rd1
  by_cases hn : TakeGateNeeded offer (kind.delta increase debt)
  · rw [if_pos hn] at rd1
    have rd2 : RD midnightBytecode I g s0 kind.preparePC
        ([UInt256.ofNat offer.market.enterGate.val, ⟨0⟩, buyerSlot, debt, buyerDebt,
          sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
        mem aw1 rdata σ (k1 + 5) (C1 + 20) := by
      cases kind with
      | credit =>
        exact midnight_block_12261_taken
          (R := [buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr,
            increase] ++ R)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by decide) (by jump_dest) rd1
      | debt =>
        exact midnight_block_12302_taken
          (R := [buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr,
            increase] ++ R)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by decide) (by jump_dest) rd1
    exact Or.inr ⟨hn, _, _, _, ha1.mono (by omega), rd2⟩
  · rw [if_neg hn] at rd1
    have rd3 : RD midnightBytecode I g s0 kind.finishPC
        ([buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr, increase] ++ R)
        mem aw1 rdata σ (k1 + 5 + 5) (C1 + 20 + 19) := by
      cases kind with
      | credit =>
        have rd2 := midnight_block_12261_fallthrough
          (by simp only [List.length_cons]; omega) (by decide) rd1
        exact midnight_block_12268_fallthrough
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (by decide) rd2
      | debt =>
        have rd2 := midnight_block_12302_fallthrough
          (by simp only [List.length_cons]; omega) (by decide) rd1
        exact midnight_block_12309_fallthrough
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (by decide) rd2
    exact Or.inl ⟨hn, _, _, _, ha1.mono (by omega), rd3⟩

theorem midnightTakeGateRequire {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw junk word : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (kind : TakeGateKind) (hstack : R.length + 4 ≤ 1024)
    (hc : word = ⟨0⟩ ∨ word = ⟨1⟩) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 kind.joinPC (junk :: word :: R) mem aw rdata σ k C) :
    (word = ⟨0⟩ ∧ RDrev midnightBytecode g s0) ∨
    (word = ⟨1⟩ ∧ ∃ k' C', MemoryFunding credit mem aw C' ∧
      RD midnightBytecode I g s0 kind.finishPC R mem aw rdata σ k' C') := by
  rcases hc with hz | hone
  · refine Or.inl ⟨hz, ?_⟩
    subst word
    cases kind with
    | credit =>
      have rd1 := midnight_block_12268_taken (by omega) (by decide) (by jump_dest) rd
      exact midnight_block_14266 (R := R) (by omega) rd1
    | debt =>
      have rd1 := midnight_block_12309_taken (by omega) (by decide) (by jump_dest) rd
      exact midnight_block_14145 (R := R) (by omega) rd1
  · refine Or.inr ⟨hone, k + 5, C + 19, ha.mono (by omega), ?_⟩
    subst word
    cases kind with
    | credit => exact midnight_block_12268_fallthrough (by omega) (by decide) rd
    | debt => exact midnight_block_12309_fallthrough (by omega) (by decide) rd

theorem midnightTakeGateTail {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw word w0 w1 w2 w3 w4 w5 w6 w7 w8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (kind : TakeGateKind)
    (hstack : R.length + 13 ≤ 1024) (hc : word = ⟨0⟩ ∨ word = ⟨1⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 kind.decodedPC
      ([word, w0, w1, w2, w3, w4, w5, w6, w7, w8] ++ R) mem aw rdata σ k C) :
    (word = ⟨0⟩ ∧ RDrev midnightBytecode g s0) ∨
    (word = ⟨1⟩ ∧ ∃ k' C', MemoryFunding credit mem aw C' ∧
      RD midnightBytecode I g s0 kind.finishPC
        ([w0, w1, w2, w3, w4, w5, w6, w7, w8] ++ R) mem aw rdata σ k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd2 : RD midnightBytecode I g s0 kind.joinPC
      ([w8, word, w0, w1, w2, w3, w4, w5, w6, w7, w8] ++ R)
      mem aw rdata σ (k + 4 + 5) (C + 15 + 17) := by
    cases kind with
    | credit =>
      have rd1 := midnight_block_14372 (by omega) (by jump_dest) rd
      exact midnight_block_14340 (R := R) (by omega) (by jump_dest) rd1
    | debt =>
      have rd1 := midnight_block_14251 (by omega) (by jump_dest) rd
      exact midnight_block_14219 (R := R) (by omega) (by jump_dest) rd1
  exact midnightTakeGateRequire kind
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hc (ha.mono (by omega)) rd2

end Benchmarks.Midnight
