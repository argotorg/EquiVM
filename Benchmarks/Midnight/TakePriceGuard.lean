import Benchmarks.Midnight.TickPriceRuntime
import Benchmarks.Midnight.TakeTickGuard
import Benchmarks.Midnight.RuntimeBlocks_055

variable {fork : Ethereum.Fork}

/-! Tick range validation and price arithmetic at the take call site. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakePriceGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 13 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11413⟩ R mem aw rdata σ k C) :
    (6744 < offer.tick.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (offer.tick.toNat ≤ 6744 ∧ ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11514⟩
        (UInt256.div (tickPriceNumerator offer.tick.toNat)
            (tickPriceDenominator offer.tick.toNat) ::
          UInt256.ofNat 49999999999 :: UInt256.ofNat 100000000000 ::
          UInt256.ofNat 100000000000 :: R) mem aw' rdata σ k' C') := by
  have ht : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 160) mem = offer.tick :=
    ho.words.load_offset ⟨5, by change 5 < 15; decide⟩ rfl
  by_cases hb : offer.tick.toNat ≤ 6744
  · have rd1 := midnightBlocks.midnight_block_11413_fallthrough (by omega) (by
      rw [hroot, ht]
      exact ugt_zero hb) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    simp only [midnightBlocks.midnight_block_11413_fallthrough_stack, hroot, ht] at rd1 ha1
    obtain ⟨k2, C2, hC2, rd2⟩ := midnightTickPriceCore hstack hb rd1
    exact Or.inr ⟨hb, _, k2, C2, ha1.mono hC2, rd2⟩
  · have rd1 := midnightBlocks.midnight_block_11413_taken (by omega) (by
      rw [hroot, ht, ugt_one (by change 6744 < offer.tick.toNat; omega)]
      decide) (by jump_dest) rd
    exact Or.inl ⟨by omega, midnightBlocks.midnight_block_14766
      (by change R.length + 1 + 2 ≤ 1024; omega) rd1⟩

end Benchmarks.Midnight
