import Benchmarks.Midnight.TouchMarketHeaderTrace
import Benchmarks.Midnight.MemoryFunding

/-! Funding retained by the header checks for a fresh market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTouchMarketHeader_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr arrayPtr root id ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (m : MarketData) (hstack : R.length + 9 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m) (hfund : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨20764⟩
      ((ptr + UInt256.ofNat 32) :: ptr :: id :: ret :: R) mem aw rdata σ k C) :
    (¬ TouchMarketHeaderSafe I m ∧ RDrev midnightBytecode g s0) ∨
    (TouchMarketHeaderSafe I m ∧ ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨20840⟩
        (⟨0⟩ :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id :: ⟨0⟩ :: R)
        mem aw' rdata σ k' C') := by
  rcases midnightTouchMarketHeader m hstack hm rd with hbad | ⟨hsafe, _⟩
  · exact Or.inl hbad
  obtain ⟨hc, ha, ht, hmat, hn, hcount⟩ := hsafe
  have hchain : (UInt256.ofNat Ethereum.chainId).toNat = Ethereum.chainId := by native_decide
  have he : UInt256.ofNat Ethereum.chainId = m.chainId := u256_inj (by rw [hchain, hc])
  have haddress : UInt256.land solcAddrMask (UInt256.ofNat m.midnight.val) =
      UInt256.ofNat m.midnight.val := solcAddrMask_clean_left (addressWord_canonical m.midnight)
  have hlen : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    ulit_toNat' _ (lt_trans hm.collateralCount (by decide))
  have rd1 := midnightBlocks.midnight_block_20764_fallthrough
    (by simp only [List.length_cons]; omega) (by rw [hm.chainId, he, u256_sub_self]; rfl) rd
  have hf1 := memoryFundingAt (credit := credit) rd1 (by memory_fund hfund)
  have rd2 := midnightBlocks.midnight_block_20773_fallthrough
    (by simp only [List.length_cons]; omega)
    (by rw [hm.midnight, addressMask_computed, haddress, ha, u256_sub_self]; rfl) rd1
  have hf2 := memoryFundingAt (credit := credit) rd2 (by memory_fund hf1)
  simp only [midnightBlocks.midnight_block_20773_fallthrough_stack] at rd2
  have hsum := uadd_word_ofNat_toNat (UInt256.ofNat I.header.timestamp) 3153600000 ht
  have rd3 := midnightBlocks.midnight_block_20789_fallthrough
    (by simp only [List.length_cons]; omega) (ugt_zero (by rw [hsum]; omega)) rd2
  have hf3 := memoryFundingAt (credit := credit) rd3 (by memory_fund hf2)
  simp only [midnightBlocks.midnight_block_20789_fallthrough_stack, hm.maturity] at rd3
  have rd4 := midnightBlocks.midnight_block_20809_fallthrough
    (by simp only [List.length_cons]; omega) (ugt_zero (by rw [hsum]; exact hmat)) rd3
  have hf4 := memoryFundingAt (credit := credit) rd4 (hf3.mono (by omega))
  simp only [midnightBlocks.midnight_block_20809_fallthrough_stack] at rd4
  have hnz : UInt256.ofNat m.collaterals.length ≠ (⟨0⟩ : UInt256) := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [hlen] at hzNat
    change m.collaterals.length = 0 at hzNat
    omega
  have rd5 := midnightBlocks.midnight_block_20814_fallthrough
    (by simp only [List.length_cons]; omega)
    (by rw [hm.arrayPtr, hm.length]; exact isZero_eq_zero_of_ne hnz) rd4
  have hf5 := memoryFundingAt (credit := credit) rd5 (by memory_fund hf4)
  simp only [midnightBlocks.midnight_block_20814_fallthrough_stack] at rd5
  have rd6 := midnightBlocks.midnight_block_20827_fallthrough
    (by simp only [List.length_cons]; omega)
    (by rw [hm.arrayPtr, hm.length]; apply ugt_zero; rw [hlen]; exact hcount) rd5
  have hf6 := memoryFundingAt (credit := credit) rd6 (by memory_fund hf5)
  have rd7 := midnightBlocks.midnight_block_20837 (by omega) rd6
  exact Or.inr ⟨⟨hc, ha, ht, hmat, hn, hcount⟩, _, _, _, hf6.mono (by omega), rd7⟩

end Benchmarks.Midnight
