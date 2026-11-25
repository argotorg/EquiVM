import Benchmarks.Midnight.TouchMarketHeaderSource
import Benchmarks.Midnight.MarketHeapAccess
import Benchmarks.Midnight.RuntimeBlocks_079
import Benchmarks.Midnight.RuntimeBlocks_081

variable {fork : Ethereum.Fork}

/-! Runtime execution of the checks that precede the collateral-validation loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightTouchMarketHeader {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr root id ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (m : MarketData) (hstack : R.length + 9 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m)
    (rd : RD fork midnightBytecode I g s0 ⟨20764⟩
      ((ptr + UInt256.ofNat 32) :: ptr :: id :: ret :: R) mem aw rdata σ k C) :
    (¬ TouchMarketHeaderSafe I m ∧ RDrev fork midnightBytecode g s0) ∨
    (TouchMarketHeaderSafe I m ∧ ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨20840⟩
      (⟨0⟩ :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id :: ⟨0⟩ :: R)
      mem aw' rdata σ k' C') := by
  have hchain : (UInt256.ofNat Ethereum.chainId).toNat = Ethereum.chainId := by native_decide
  have haddress : UInt256.land solcAddrMask (UInt256.ofNat m.midnight.val) =
      UInt256.ofNat m.midnight.val := solcAddrMask_clean_left (by
    rw [ulit_toNat' _ (lt_trans m.midnight.isLt (by decide))]
    exact m.midnight.isLt)
  have hlen : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    ulit_toNat' _ (lt_trans hm.collateralCount (by decide))
  by_cases hc : m.chainId.toNat = Ethereum.chainId
  · have he : UInt256.ofNat Ethereum.chainId = m.chainId := u256_inj (by rw [hchain, hc])
    have rd1 := midnightBlocks.midnight_block_20764_fallthrough (by
      simp only [List.length_cons]; omega) (by rw [hm.chainId, he, u256_sub_self]; rfl) rd
    by_cases ha : m.midnight = I.codeOwner
    · have rd2 := midnightBlocks.midnight_block_20773_fallthrough (by
        simp only [List.length_cons]; omega) (by
          rw [hm.midnight, addressMask_computed, haddress, ha, u256_sub_self]; rfl) rd1
      simp only [midnightBlocks.midnight_block_20773_fallthrough_stack] at rd2
      by_cases ht : (UInt256.ofNat I.header.timestamp).toNat + 3153600000 < UInt256.size
      · have hsum := uadd_word_ofNat_toNat (UInt256.ofNat I.header.timestamp) 3153600000 ht
        have rd3 := midnightBlocks.midnight_block_20789_fallthrough (by
          simp only [List.length_cons]; omega) (ugt_zero (by rw [hsum]; omega)) rd2
        simp only [midnightBlocks.midnight_block_20789_fallthrough_stack, hm.maturity] at rd3
        by_cases hmat : m.maturity.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat + 3153600000
        · have rd4 := midnightBlocks.midnight_block_20809_fallthrough (by
            simp only [List.length_cons]; omega) (ugt_zero (by rw [hsum]; exact hmat)) rd3
          simp only [midnightBlocks.midnight_block_20809_fallthrough_stack] at rd4
          by_cases hn : 0 < m.collaterals.length
          · have hnz : UInt256.ofNat m.collaterals.length ≠ ⟨0⟩ := by
              intro hz
              have hzNat := congrArg UInt256.toNat hz
              rw [hlen] at hzNat
              change m.collaterals.length = 0 at hzNat
              omega
            have rd5 := midnightBlocks.midnight_block_20814_fallthrough (by
              simp only [List.length_cons]; omega) (by
                rw [hm.arrayPtr, hm.length]; exact isZero_eq_zero_of_ne hnz) rd4
            simp only [midnightBlocks.midnight_block_20814_fallthrough_stack] at rd5
            by_cases hcount : m.collaterals.length ≤ 128
            · have rd6 := midnightBlocks.midnight_block_20827_fallthrough (by
                simp only [List.length_cons]; omega) (by
                  rw [hm.arrayPtr, hm.length]
                  apply ugt_zero
                  rw [hlen]; exact hcount) rd5
              have rd7 := midnightBlocks.midnight_block_20837 (by omega) rd6
              exact Or.inr ⟨⟨hc, ha, ht, hmat, hn, hcount⟩, _, _, _, rd7⟩
            · left
              refine ⟨fun hs ↦ hcount hs.2.2.2.2.2, ?_⟩
              have hgt : UInt256.gt (UInt256.ofNat m.collaterals.length)
                  (UInt256.ofNat 128) = ⟨1⟩ := ugt_one (by rw [hlen]; exact Nat.lt_of_not_ge hcount)
              have rd6 := midnightBlocks.midnight_block_20827_taken (by
                simp only [List.length_cons]; omega) (by
                  rw [hm.arrayPtr, hm.length, hgt]; decide) (by jump_dest) rd5
              exact midnightBlocks.midnight_block_21760 (by simp only [List.length_cons]; omega) rd6
          · left
            refine ⟨fun hs ↦ hn hs.2.2.2.2.1, ?_⟩
            have he : m.collaterals.length = 0 := by omega
            have rd5 := midnightBlocks.midnight_block_20814_taken (by
              simp only [List.length_cons]; omega) (by
                rw [hm.arrayPtr, hm.length, he]; decide) (by jump_dest) rd4
            exact midnightBlocks.midnight_block_21775 (by
              simp only [midnightBlocks.midnight_block_20814_taken_stack, List.length_cons]; omega) rd5
        · left
          refine ⟨fun hs ↦ hmat hs.2.2.2.1, ?_⟩
          have hgt : UInt256.gt m.maturity
              (UInt256.ofNat I.header.timestamp + UInt256.ofNat 3153600000) = ⟨1⟩ :=
            ugt_one (by rw [hsum]; exact Nat.lt_of_not_ge hmat)
          have rd4 := midnightBlocks.midnight_block_20809_taken (by
            simp only [List.length_cons]; omega) (by rw [hgt]; decide) (by jump_dest) rd3
          exact midnightBlocks.midnight_block_21790 (by
            simp only [midnightBlocks.midnight_block_20809_taken_stack, List.length_cons]; omega) rd4
      · left
        refine ⟨fun hs ↦ ht hs.2.2.1, ?_⟩
        have hgt : UInt256.gt (UInt256.ofNat I.header.timestamp)
            (UInt256.ofNat I.header.timestamp + UInt256.ofNat 3153600000) = ⟨1⟩ := by
          rw [u256_add_comm]
          exact u256_gt_add_right_of_overflow _ _ (Nat.le_of_not_gt ht)
        have rd3 := midnightBlocks.midnight_block_20789_taken (by
          simp only [List.length_cons]; omega) (by rw [hgt]; decide) (by jump_dest) rd2
        exact midnightBlocks.midnight_block_7302 (by
          simp only [midnightBlocks.midnight_block_20789_taken_stack, List.length_cons]; omega) rd3
    · left
      refine ⟨fun hs ↦ ha hs.2.1, ?_⟩
      have rd2 := midnightBlocks.midnight_block_20773_taken (by
        simp only [List.length_cons]; omega) (by
          rw [hm.midnight, addressMask_computed, haddress]
          exact u256_sub_ne_zero_of_ne (fun he ↦ ha (Reasoning.VyperDispatch.ofNat_addr_inj he).symm))
            (by jump_dest) rd1
      exact midnightBlocks.midnight_block_21805 (by
        simp only [midnightBlocks.midnight_block_20773_taken_stack, List.length_cons]; omega) rd2
  · left
    refine ⟨fun hs ↦ hc hs.1, ?_⟩
    have rd1 := midnightBlocks.midnight_block_20764_taken (by
      simp only [List.length_cons]; omega) (by
        rw [hm.chainId]
        apply u256_sub_ne_zero_of_ne
        intro he
        apply hc
        rw [← he, hchain]) (by jump_dest) rd
    exact midnightBlocks.midnight_block_21820 (by simp only [List.length_cons]; omega) rd1

end Benchmarks.Midnight
