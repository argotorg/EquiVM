import Benchmarks.Midnight.CollateralValidationTrace
import Benchmarks.Midnight.MemoryArrayIndexFunding
import Benchmarks.Midnight.CollateralLifGas
import Benchmarks.Midnight.CollateralValidationStorageFunding

/-! A collateral-validation iteration retaining paid memory growth. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES midnightCollateralValidationStep with memory funding.
set_option maxRecDepth 2000000 in
theorem midnightCollateralValidationStep_funded {credit : Nat} {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr root id ret : UInt256} {k C : Nat}
    {R : List UInt256} (m : MarketData) (previous : AccountAddress) (c : CollateralData)
    (i : Nat) (hi : i < m.collaterals.length) (hc : m.collaterals[i] = c)
    (hstack : R.length + 15 ≤ 1024) (hm : MarketStored mem ptr arrayPtr root m)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨20840⟩
      (UInt256.ofNat previous.val :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id ::
        UInt256.ofNat i :: R) mem aw rdata evm.accountMap k C) :
    (¬ CollateralValid evm previous c ∧ RDrev midnightBytecode g s0) ∨
    (CollateralValid evm previous c ∧ ∃ aw' k' C',
      MemoryFunding credit (collateralValidationMemory mem c) aw' C' ∧
      RD midnightBytecode evm.executionEnv g s0 ⟨20840⟩
      (UInt256.ofNat c.token.val :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id ::
        UInt256.ofNat (i + 1) :: R) (collateralValidationMemory mem c) aw' rdata evm.accountMap k' C') := by
  have hi64 : i < 2^64 := lt_trans hi hm.collateralCount
  have hin : (UInt256.ofNat i).toNat = i := ulit_toNat' _ (lt_trans hi64 (by decide))
  have hlen : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    ulit_toNat' _ (lt_trans hm.collateralCount (by decide))
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat m.collaterals.length) = ⟨1⟩ :=
    ult_one (by rw [hin, hlen]; exact hi)
  have himem : (UInt256.ofNat i).toNat < (memLoad arrayPtr mem).toNat := by
    rw [hm.length, hin, hlen]; exact hi
  have hmem : 64 ≤ mem.size := by
    have hlo := hm.lower; have hs := hm.words.size
    change ptr.toNat + 32 * 8 ≤ mem.size at hs
    omega
  obtain ⟨cp, hcp, hcplo, hcphi, hw⟩ := hm.collaterals.get i hi
  rw [hc] at hw
  have htoken : memLoad cp mem = UInt256.ofNat c.token.val :=
    hw.load_word ⟨0, by simp [CollateralData.words]⟩ (by simp)
  have hlltv : memLoad (cp + UInt256.ofNat 32) mem = c.lltv :=
    hw.load_offset ⟨1, by simp [CollateralData.words]⟩ rfl
  have htokMask : UInt256.land (UInt256.ofNat c.token.val) solcAddrMask =
      UInt256.ofNat c.token.val := solcAddrMask_clean (addressWord_val_canonical c.token)
  have hprevMask : UInt256.land (UInt256.ofNat previous.val) solcAddrMask =
      UInt256.ofNat previous.val := solcAddrMask_clean (addressWord_val_canonical previous)
  have htokNat := ulit_toNat' c.token.val (lt_trans c.token.isLt (by decide))
  have hprevNat := ulit_toNat' previous.val (lt_trans previous.isLt (by decide))
  have rd1 := midnightBlocks.midnight_block_20840_fallthrough (by omega) (by
    rw [hm.arrayPtr, hm.length, hlt]; rfl) rd
  have hf1 := memoryFundingAt (credit := credit) rd1 (by memory_fund hfund)
  simp only [midnightBlocks.midnight_block_20840_fallthrough_stack, hm.arrayPtr] at rd1 hf1
  have rd2 := midnightBlocks.midnight_block_20852 (by omega) (by jump_dest) rd1
  have hf2 := memoryFundingAt (credit := credit) rd2 (by memory_fund hf1)
  simp only [midnightBlocks.midnight_block_20852_stack, addressMask_computed] at rd2 hf2
  obtain ⟨aw3, k3, C3, hf3, rd3⟩ := midnightMemoryArrayIndex_memoryFunded (by simp only [List.length_cons]; omega)
    (by rw [hin]; exact hi64) himem (by jump_dest) hf2 rd2
  simp only [hin] at rd3 hf3
  by_cases horder : previous.val < c.token.val
  · have hgt : UInt256.gt (UInt256.ofNat c.token.val) (UInt256.ofNat previous.val) = ⟨1⟩ :=
      ugt_one (by rw [htokNat, hprevNat]; exact horder)
    have rd4 := midnightBlocks.midnight_block_20870_fallthrough (by
      simp only [List.length_cons]; omega) (by rw [hcp, htoken, htokMask, hprevMask, hgt]; rfl) rd3
    have hf4 := memoryFundingAt (credit := credit) rd4 (by memory_fund hf3)
    simp only [midnightBlocks.midnight_block_20870_fallthrough_stack, hcp, htoken, htokMask] at rd4 hf4
    have rd5 := midnightBlocks.midnight_block_20883 (by omega) (by jump_dest) rd4
    have hf5 := memoryFundingAt (credit := credit) rd5 (by memory_fund hf4)
    simp only [midnightBlocks.midnight_block_20883_stack, hm.arrayPtr] at rd5 hf5
    obtain ⟨aw6, k6, C6, hf6, rd6⟩ := midnightMemoryArrayIndex_memoryFunded (by simp only [List.length_cons]; omega)
      (by rw [hin]; exact hi64) himem (by jump_dest) hf5 rd5
    simp only [hin] at rd6 hf6
    let mem1 := twoWordHashMem c.lltv (UInt256.ofNat 7) mem
    have hh7 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem c.lltv (UInt256.ofNat 7) mem) = solcMappingSlot ⟨7⟩ c.lltv :=
      twoWordHashMem_mapSlot_of_ge64 c.lltv (UInt256.ofNat 7) hmem
    by_cases hen : collateralEnabledWord evm false c.lltv = ⟨0⟩
    · left
      refine ⟨fun hs ↦ hs.2.1 hen, ?_⟩
      obtain ⟨aw7, k7, C7, rd7⟩ := midnightBlocks.midnight_block_20895_taken_packed (by
        simp only [List.length_cons]; omega) (by
          simp only [hcp, hlltv, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
            show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh7]
          change UInt256.isZero (collateralEnabledWord evm false c.lltv) ≠ ⟨0⟩
          rw [hen]; decide) (by jump_dest) rd6
      exact midnightBlocks.midnight_block_21100 (by
        simp only [midnightBlocks.midnight_block_20895_taken_stack, List.length_cons]; omega) rd7
    · obtain ⟨aw7, k7, C7, hf7, rd7⟩ := midnight_block_20895_fallthrough_funded (by
        simp only [List.length_cons]; omega) (by
          simp only [hcp, hlltv, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
            show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh7]
          exact isZero_eq_zero_of_ne hen) hf6 rd6
      simp only [midnightBlocks.midnight_block_20895_fallthrough_stack,
        midnightBlocks.midnight_block_20895_fallthrough_memory, hcp, hlltv] at rd7 hf7
      change RD _ _ _ _ _ _ mem1 _ _ _ _ _ at rd7
      change MemoryFunding credit mem1 aw7 C7 at hf7
      have hm1 : MarketStored mem1 ptr arrayPtr root m :=
        hm.preserve (twoWordHashMem_prefix mem c.lltv (UInt256.ofNat 7) root.toNat)
      obtain ⟨cp1, hcp1, _, _, hw1⟩ := hm1.collaterals.get i hi
      rw [hc] at hw1
      have hcursor : memLoad (cp1 + UInt256.ofNat 64) mem1 = c.liquidationCursor :=
        hw1.load_offset ⟨2, by simp [CollateralData.words]⟩ rfl
      have rd8 := midnightBlocks.midnight_block_20920 (by omega) (by jump_dest) rd7
      have hf8 := memoryFundingAt (credit := credit) rd8 (by memory_fund hf7)
      simp only [midnightBlocks.midnight_block_20920_stack, hm1.arrayPtr] at rd8 hf8
      obtain ⟨aw9, k9, C9, hf9, rd9⟩ := midnightMemoryArrayIndex_memoryFunded (by simp only [List.length_cons]; omega)
        (by rw [hin]; exact hi64) (by rw [hm1.length, hin, hlen]; exact hi) (by jump_dest) hf8 rd8
      simp only [hin] at rd9 hf9
      let mem2 := twoWordHashMem c.liquidationCursor (UInt256.ofNat 8) mem1
      have hmem1 : 64 ≤ mem1.size := hmem.trans (twoWordHashMem_prefix mem c.lltv _ root.toNat).size
      have hh8 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
          (twoWordHashMem c.liquidationCursor (UInt256.ofNat 8) mem1) =
          solcMappingSlot ⟨8⟩ c.liquidationCursor :=
        twoWordHashMem_mapSlot_of_ge64 c.liquidationCursor (UInt256.ofNat 8) hmem1
      by_cases hen2 : collateralEnabledWord evm true c.liquidationCursor = ⟨0⟩
      · left
        refine ⟨fun hs ↦ hs.2.2.1 hen2, ?_⟩
        obtain ⟨aw10, k10, C10, rd10⟩ := midnightBlocks.midnight_block_20932_taken_packed (by
          simp only [List.length_cons]; omega) (by
            simp only [hcp1, hcursor, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
              show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh8]
            change UInt256.isZero (collateralEnabledWord evm true c.liquidationCursor) ≠ ⟨0⟩
            rw [hen2]; decide) (by jump_dest) rd9
        exact midnightBlocks.midnight_block_21085 (by
          simp only [midnightBlocks.midnight_block_20932_taken_stack, List.length_cons]; omega) rd10
      · obtain ⟨aw10, k10, C10, hf10, rd10⟩ := midnight_block_20932_fallthrough_funded (by
          simp only [List.length_cons]; omega) (by
            simp only [hcp1, hcursor, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
              show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh8]
            exact isZero_eq_zero_of_ne hen2) hf9 rd9
        simp only [midnightBlocks.midnight_block_20932_fallthrough_stack,
          midnightBlocks.midnight_block_20932_fallthrough_memory, hcp1, hcursor] at rd10 hf10
        change RD _ _ _ _ _ _ mem2 _ _ _ _ _ at rd10
        change MemoryFunding credit mem2 aw10 C10 at hf10
        rcases midnightCollateralLif_mono (by simp only [List.length_cons]; omega) rd10 with
          ⟨hbad, hr⟩ | ⟨hs, k11, C11, hc11, rd11⟩
        · exact Or.inl ⟨fun h ↦ hbad h.2.2.2, hr⟩
        · have rd12 := midnightBlocks.midnight_block_21008 (by omega) (by jump_dest) rd11
          have hinc : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) := by
            apply u256_inj
            simp only [uadd_toNat, ofNat_toNat_mod, Nat.mod_add_mod, Nat.add_mod_mod]
          refine Or.inr ⟨⟨horder, hen, hen2, hs⟩, aw10, k11 + 7, C11 + 26, hf10.mono (by omega), ?_⟩
          simpa only [midnightBlocks.midnight_block_21008_stack, hinc] using rd12
  · left
    refine ⟨fun hs ↦ horder hs.1, ?_⟩
    have hgt : UInt256.gt (UInt256.ofNat c.token.val) (UInt256.ofNat previous.val) = ⟨0⟩ :=
      ugt_zero (by rw [htokNat, hprevNat]; exact Nat.le_of_not_gt horder)
    have rd4 := midnightBlocks.midnight_block_20870_taken (by
      simp only [List.length_cons]; omega) (by
        rw [hcp, htoken, htokMask, hprevMask, hgt]; decide) (by jump_dest) rd3
    exact midnightBlocks.midnight_block_21115 (by
      simp only [midnightBlocks.midnight_block_20870_taken_stack, List.length_cons]; omega) rd4


end Benchmarks.Midnight
