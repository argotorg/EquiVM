import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.ArrayIndexGas
import Benchmarks.Midnight.PositionUpdateMemory
import Benchmarks.Midnight.CollateralStorage
import Benchmarks.Midnight.AddressDecode

/-! Bounds checks, token lookup, and the initial packed collateral read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightSupplyCollateralRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw market array limit root id user index assets : UInt256}
    {m : MarketData} {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hmem : 96 ≤ mem.size)
    (hm : MarketStored mem market array limit m)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨17031⟩
      ([id, ⟨96⟩, user, index, assets, market] ++ R) mem aw rdata σ k C) :
    ((¬ index.toNat < m.collaterals.length ∨ ¬ index.toNat < 128) ∧
      RDrev midnightBytecode g s0) ∨
    (∃ hi : index.toNat < m.collaterals.length, index.toNat < 128 ∧
      ∃ check aw' k' C',
        TransferBudget root credit (positionReadMemory mem id user) aw' C' ∧
        (check ≠ ⟨0⟩ ↔ collateralWord (fun slot ↦ solcSlotWordAt slot σ I) id user index = ⟨0⟩ ∧
          assets ≠ ⟨0⟩) ∧
        RD midnightBytecode I g s0 ⟨17119⟩
          ([check, market + UInt256.ofNat 96, positionSlot id user,
            collateralWord (fun slot ↦ solcSlotWordAt slot σ I) id user index,
            index, id, user, UInt256.ofNat m.collaterals[index.toNat].token.val,
            assets, positionSlot id user + UInt256.ofNat 3] ++ R)
          (positionReadMemory mem id user) aw' rdata σ k' C') := by
  change RD midnightBytecode I g s0 ⟨17031⟩
    (id :: UInt256.ofNat 96 :: user :: index :: assets :: market :: R) mem aw rdata σ k C at rd
  have rd1 := midnightBlocks.midnight_block_17031 (R := R)
    (by omega) (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
  simp only [midnightBlocks.midnight_block_17031_stack, hm.arrayPtr, addressMask_computed] at rd1
  have hlen : (memLoad array mem).toNat = m.collaterals.length := by
    rw [hm.length, UInt256.toNat_ofNat_of_lt (by
      have := hm.collateralCount; change _ < 2^256; omega)]
  by_cases hi : index.toNat < m.collaterals.length
  · have hi64 : index.toNat < 2^64 := hi.trans hm.collateralCount
    obtain ⟨aw2, k2, C2, hb2, rd2⟩ := midnightMemoryArrayIndex_funded
      (by simp only [List.length_cons]; omega) hi64 (by rw [hlen]; exact hi)
      (by jump_dest) hb1 rd1
    obtain ⟨cp, hcp, hcplo, hcphi, hcw⟩ := hm.collaterals.get index.toNat hi
    have htoken : memLoad cp mem = UInt256.ofNat m.collaterals[index.toNat].token.val :=
      hcw.load_word ⟨0, by simp [CollateralData.words]⟩ (by simp)
    have rd3 := midnightBlocks.midnight_block_17053 (R := R)
      (by omega) (by jump_dest) rd2
    have hb3 := transferBudgetAt (root := root) (credit := credit) rd3 (by
      simp only [midnightBlocks.midnight_block_17053_memory]
      transfer_budget hb2)
    have hh0 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
        solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 id ⟨0⟩ (by omega)
    have hs0 : 64 ≤ (twoWordHashMem id ⟨0⟩ mem).size := by
      rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega
    have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem user (solcMappingSlot ⟨0⟩ id) (twoWordHashMem id ⟨0⟩ mem)) =
        positionSlot id user := twoWordHashMem_mapSlot_of_ge64 _ _ hs0
    simp only [midnightBlocks.midnight_block_17053_stack, midnightBlocks.midnight_block_17053_memory,
      hcp, htoken, addressWord_val_clean, uint128Mask_computed,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
      hh0, hh1] at rd3 hb3
    have hclean : UInt256.land (UInt256.ofNat m.collaterals[index.toNat].token.val) solcAddrMask =
        UInt256.ofNat m.collaterals[index.toNat].token.val := addressWord_val_clean _
    rw [hclean] at rd3
    by_cases hi128 : index.toNat < 128
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightUint128ArrayLocation_mono
        (by simp only [List.length_cons]; omega) hi128 (by jump_dest) rd3
      have hb4 := transferBudgetAt (root := root) (credit := credit) rd4 (hb3.mono hc4)
      let old := collateralWord (fun slot ↦ solcSlotWordAt slot σ I) id user index
      have ho : UInt256.land
          (UInt256.shiftRight (solcSlotWordAt (positionSlot id user + UInt256.ofNat 3 +
            UInt256.ofNat (index.toNat / 2)) σ I)
              (UInt256.shiftLeft (UInt256.ofNat (16 * (index.toNat % 2))) (UInt256.ofNat 3)))
          uint128Mask = old := by
        rw [(uint128ArrayIndexFacts index hi128).2.2]
        rfl
      dsimp only [solcSlotWordAt] at ho
      by_cases hz : old = ⟨0⟩
      · obtain ⟨k5, C5, hc5, rd5⟩ := collateral_block_17102_taken_mono
          (by simp only [List.length_cons]; omega)
          (by change UInt256.isZero _ ≠ _; rw [ho, hz]; decide) (by jump_dest) rd4
        have hb5 := transferBudgetAt (root := root) (credit := credit) rd5 (hb4.mono hc5)
        simp only [midnightBlocks.midnight_block_17102_taken_stack, ho] at rd5
        have rd6 := midnightBlocks.midnight_block_17536
          (by simp only [List.length_cons]; omega) (by jump_dest) rd5
        have hb6 := transferBudgetAt (root := root) (credit := credit) rd6 (by transfer_budget hb5)
        simp only [midnightBlocks.midnight_block_17536_stack] at rd6
        refine Or.inr ⟨hi, hi128, _, _, _, _, hb6, ?_, rd6⟩
        change UInt256.isZero (UInt256.isZero assets) ≠ ⟨0⟩ ↔ old = ⟨0⟩ ∧ assets ≠ ⟨0⟩
        by_cases ha : assets = ⟨0⟩
        · rw [ha, hz]; decide
        · rw [isZero_eq_zero_of_ne ha]
          simp only [hz, ha, and_self, ne_eq]
          decide
      · obtain ⟨k5, C5, hc5, rd5⟩ := collateral_block_17102_fallthrough_mono
          (by simp only [List.length_cons]; omega)
          (by change UInt256.isZero _ = _; rw [ho]; exact isZero_eq_zero_of_ne hz) rd4
        have hb5 := transferBudgetAt (root := root) (credit := credit) rd5 (hb4.mono hc5)
        simp only [midnightBlocks.midnight_block_17102_fallthrough_stack, ho] at rd5
        refine Or.inr ⟨hi, hi128, _, _, _, _, hb5, ?_, rd5⟩
        change UInt256.isZero old ≠ ⟨0⟩ ↔ old = ⟨0⟩ ∧ assets ≠ ⟨0⟩
        simp only [isZero_eq_zero_of_ne hz, hz, false_and, ne_self_iff_false]
    · exact Or.inl ⟨Or.inr hi128, midnightUint128ArrayLocationRevert
        (by simp only [List.length_cons]; omega) (by omega) rd3⟩
  · exact Or.inl ⟨Or.inl hi, midnightMemoryArrayIndexRevert
      (by simp only [List.length_cons]; omega) (by rw [hlen]; omega) rd1⟩

end Benchmarks.Midnight
