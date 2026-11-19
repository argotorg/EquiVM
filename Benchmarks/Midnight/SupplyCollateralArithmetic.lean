import Benchmarks.Midnight.CheckedAddGas
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.ArrayIndexGas
import Benchmarks.Midnight.CollateralPackedStore
import Benchmarks.Midnight.CollateralBlocksStatic
import Benchmarks.Midnight.RuntimeBlocks_019

/-! Checked addition and the packed collateral-balance write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyCollateralArithmetic {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw unused0 unused1 old index id user token assets : UInt256}
    {k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 20 ≤ 1024) (hi : index.toNat < 128)
    (rd : RD midnightBytecode I g s0 ⟨17124⟩
      ([unused0, unused1, old, index, id, user, token, assets,
        positionSlot id user + UInt256.ofNat 3] ++ R) mem aw rdata evm.accountMap k C) :
    (¬ old.toNat + assets.toNat < 2^128 ∧ RDrev midnightBytecode g s0) ∨
    (old.toNat + assets.toNat < 2^128 ∧ I.perm = false ∧ RDstatic midnightBytecode g s0) ∨
    (old.toNat + assets.toNat < 2^128 ∧ I.perm = true ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨17152⟩
        ([id, token, user, token, assets, UInt256.ofNat 15786] ++ R) mem aw rdata
        (collateralWriteState evm id user index (old + assets)).accountMap k' C') := by
  have rd1 := midnightBlocks.midnight_block_17124 (R := R) (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_17124_stack] at rd1
  by_cases h256 : old.toNat + assets.toNat < UInt256.size
  · have hsum : (old + assets).toNat = old.toNat + assets.toNat := addWord_toNat _ _ h256
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedAdd_mono
      (by simp only [List.length_cons]; omega) h256 (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_4204
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    by_cases h128 : old.toNat + assets.toNat < 2^128
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightToUint128_mono
        (by simp only [List.length_cons]; omega) (by rw [hsum]; exact h128)
        (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_4587
        (by simp only [List.length_cons]; omega) (by jump_dest) rd4
      simp only [midnightBlocks.midnight_block_4587_stack] at rd5
      obtain ⟨k6, C6, hc6, rd6⟩ := midnightUint128ArrayLocation_mono
        (by simp only [List.length_cons]; omega) hi (by jump_dest) rd5
      by_cases hp : I.perm = true
      · obtain ⟨k7, C7, hc7, rd7⟩ := collateral_block_4593_mono
          (by simp only [List.length_cons]; omega) hp (by jump_dest) rd6
        simp only [midnightBlocks.midnight_block_4593_stack, uint128Mask_computed,
          (uint128ArrayIndexFacts index hi).2.2] at rd7
        have hac : (collateralWriteState evm id user index (old + assets)).accountMap =
            sstoreAccountMap I.codeOwner evm.accountMap (collateralLoc id user index).slot
              (collateralWriteWord (solcSlotWordAt (collateralLoc id user index).slot
                evm.accountMap I) index (old + assets)) := by
          rw [collateralWriteState, storageStore_accountMap,
            storageLoad_codeOwner_eq_solcSlotWordAt evm I _
              (congrArg ExecutionEnv.codeOwner henv), henv]
        refine Or.inr (Or.inr ⟨h128, hp, k7, C7, by omega, ?_⟩)
        rw [hac]
        exact rd7
      · have hf : I.perm = false := Bool.eq_false_iff.mpr hp
        exact Or.inr (Or.inl ⟨h128, hf, collateral_block_4593_static
          (by simp only [List.length_cons]; omega) hf rd6⟩)
    · exact Or.inl ⟨h128, midnightToUint128Revert
        (by simp only [List.length_cons]; omega) (by rw [hsum]; omega) rd3⟩
  · refine Or.inl ⟨?_, midnightCheckedAddRevert
      (by simp only [List.length_cons]; omega) (by omega) rd1⟩
    change ¬ old.toNat + assets.toNat < 2^256 at h256
    omega

end Benchmarks.Midnight
