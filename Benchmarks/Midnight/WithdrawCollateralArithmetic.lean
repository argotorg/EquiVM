import Benchmarks.Midnight.CheckedSubGas
import Benchmarks.Midnight.SupplyCollateralArithmetic

variable {fork : Ethereum.Fork}

/-! Checked subtraction and the packed collateral-balance write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem withdrawCollateralArithmetic {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw old index id user assets ret : UInt256}
    {k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 12 ≤ 1024) (hi : index.toNat < 128)
    (hold : old.toNat < 2^128) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨19447⟩
      ([old, assets, UInt256.ofNat 4573, ret, positionSlot id user + UInt256.ofNat 3, index] ++ R)
      mem aw rdata evm.accountMap k C) :
    (old.toNat < assets.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (assets.toNat ≤ old.toNat ∧ I.perm = false ∧ RDstatic fork midnightBytecode g s0) ∨
    (assets.toNat ≤ old.toNat ∧ I.perm = true ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ret (UInt256.sub old assets :: index :: R) mem aw rdata
        (collateralWriteState evm id user index (UInt256.sub old assets)).accountMap k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  by_cases hle : assets.toNat ≤ old.toNat
  · have hvalue : (UInt256.sub old assets).toNat < 2^128 := by
      rw [usub_toNat hle]; omega
    obtain ⟨k1, C1, hc1, rd1⟩ := midnightCheckedSub_mono
      (by simp only [List.length_cons]; omega) hle (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_4573
      (by omega) (by jump_dest) rd1
    obtain ⟨k3, C3, hc3, rd3⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) hvalue (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_4587
      (by simp only [List.length_cons]; omega) (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_4587_stack] at rd4
    obtain ⟨k5, C5, hc5, rd5⟩ := midnightUint128ArrayLocation_mono
      (by simp only [List.length_cons]; omega) hi (by jump_dest) rd4
    by_cases hp : I.perm = true
    · obtain ⟨k6, C6, hc6, rd6⟩ := collateral_block_4593_mono
        (by simp only [List.length_cons]; omega) hp hret rd5
      simp only [midnightBlocks.midnight_block_4593_stack, uint128Mask_computed,
        (uint128ArrayIndexFacts index hi).2.2] at rd6
      have hac : (collateralWriteState evm id user index (UInt256.sub old assets)).accountMap =
          sstoreAccountMap I.codeOwner evm.accountMap (collateralLoc id user index).slot
            (collateralWriteWord (solcSlotWordAt (collateralLoc id user index).slot
              evm.accountMap I) index (UInt256.sub old assets)) := by
        rw [collateralWriteState, storageStore_accountMap,
          storageLoad_codeOwner_eq_solcSlotWordAt evm I _
            (congrArg ExecutionEnv.codeOwner henv), henv]
      refine Or.inr (Or.inr ⟨hle, hp, k6, C6, by omega, ?_⟩)
      rw [hac]
      exact rd6
    · have hf : I.perm = false := Bool.eq_false_iff.mpr hp
      exact Or.inr (Or.inl ⟨hle, hf, collateral_block_4593_static
        (by simp only [List.length_cons]; omega) hf rd5⟩)
  · exact Or.inl ⟨by omega, midnightCheckedSubRevert
      (by simp only [List.length_cons]; omega) (by omega) rd⟩

end Benchmarks.Midnight
