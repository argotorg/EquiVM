import Benchmarks.Midnight.ClaimFeeTraceSteps
import Benchmarks.Midnight.ClaimFeeStatic
import Benchmarks.Midnight.ClaimFeeSource
import Benchmarks.Midnight.AddressDecode

variable {fork : Ethereum.Fork}

/-! Matching checked arithmetic and static rejection before the claim's token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightClaimFeeArithmetic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {evm origin : EVM.State} {m : MarketData} {mem rdata : ByteArray}
    {aw root amount market receiver : UInt256} {credit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hstack : R.length + 18 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = root) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨15580⟩
      ([solcMappingSlot ⟨1⟩ m.id, m.id, receiver, amount, market] ++ R)
      mem aw rdata evm.accountMap k C) :
    (RDrev fork midnightBytecode g s0 ∧
      ExecBlock fork config (claimFeeAliasFrame origin m amount receiver) evm
        (claimContinuousFeeTransition.body.drop 6) .reverted) ∨
    (RDstatic fork midnightBytecode g s0 ∧
      ExecBlock fork config (claimFeeAliasFrame origin m amount receiver) evm
        (claimContinuousFeeTransition.body.drop 6) .staticViolation) ∨
    (ClaimFeeArithmeticSafe evm m.id amount ∧ I.perm = true ∧
      ∃ aw' k' C', TransferBudget root credit (writeWord mem root.toNat amount) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨23236⟩
          ([UInt256.land (memLoad (market + ⟨64⟩) (writeWord mem root.toNat amount)) solcAddrMask,
            receiver, amount, ⟨15786⟩] ++ R)
          (writeWord mem root.toNat amount) aw' rdata
          (claimFeeFinalState evm m.id amount).accountMap k' C') := by
  change RD fork _ _ _ _ _ (_ :: _ :: _ :: _ :: _ :: R) _ _ _ _ _ _ at rd
  have rd1 := midnightBlocks.midnight_block_15580 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_15580_stack, addressMask_computed] at rd1
  have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (hb.mono (by omega))
  have hg := claimFeeAlias_get origin m amount receiver
  by_cases hamount : amount.toNat < 2^128
  · obtain ⟨_, _, hc2, rd2⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) hamount (by jump_dest) rd1
    obtain ⟨_, _, hb3, rd3⟩ := midnightClaimFeeReadCredit henv
      (by simp only [List.length_cons]; omega) (hb1.mono hc2) rd2
    by_cases hc : amount.toNat ≤ (marketBalanceWord evm m.id 2).toNat
    · obtain ⟨_, _, hc4, rd4⟩ := midnightCheckedSub128_mono
        (by simp only [List.length_cons]; omega) (marketBalanceWord_lt evm m.id 2)
        hamount hc (by jump_dest) rd3
      by_cases hperm : I.perm = true
      · have hp : evm.executionEnv.perm = true := by rw [henv]; exact hperm
        obtain ⟨_, _, hb5, rd5⟩ := midnightClaimFeeWriteCredit henv
          (by simp only [List.length_cons]; omega) hperm (hb3.mono hc4) rd4
        have rd6 := midnightBlocks.midnight_block_15658
          (by simp only [List.length_cons]; omega) (by jump_dest) rd5
        simp only [midnightBlocks.midnight_block_15658_stack, uint128Mask_computed] at rd6
        have hb6 := transferBudgetAt (root := root) (credit := credit) rd6 (hb5.mono (by omega))
        obtain ⟨_, _, hc7, rd7⟩ := midnightToUint128_mono
          (by simp only [List.length_cons]; omega) hamount (by jump_dest) rd6
        obtain ⟨_, _, hc8, rd8⟩ := midnightClaimFeeReadLow 0 (by decide)
          (by simpa only [claimFeeCreditState_env] using henv)
          (by simp only [List.length_cons]; omega) rd7
        have hb8 := (hb6.mono hc7).mono hc8
        by_cases hu : amount.toNat ≤ (marketBalanceWord (claimFeeCreditState evm m.id amount) m.id 0).toNat
        · obtain ⟨_, _, hc9, rd9⟩ := midnightCheckedSub128_mono
            (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ m.id 0)
            hamount hu (by jump_dest) rd8
          obtain ⟨_, _, hb10, rd10⟩ := midnightClaimFeeWriteUnits henv (by omega)
            hperm (hb8.mono hc9) rd9
          simp only [List.cons_append, List.nil_append] at rd10
          obtain ⟨_, _, hc11, rd11⟩ := midnightToUint128_mono
            (by simp only [List.length_cons]; omega)
            hamount (by jump_dest) rd10
          obtain ⟨_, _, hc12, rd12⟩ := midnightClaimFeeReadLow 1 (by decide)
            (by simpa only [claimFeeUnitsState_env] using henv)
            (by simp only [List.length_cons]; omega) rd11
          have hb12 := (hb10.mono hc11).mono hc12
          by_cases hw : amount.toNat ≤ (marketBalanceWord (claimFeeUnitsState evm m.id amount) m.id 1).toNat
          · obtain ⟨_, _, hc13, rd13⟩ := midnightCheckedSub128_mono
              (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ m.id 1)
              hamount hw (by jump_dest) rd12
            exact Or.inr (Or.inr ⟨⟨hamount, hc, hu, hw⟩, hperm,
              midnightClaimFeeWriteWithdrawable henv (by omega) hperm hfree (hb12.mono hc13) rd13⟩)
          · refine Or.inl ⟨midnightCheckedSub128Revert
              (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ m.id 1)
              hamount (Nat.lt_of_not_ge hw) rd12, ?_⟩
            apply claimFeeCreditSource hamount hc hp
            apply claimFeeUnitsSource hamount hu hp
            have hg2 := claimFeeUnits_get origin m amount receiver
            exact claimFeeSubtractUnderflow 1 "__c3" (by decide) hg2.1 hg2.2.1 hg2.2.2
              hamount (Nat.lt_of_not_ge hw) (claimContinuousFeeTransition.body.drop 12)
        · refine Or.inl ⟨midnightCheckedSub128Revert
            (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ m.id 0)
            hamount (Nat.lt_of_not_ge hu) rd8, ?_⟩
          apply claimFeeCreditSource hamount hc hp
          have hg1 := claimFeeCredit_get origin m amount receiver
          exact claimFeeSubtractUnderflow 0 "__c2" (by decide) hg1.1 hg1.2.1 hg1.2.2
            hamount (Nat.lt_of_not_ge hu) (claimContinuousFeeTransition.body.drop 10)
      · have hp : I.perm = false := Bool.eq_false_iff.mpr hperm
        refine Or.inr (Or.inl ⟨midnightClaimFeeStatic
          (by simp only [List.length_cons]; omega) hp rd4, ?_⟩)
        exact claimFeeSubtractStatic 2 "__c1" (by decide) hg.1 hg.2.1 hg.2.2 hamount hc
          (by rw [henv]; exact hp) (claimContinuousFeeTransition.body.drop 8)
    · refine Or.inl ⟨midnightCheckedSub128Revert
        (by simp only [List.length_cons]; omega) (marketBalanceWord_lt evm m.id 2)
        hamount (Nat.lt_of_not_ge hc) rd3, ?_⟩
      exact claimFeeSubtractUnderflow 2 "__c1" (by decide) hg.1 hg.2.1 hg.2.2
        hamount (Nat.lt_of_not_ge hc) (claimContinuousFeeTransition.body.drop 8)
  · refine Or.inl ⟨midnightToUint128Revert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hamount) rd1, ?_⟩
    apply ExecBlock.consRevert
    apply callToUint128Revert hg.1 _ (Nat.le_of_not_gt hamount)
    simp only [evalExprs?, evalWordLocal hg.2.1, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
