import Benchmarks.Midnight.WithdrawUnitsTraceSteps
import Benchmarks.Midnight.ClaimFeeTraceSteps

/-! Matching all checked balance reductions before withdrawal's final write and transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightWithdrawUnitsBalances {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root units id user decrease market : UInt256} {receiver : AccountAddress}
    {gasCredit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I)
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 24 ≤ 1024) (hb : TransferBudget root gasCredit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨23403⟩
      ([units, UInt256.ofNat 3993, UInt256.ofNat 4002, uint128Mask,
        positionSlot id user, solcMappingSlot ⟨1⟩ id, id, user, decrease,
        market, UInt256.ofNat 64, solcAddrMask, UInt256.ofNat receiver.val, units] ++ R)
      mem aw rdata evm.accountMap k C) :
    (RDrev midnightBytecode g s0 ∧
      ExecBlock config frame evm (withdrawTransition.body.drop 10) .reverted) ∨
    (WithdrawUnitsBalancesSafe evm id user units ∧ ∃ k' C',
      TransferBudget root gasCredit mem aw C' ∧
      RD midnightBytecode I g s0 ⟨4088⟩
        ([UInt256.sub (marketBalanceWord (withdrawUnitsWithdrawableState evm id user units) id 0)
            units, uint128Mask, solcMappingSlot ⟨1⟩ id, id, user, decrease,
          market, UInt256.ofNat 64, solcAddrMask, UInt256.ofNat receiver.val, units] ++ R)
        mem aw rdata (withdrawUnitsWithdrawableState evm id user units).accountMap k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  have hp : evm.executionEnv.perm = true := by rw [henv]; exact hperm
  have hf1 := hf.insert "__c4" (.int units.toNat) (by decide)
  have hf2 := hf1.insert "__c5" (.int units.toNat) (by decide)
  have hf3 := hf2.insert "__c6" (.int units.toNat) (by decide)
  by_cases h128 : units.toNat < 2^128
  · obtain ⟨k1, C1, hc1, rd1⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightWithdrawUnitsReadCredit henv
      (by simp only [List.length_cons]; omega) rd1
    by_cases hc : units.toNat ≤ (positionFieldWord evm id user 0).toNat
    · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedSub128_mono
        (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id user 0)
        h128 hc (by jump_dest) rd2
      obtain ⟨k4, C4, hc4, rd4⟩ := midnightWithdrawUnitsWriteCredit henv (by omega) hperm rd3
      have sourceCredit {result : ExecResult}
          (ht : ExecBlock config (withdrawUnitsCreditFrame frame units)
            (withdrawUnitsCreditState evm id user units) (withdrawTransition.body.drop 12) result) :
          ExecBlock config frame evm (withdrawTransition.body.drop 10) result :=
        withdrawUnitsSubtractSource hf.contract hf.units
          (evalPositionAliasField 0 hcanon hf1.position)
          (assignPositionAliasField 0 _ hcanon hf1.position)
          (positionFieldWord_lt evm id user 0) h128 hc hp ht
      simp only [List.cons_append, List.nil_append] at rd4
      obtain ⟨k5, C5, hc5, rd5⟩ := midnightToUint128_mono
        (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd4
      obtain ⟨k6, C6, hc6, rd6⟩ := midnightWithdrawUnitsReadWithdrawable
        ((withdrawUnitsCreditState_env ..).trans henv)
        (by simp only [List.length_cons]; omega) rd5
      by_cases hw : units.toNat ≤
          (marketBalanceWord (withdrawUnitsCreditState evm id user units) id 1).toNat
      · obtain ⟨k7, C7, hc7, rd7⟩ := midnightCheckedSub128_mono
          (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ id 1)
          h128 hw (by jump_dest) rd6
        obtain ⟨k8, C8, hc8, rd8⟩ := midnightWithdrawUnitsWriteWithdrawable henv
          (by omega) hperm rd7
        have sourceWithdrawable {result : ExecResult}
            (ht : ExecBlock config (withdrawUnitsWithdrawableFrame frame units)
              (withdrawUnitsWithdrawableState evm id user units)
              (withdrawTransition.body.drop 14) result) :
            ExecBlock config (withdrawUnitsCreditFrame frame units)
              (withdrawUnitsCreditState evm id user units)
              (withdrawTransition.body.drop 12) result :=
          withdrawUnitsSubtractSource hf1.contract hf1.units
            (evalMarketBalance 1 hf2.marketState) (assignMarketBalance 1 _ hf2.marketState)
            (marketBalanceWord_lt _ id 1) h128 hw (by simpa only [withdrawUnitsCreditState_env]
              using hp) ht
        simp only [List.cons_append, List.nil_append] at rd8
        obtain ⟨k9, C9, hc9, rd9⟩ := midnightToUint128_mono
          (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd8
        obtain ⟨k10, C10, hc10, rd10⟩ := midnightClaimFeeReadLow 0 (by decide)
          ((withdrawUnitsWithdrawableState_env ..).trans henv)
          (by simp only [List.length_cons]; omega) rd9
        by_cases hu : units.toNat ≤
            (marketBalanceWord (withdrawUnitsWithdrawableState evm id user units) id 0).toNat
        · obtain ⟨k11, C11, hc11, rd11⟩ := midnightCheckedSub128_mono
            (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ id 0)
            h128 hu (by jump_dest) rd10
          exact Or.inr ⟨⟨h128, hc, hw, hu⟩, k11, C11, hb.mono (by omega), rd11⟩
        · refine Or.inl ⟨midnightCheckedSub128Revert
            (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ id 0)
            h128 (Nat.lt_of_not_ge hu) rd10, ?_⟩
          apply sourceCredit
          apply sourceWithdrawable
          exact withdrawUnitsSubtractUnderflow hf2.contract hf2.units
            (evalMarketBalance 0 hf3.marketState) h128 (Nat.lt_of_not_ge hu)
            (withdrawTransition.body.drop 16)
      · refine Or.inl ⟨midnightCheckedSub128Revert
          (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ id 1)
          h128 (Nat.lt_of_not_ge hw) rd6, ?_⟩
        apply sourceCredit
        exact withdrawUnitsSubtractUnderflow hf1.contract hf1.units
          (evalMarketBalance 1 hf2.marketState) h128 (Nat.lt_of_not_ge hw)
          (withdrawTransition.body.drop 14)
    · refine Or.inl ⟨midnightCheckedSub128Revert
        (by simp only [List.length_cons]; omega) (positionFieldWord_lt evm id user 0)
        h128 (Nat.lt_of_not_ge hc) rd2, ?_⟩
      exact withdrawUnitsSubtractUnderflow hf.contract hf.units
        (evalPositionAliasField 0 hcanon hf1.position) h128 (Nat.lt_of_not_ge hc)
        (withdrawTransition.body.drop 12)
  · refine Or.inl ⟨midnightToUint128Revert (by simp only [List.length_cons]; omega)
      (Nat.le_of_not_lt h128) rd, ?_⟩
    apply ExecBlock.consRevert
    apply callToUint128Revert hf.contract _ (Nat.le_of_not_lt h128)
    simp only [evalExprs?, evalWordLocal hf.units, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
