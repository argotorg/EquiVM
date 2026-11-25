import Benchmarks.Midnight.RepayDebtWrite
import Benchmarks.Midnight.RepayWithdrawableRead
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.CheckedExtraGas

variable {fork : Ethereum.Fork}

/-! Repayment's checked balance phase, including arithmetic and static failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def repayBalanceMemory (mem : ByteArray) (id user : UInt256) : ByteArray :=
  twoWordHashMem id ⟨1⟩ (positionReadMemory mem id user)

theorem midnightRepayBalances {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root id user units dp dl market : UInt256} {callback : AccountAddress} {data : ByteArray}
    {credit k C : Nat} {R : List UInt256}
    (henv : evm.executionEnv = I) (hf : RepaySourceFrame frame m id user units callback data)
    (hcanon : user.toNat < EVM.addressModulus) (hstack : R.length + 16 ≤ 1024)
    (hmem : 832 ≤ mem.size) (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨9861⟩
      ([id, dp, dl, user, UInt256.ofNat callback.val, units, market] ++ R)
      mem aw rdata evm.accountMap k C) :
    (RDrev fork midnightBytecode g s0 ∧
      ExecBlock fork config frame evm (repayTransition.body.drop 5) .reverted) ∨
    (RDstatic fork midnightBytecode g s0 ∧
      ExecBlock fork config frame evm (repayTransition.body.drop 5) .staticViolation) ∨
    (I.perm = true ∧ RepayBalancesSafe evm id user units ∧ ∃ aw' k' C',
      TransferBudget root credit (repayBalanceMemory mem id user) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨9992⟩
        ([marketBalanceWord (repayDebtState evm id user units) id 1 + units,
          uint128Mask, solcMappingSlot ⟨1⟩ id + ⟨1⟩, dp, id, dl, user,
          UInt256.ofNat callback.val, units, market] ++ R)
        (repayBalanceMemory mem id user) aw' rdata
        (repayDebtState evm id user units).accountMap k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_9861
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_9861_stack] at rd1
  by_cases h128 : units.toNat < 2^128
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd1
    obtain ⟨aw3, k3, C3, hb3, rd3⟩ := midnightRepayReadDebt
      (by simp only [List.length_cons]; omega) hmem hz (hb.mono (by omega)) rd2
    have hw : low128 (healthPositionWord evm id user) =
        low128 (solcSlotWordAt (positionSlot id user + ⟨2⟩) evm.accountMap I) := by
      rw [healthPositionWord, storageLoad_codeOwner_eq_solcSlotWordAt evm I _
        (congrArg ExecutionEnv.codeOwner henv)]
    rw [← hw] at rd3
    have hf1 := hf.insert "__c1" (.int units.toNat) (by decide)
    by_cases hle : units.toNat ≤ (low128 (healthPositionWord evm id user)).toNat
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedSub128_mono
        (by simp only [List.length_cons]; omega) (low128_lt _) h128 hle (by jump_dest) rd3
      rcases midnightRepayWriteDebt (by simp only [List.length_cons]; omega) rd4 with
        ⟨hp, hs⟩ | ⟨hp, k5, C5, hc5, rd5⟩
      · exact Or.inr (Or.inl ⟨hs, repayDebtStatic hf hcanon h128 hle (by rw [henv]; exact hp)⟩)
      · have hstore : storeLow128Accounts evm.accountMap I (positionSlot id user + ⟨2⟩)
            (UInt256.sub (low128 (healthPositionWord evm id user)) units) =
            (repayDebtState evm id user units).accountMap := by
          rw [repayDebtState, storeLow128_accounts, henv]
        rw [hstore] at rd5
        obtain ⟨k6, C6, hc6, rd6⟩ := midnightToUint128_mono
          (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd5
        have hs3 : (positionReadMemory mem id user).size = mem.size :=
          positionReadMemory_size mem id user (by omega)
        have hz3 : memLoad (UInt256.ofNat 800) (positionReadMemory mem id user) = ⟨0⟩ := by
          rw [positionReadMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 800) (by decide)
            (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hmem),
            memLoad_twoWordHashMem id ⟨0⟩ (UInt256.ofNat 800) (by decide) hmem, hz]
        obtain ⟨aw7, k7, C7, hb7, rd7⟩ := midnightRepayReadWithdrawable
          (by simp only [List.length_cons]; omega) (by rw [hs3]; exact hmem) hz3
          (hb3.mono (by omega)) rd6
        have hw' : marketBalanceWord (repayDebtState evm id user units) id 1 =
            low128 (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
              (repayDebtState evm id user units).accountMap I) := by
          change low128 (Stele.EVM.storageLoad _ _ _) = _
          rw [storageLoad_codeOwner_eq_solcSlotWordAt _ I _
            (congrArg ExecutionEnv.codeOwner ((repayDebtState_env ..).trans henv))]
          rfl
        rw [← hw'] at rd7
        by_cases hsum : (marketBalanceWord (repayDebtState evm id user units) id 1).toNat +
            units.toNat < 2^128
        · obtain ⟨k8, C8, hc8, rd8⟩ := midnightCheckedAdd128_mono
            (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ id 1)
            h128 hsum (by jump_dest) rd7
          exact Or.inr (Or.inr ⟨hp, ⟨h128, hle, hsum⟩, aw7, k8, C8, hb7.mono hc8, rd8⟩)
        · refine Or.inl ⟨midnightCheckedAdd128Revert
            (by simp only [List.length_cons]; omega) (marketBalanceWord_lt _ id 1)
            h128 (Nat.le_of_not_lt hsum) rd7, ?_⟩
          apply repayDebtSource hf hcanon h128 hle (by rw [henv]; exact hp)
          exact repayWithdrawableOverflow hf1 h128 (Nat.le_of_not_lt hsum)
    · refine Or.inl ⟨midnightCheckedSub128Revert
        (by simp only [List.length_cons]; omega) (low128_lt _) h128 (Nat.lt_of_not_ge hle) rd3, ?_⟩
      exact withdrawUnitsSubtractUnderflow hf.contract hf.units
        (evalRepayDebt hf1.contract hf1.position hf1.idValue hf1.userValue hcanon)
        h128 (Nat.lt_of_not_ge hle) (repayTransition.body.drop 7)
  · refine Or.inl ⟨midnightToUint128Revert (by simp only [List.length_cons]; omega)
      (Nat.le_of_not_lt h128) rd1, ?_⟩
    apply ExecBlock.consRevert
    apply callToUint128Revert hf.contract _ (Nat.le_of_not_lt h128)
    simp only [evalExprs?, evalWordLocal hf.units, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
