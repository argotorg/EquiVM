import Benchmarks.Midnight.PositionUpdateSource
import Benchmarks.Midnight.PositionUpdateViewBudget
import Benchmarks.Midnight.PositionUpdateFeeBudget
import Benchmarks.Midnight.PositionUpdateDecreaseBudget
import Benchmarks.Midnight.PositionUpdateWritesBudget
import Benchmarks.Midnight.PositionUpdateMemory

/-! The complete position update with retained transfer funding and source execution. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionUpdateInternal_budget {evm : EVM.State} {g : Sat256} {s0 : State}
    {imms : Store} {m : MarketData} {mem rdata : ByteArray} {aw root ptr id user ret : UInt256}
    {budgetRoot : UInt256} {gasCredit : Nat}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 27 ≤ 1024)
    (hcanon : user.toNat < EVM.addressModulus)
    (hlo : 64 ≤ (ptr + UInt256.ofNat 128).toNat)
    (hhi : (ptr + UInt256.ofNat 128).toNat + 32 ≤ mem.size)
    (hmaturity : memLoad (ptr + UInt256.ofNat 128) mem = m.maturity)
    (hrootlo : 96 ≤ root.toNat) (hroot : root.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hb : TransferBudget budgetRoot gasCredit mem aw C)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨23599⟩ (ptr :: id :: user :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    let credit := positionNewCredit evm m id user
    let pending := positionNewPending evm m id user
    let fee := positionViewFee evm m id user
    (RDrev midnightBytecode g s0 ∧
      ExecFuncBody config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body .reverted) ∨
    (RDstatic midnightBytecode g s0 ∧
      ExecFuncBody config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body .staticViolation) ∨
    (evm.executionEnv.perm = true ∧
      credit.toNat < 2^128 ∧ pending.toNat < 2^128 ∧ fee.toNat < 2^128 ∧
      ExecFuncBody config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body
        (.returned (positionUpdateFinalFrame evm imms m id user) (positionUpdateFinalState evm m id user)
          (some [.int credit.toNat, .int pending.toNat, .int fee.toNat])) ∧
      ∃ aw' k' C',
        TransferBudget budgetRoot gasCredit
          (positionUpdateLogMemory mem root evm m id user) aw' C' ∧
        RD midnightBytecode evm.executionEnv g s0 ret (fee :: pending :: credit :: R)
        (positionUpdateLogMemory mem root evm m id user) aw' rdata
        (positionUpdateFinalState evm m id user).accountMap k' C') := by
  let credit := positionNewCredit evm m id user
  let pending := positionNewPending evm m id user
  let fee := positionViewFee evm m id user
  have hmem : 96 ≤ mem.size := by omega
  have hscratch : 96 ≤ (positionUpdateScratch mem evm id user).size := by
    rw [positionUpdateScratch_size _ _ _ _ (by omega)]; exact hmem
  have hv := midnightPositionUpdateView_budget hstack hcanon hlo hhi hmaturity hb rd
  change (¬ PositionViewSourceSafe evm m id user ∧ RDrev midnightBytecode g s0) ∨
    (PositionViewSourceSafe evm m id user ∧ ∃ aw' k' C',
      TransferBudget budgetRoot gasCredit (positionUpdateScratch mem evm id user) aw' C' ∧
      RD midnightBytecode evm.executionEnv g s0 ⟨23680⟩
        ([fee, pending, credit, updatePositionTopic, id, positionSlot id user,
          solcAddrMask, ret, ⟨96⟩, user] ++ R)
        (positionUpdateScratch mem evm id user) aw' rdata evm.accountMap k' C') at hv
  rcases hv with ⟨hbad, hr⟩ | ⟨hsafe, aw1, k1, C1, hb1, rd1⟩
  · exact Or.inl ⟨hr, positionUpdateViewReverts evm imms m id user hcanon hbad⟩
  · have hc128 : credit.toNat < 2^128 := positionNewCredit_lt hsafe
    have hp128 : pending.toNat < 2^128 := positionNewPending_lt hsafe
    have hf128 : fee.toNat < 2^128 := positionAccruedFee_lt ..
    have hd := midnightPositionUpdateDecrease_budget (by omega) hc128 hp128 hb1 rd1
    change (¬ (credit.toNat ≤ (positionFieldWord evm id user 0).toNat ∧
        pending.toNat ≤ (positionFieldWord evm id user 1).toNat) ∧ RDrev midnightBytecode g s0) ∨
      (credit.toNat ≤ (positionFieldWord evm id user 0).toNat ∧
        pending.toNat ≤ (positionFieldWord evm id user 1).toNat ∧ ∃ k' C',
        TransferBudget budgetRoot gasCredit (positionUpdateScratch mem evm id user) aw1 C' ∧
        RD midnightBytecode evm.executionEnv g s0 ⟨23723⟩
          ([positionPendingDecrease evm m id user, ⟨23855⟩, positionSlot id user, user, solcAddrMask,
            ⟨96⟩, updatePositionTopic, id, positionCreditDecrease evm m id user, credit, ret, fee, pending] ++ R)
          (positionUpdateScratch mem evm id user) aw1 rdata evm.accountMap k' C') at hd
    rcases hd with ⟨hbad, hr⟩ | ⟨hc, hp, k2, C2, hb2, rd2⟩
    · exact Or.inl ⟨hr, positionUpdateDecreaseReverts evm imms m id user hcanon hsafe hbad⟩
    · by_cases hperm : evm.executionEnv.perm = true
      · obtain ⟨aw3, k3, C3, hb3, rd3⟩ := midnightPositionUpdateWrites_budget
          (by omega) (by omega) hperm hb2 rd2
        have hs3 : 96 ≤ (twoWordHashMem id (UInt256.ofNat 1) (positionUpdateScratch mem evm id user)).size := by
          rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hscratch
        have hf3 : memLoad (UInt256.ofNat 64)
            (twoWordHashMem id (UInt256.ofNat 1) (positionUpdateScratch mem evm id user)) = root := by
          rw [memLoad_twoWordHashMem id (UInt256.ofNat 1) (UInt256.ofNat 64) (by decide) hscratch,
            positionUpdateScratch_load mem evm id user (UInt256.ofNat 64) (by decide) hmem, hfree]
        have hcd : (positionCreditDecrease evm m id user).toNat < 2^128 := by
          unfold positionCreditDecrease
          rw [usub_toNat hc]
          have h := positionFieldWord_lt evm id user 0
          omega
        have hpd : (positionPendingDecrease evm m id user).toNat < 2^128 := by
          unfold positionPendingDecrease
          rw [usub_toNat hp]
          have h := positionFieldWord_lt evm id user 1
          omega
        have hfword : marketFeeCreditWord (positionUpdatedBalances evm m id user) id =
            UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
              (positionUpdateAccounts evm.accountMap evm.executionEnv id user credit pending)
              evm.executionEnv) (UInt256.ofNat 128) := by
          have hl := storageLoad_codeOwner_eq_solcSlotWordAt (positionUpdatedBalances evm m id user)
            evm.executionEnv (solcMappingSlot ⟨1⟩ id + ⟨1⟩) (by simp [positionUpdatedBalances])
          simpa only [marketFeeCreditWord, positionUpdatedBalances, positionUpdateState_accounts]
            using congrArg (fun w ↦ UInt256.shiftRight w (UInt256.ofNat 128)) hl
        rcases midnightPositionUpdateFee_budget (by omega) hs3 hperm hroot hf3 hf128 hcd hpd hret hb3 rd3 with
          ⟨hbad, hr⟩ | ⟨hsum, aw4, k4, C4, hb4, rd4⟩
        · rw [← hfword] at hbad
          exact Or.inl ⟨hr, positionUpdateSourceFeeReverts evm imms m id user hcanon hsafe hc hp hbad hperm⟩
        · have hsrcsum : (marketFeeCreditWord (positionUpdatedBalances evm m id user) id).toNat +
              fee.toNat < 2^128 := by rw [hfword]; exact hsum
          dsimp only [credit, pending, fee] at rd4
          rw [← positionUpdateFinalState_accounts evm m id user] at rd4
          exact Or.inr (Or.inr ⟨hperm, hc128, hp128, hf128,
            positionUpdateSourceReturns evm imms m id user hcanon hsafe hc hp hsrcsum hperm,
            _, _, _, hb4, rd4⟩)
      · have hpfalse : evm.executionEnv.perm = false := Bool.eq_false_iff.mpr hperm
        exact Or.inr (Or.inl ⟨midnightPositionUpdateStatic (by omega) hpfalse rd2,
          positionUpdateSourceStatic evm imms m id user hcanon hsafe hc hp hpfalse⟩)

end Benchmarks.Midnight
