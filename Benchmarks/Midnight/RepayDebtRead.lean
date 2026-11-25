import Benchmarks.Midnight.RepayBalanceStorage
import Benchmarks.Midnight.PositionUpdateMemory
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_039

variable {fork : Ethereum.Fork}

/-! Repayment's debt-slot read preserves the later transfer budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayReadDebt {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw amount x1 id x3 user budgetRoot : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD fork midnightBytecode ee g s0 ⟨9871⟩ (amount :: x1 :: id :: x3 :: user :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot credit (positionReadMemory mem id user) aw' C' ∧
      RD fork midnightBytecode ee g s0 ⟨19743⟩
        (low128 (solcSlotWordAt (positionSlot id user + ⟨2⟩) σ ee) :: amount ::
          UInt256.ofNat 9925 :: uint128Mask :: (positionSlot id user + ⟨2⟩) ::
          x1 :: id :: x3 :: user :: R)
        (positionReadMemory mem id user) aw' rdata σ k' C' := by
  have hvalid : (D_J midnightBytecode 0).contains (UInt256.ofNat 19743) = true := by jump_dest
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have hb4 := transferBudgetAt (root := budgetRoot) (credit := credit) r4
    (by transfer_budget hb)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have hb5 := transferBudgetAt (root := budgetRoot) (credit := credit) r5
    (by transfer_budget hb4)
  have r6 := r5.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have hb7 := transferBudgetAt (root := budgetRoot) (credit := credit) r7
    (by transfer_budget hb5)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have hb9 := transferBudgetAt (root := budgetRoot) (credit := credit) r9
    (by transfer_budget hb7)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have hb12 := transferBudgetAt (root := budgetRoot) (credit := credit) r12
    (by transfer_budget hb9)
  have r13 := RD.genKeccak256 r12 (by native_decide) (by evm_ov)
  have hb13 := transferBudgetAt (root := budgetRoot) (credit := credit) r13
    (by transfer_budget hb12)
  have r14 := r13.dup6 (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have hb16 := transferBudgetAt (root := budgetRoot) (credit := credit) r16
    (by transfer_budget hb13)
  have r17 := r16.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r18 := RD.genMstore r17 (by native_decide) (by evm_ov)
  have hb18 := transferBudgetAt (root := budgetRoot) (credit := credit) r18
    (by transfer_budget hb16)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r22 := r21.shl (by native_decide) (by evm_ov)
  have r23 := r22.sub (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 9925) (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := RD.genKeccak256 r27 (by native_decide) (by evm_ov)
  have hb28 := transferBudgetAt (root := budgetRoot) (credit := credit) r28
    (by transfer_budget hb18)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := r29.swap3 (by native_decide) (by evm_ov)
  have r31 := r30.dup3 (by native_decide) (by evm_ov)
  have r32 := r31.dup5 (by native_decide) (by evm_ov)
  have hb32 := transferBudgetAt (root := budgetRoot) (credit := credit) r32
    (hb28.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans
      ((Nat.le_add_right _ 3).trans (Nat.le_add_right _ 3)))))
  obtain ⟨_, _, hc33, r33⟩ := RD.sloadMono r32 (by native_decide) (by evm_ov)
  have r34 := r33.and (by native_decide) (by evm_ov)
  have r35 := r34.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r36 := r35.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r36 (by native_decide)
  have hbFinal := transferBudgetAt (root := budgetRoot) (credit := credit) rFinal
    (hb32.mono (by omega))
  have hz1 : memLoad (UInt256.ofNat 800) (wordAt0Mem id mem) = ⟨0⟩ := by
    change memLoad (UInt256.ofNat 800) (writeWord mem 0 id) = ⟨0⟩
    rw [memLoad_writeWord_preserved mem 0 (UInt256.ofNat 800) id
      hmem (Or.inr (by decide)), hz]
  have hz' : memLoad (UInt256.ofNat 800) (twoWordHashMem id ⟨0⟩ mem) = ⟨0⟩ := by
    rw [memLoad_twoWordHashMem _ _ _ (by decide) (by change 832 ≤ mem.size; exact hmem), hz]
  simp only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    uint128Mask_computed, hz1] at rFinal hbFinal
  rw [hz'] at rFinal hbFinal
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
      solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  rw [hh1] at rFinal hbFinal
  have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (positionReadMemory mem id user) =
      positionSlot id user := twoWordHashMem_mapSlot_of_ge64 _ _ (by
        rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega)
  change RD fork midnightBytecode ee g s0 ⟨19743⟩
    (low128 (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (positionReadMemory mem id user) + ⟨2⟩) σ ee) :: amount :: UInt256.ofNat 9925 ::
      uint128Mask :: (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (positionReadMemory mem id user) + ⟨2⟩) :: x1 :: id :: x3 :: user :: R)
    (positionReadMemory mem id user) _ rdata σ _ _ at rFinal
  rw [hh2] at rFinal
  exact ⟨_, _, _, hbFinal, rFinal⟩

end Benchmarks.Midnight
