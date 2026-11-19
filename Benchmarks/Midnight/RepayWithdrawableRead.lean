import Benchmarks.Midnight.RepayDebtRead

/-! The withdrawable read follows repayment's debt write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayReadWithdrawable {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw amount x1 id budgetRoot : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD midnightBytecode ee g s0 ⟨9950⟩ (amount :: x1 :: id :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot credit (twoWordHashMem id ⟨1⟩ mem) aw' C' ∧
      RD midnightBytecode ee g s0 ⟨20456⟩
        (low128 (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨1⟩) σ ee) :: amount ::
          UInt256.ofNat 9992 :: uint128Mask :: (solcMappingSlot ⟨1⟩ id + ⟨1⟩) :: x1 :: id :: R)
        (twoWordHashMem id ⟨1⟩ mem) aw' rdata σ k' C' := by
  have hvalid : (D_J midnightBytecode 0).contains (UInt256.ofNat 20456) = true := by jump_dest
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
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (by transfer_budget hb5)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 9992) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r18 := RD.genMload r17 (by native_decide) (by evm_ov)
  have hb18 := transferBudgetAt (root := budgetRoot) (credit := credit) r18
    (by transfer_budget hb8)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have hb19 := transferBudgetAt (root := budgetRoot) (credit := credit) r19
    (by transfer_budget hb18)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := r20.swap3 (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have r23 := r22.dup5 (by native_decide) (by evm_ov)
  have hb23 := transferBudgetAt (root := budgetRoot) (credit := credit) r23
    (hb19.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans
      ((Nat.le_add_right _ 3).trans (Nat.le_add_right _ 3)))))
  obtain ⟨_, _, hc24, r24⟩ := RD.sloadMono r23 (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r27 := r26.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20456)) r27 (by native_decide)
  have hbFinal := transferBudgetAt (root := budgetRoot) (credit := credit) rFinal
    (hb23.mono (by omega))
  have hz' : memLoad (UInt256.ofNat 800) (twoWordHashMem id (UInt256.ofNat 1) mem) = ⟨0⟩ := by
    rw [memLoad_twoWordHashMem _ _ _ (by decide) (by change 832 ≤ mem.size; exact hmem), hz]
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  simp only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    uint128Mask_computed] at rFinal hbFinal
  rw [hz'] at rFinal hbFinal
  rw [hh] at rFinal
  exact ⟨_, _, _, hbFinal, rFinal⟩

end Benchmarks.Midnight
