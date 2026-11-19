import Benchmarks.Midnight.LiquidatePositionBlock

/-! The position-lookup summary with memory funding retained at each memory operation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

-- GENERALIZES midnight_block_5161 with the memory funding needed by later external calls.
theorem liquidatePositionBlock_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id borrower dl dp budgetRoot : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hm : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hc : borrower.toNat < EVM.addressModulus)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD midnightBytecode ee g s0 ⟨5161⟩ (id :: dl :: borrower :: dp :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot credit (liquidatePositionMemory mem id borrower)
      aw' C' ∧ RD midnightBytecode ee g s0
      (if calldataWord ee.calldata 100 = ⟨0⟩ then ⟨5248⟩ else ⟨8453⟩)
      (UInt256.isZero (calldataWord ee.calldata 100) ::
        UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)) ::
        positionSlot id borrower :: dp :: dl :: borrower ::
        UInt256.isZero (calldataWord ee.calldata 100) :: R)
      (liquidatePositionMemory mem id borrower) aw' rdata σ k' C' := by
  have hn := liquidatePositionBlock_normalize (ee := ee) (id := id)
    (dl := dl) (dp := dp) (R := R) hm hz hc
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have hb3 := transferBudgetAt (root := budgetRoot) (credit := credit) r3
    (by transfer_budget hb)
  have r4 := r3.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have hb5 := transferBudgetAt (root := budgetRoot) (credit := credit) r5
    (by transfer_budget hb3)
  have r6 := r5.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have hb7 := transferBudgetAt (root := budgetRoot) (credit := credit) r7
    (by transfer_budget hb5)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (by transfer_budget hb7)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have hb11 := transferBudgetAt (root := budgetRoot) (credit := credit) r11
    (by transfer_budget hb8)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have hb14 := transferBudgetAt (root := budgetRoot) (credit := credit) r14
    (by transfer_budget hb11)
  have r15 := RD.genKeccak256 r14 (by native_decide) (by evm_ov)
  have hb15 := transferBudgetAt (root := budgetRoot) (credit := credit) r15
    (by transfer_budget hb14)
  have r16 := r15.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have hb17 := transferBudgetAt (root := budgetRoot) (credit := credit) r17
    (by transfer_budget hb15)
  have r18 := r17.push2 (UInt256.ofNat 768) (by native_decide) (by evm_ov)
  have r19 := RD.genMload r18 (by native_decide) (by evm_ov)
  have hb19 := transferBudgetAt (root := budgetRoot) (credit := credit) r19
    (by transfer_budget hb17)
  have r20 := r19.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have hb21 := transferBudgetAt (root := budgetRoot) (credit := credit) r21
    (by transfer_budget hb19)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have hb22 := transferBudgetAt (root := budgetRoot) (credit := credit) r22
    (by transfer_budget hb21)
  have r23 := r22.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have hb24 := transferBudgetAt (root := budgetRoot) (credit := credit) r24
    (by transfer_budget hb22)
  have r25 := r24.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r26 := RD.genMstore r25 (by native_decide) (by evm_ov)
  have hb26 := transferBudgetAt (root := budgetRoot) (credit := credit) r26
    (by transfer_budget hb24)
  have r27 := r26.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r29 := RD.genMload r28 (by native_decide) (by evm_ov)
  have hb29 := transferBudgetAt (root := budgetRoot) (credit := credit) r29
    (by transfer_budget hb26)
  have r30 := RD.genKeccak256 r29 (by native_decide) (by evm_ov)
  have hb30 := transferBudgetAt (root := budgetRoot) (credit := credit) r30
    (by transfer_budget hb29)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.dup4 (by native_decide) (by evm_ov)
  have r37 := r36.and (by native_decide) (by evm_ov)
  have r38 := r37.push0 (by native_decide) (by evm_ov)
  have r39 := RD.genMstore r38 (by native_decide) (by evm_ov)
  have hb39 := transferBudgetAt (root := budgetRoot) (credit := credit) r39
    (by transfer_budget hb30)
  have r40 := r39.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r41 := RD.genMstore r40 (by native_decide) (by evm_ov)
  have hb41 := transferBudgetAt (root := budgetRoot) (credit := credit) r41
    (by transfer_budget hb39)
  have r42 := r41.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r43 := r42.push0 (by native_decide) (by evm_ov)
  have r44 := RD.genKeccak256 r43 (by native_decide) (by evm_ov)
  have hb44 := transferBudgetAt (root := budgetRoot) (credit := credit) r44
    (by transfer_budget hb41)
  have r45 := r44.swap3 (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r47 := r46.calldataload (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.swap4 (by native_decide) (by evm_ov)
  have r50 := r49.dup5 (by native_decide) (by evm_ov)
  have r51 := r50.dup1 (by native_decide) (by evm_ov)
  have r52 := r51.iszero (by native_decide) (by evm_ov)
  have r53 := r52.swap1 (by native_decide) (by evm_ov)
  have r54 := r53.dup2 (by native_decide) (by evm_ov)
  have r55 := r54.push2 (UInt256.ofNat 8453) (by native_decide) (by evm_ov)
  have hb55 := transferBudgetAt (root := budgetRoot) (credit := credit) r55
    (hb44.mono (by omega))
  by_cases hr : calldataWord ee.calldata 100 = ⟨0⟩
  · have r56 := r55.jumpiNT (by native_decide) (by
      change UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)) = ⟨0⟩
      rw [hr]; decide) (by evm_ov)
    have rf := RD.normalizePC (pc' := (UInt256.ofNat 5248)) r56 (by native_decide)
    have hf := transferBudgetAt (root := budgetRoot) (credit := credit) rf
      (hb55.mono (by omega))
    change TransferBudget budgetRoot credit
      (midnight_block_5161_fallthrough_memory (mem := mem) (x0 := id) (x2 := borrower)) _ _ at hf
    change RD midnightBytecode ee g s0 ⟨5248⟩
      (midnight_block_5161_fallthrough_stack (ee := ee) (mem := mem)
        (x0 := id) (x1 := dl) (x2 := borrower) (x3 := dp) (R := R))
      (midnight_block_5161_fallthrough_memory (mem := mem) (x0 := id) (x2 := borrower))
      _ rdata σ _ _ at rf
    rw [hn.1] at hf rf
    rw [hn.2] at rf
    exact ⟨_, _, _, hf, by simpa only [if_pos hr, List.cons_append, List.nil_append] using rf⟩
  · have r56 := r55.jumpiT (by native_decide) (by
      change UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)) ≠ ⟨0⟩
      rw [isZero_eq_zero_of_ne hr]; decide) (by jump_dest) (by evm_ov)
    have rf := RD.normalizePC (pc' := (UInt256.ofNat 8453)) r56 (by native_decide)
    have hf := transferBudgetAt (root := budgetRoot) (credit := credit) rf
      (hb55.mono (by omega))
    change TransferBudget budgetRoot credit
      (midnight_block_5161_fallthrough_memory (mem := mem) (x0 := id) (x2 := borrower)) _ _ at hf
    change RD midnightBytecode ee g s0 ⟨8453⟩
      (midnight_block_5161_fallthrough_stack (ee := ee) (mem := mem)
        (x0 := id) (x1 := dl) (x2 := borrower) (x3 := dp) (R := R))
      (midnight_block_5161_fallthrough_memory (mem := mem) (x0 := id) (x2 := borrower))
      _ rdata σ _ _ at rf
    rw [hn.1] at hf rf
    rw [hn.2] at rf
    exact ⟨_, _, _, hf, by simpa only [if_neg hr, List.cons_append, List.nil_append] using rf⟩

end Benchmarks.Midnight
