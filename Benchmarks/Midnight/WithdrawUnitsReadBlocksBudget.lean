import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_018
import Benchmarks.Midnight.RuntimeBlocks_019

variable {fork : Ethereum.Fork}

/-! Withdrawal blocks retain the gas available for the final token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem withdraw_units_block_3909_taken_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7
  x8 x9 x10 : UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD
      (keccakWord (⟨0⟩ : UInt256) x7 ((keccakWord (memLoad (UInt256.ofNat 800) ((memLoad
      (UInt256.ofNat 800) (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
      32)).toByteArray.write 0 (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
      32) (UInt256.ofNat 32).toNat 32)) x7 ((memLoad (UInt256.ofNat 800) (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32)).toByteArray.write 0 (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
      (x4.toByteArray.write 0 ((memLoad (UInt256.ofNat 800) (x3.toByteArray.write 0 mem (memLoad
      (UInt256.ofNat 800) mem).toNat 32)).toByteArray.write 0 (x3.toByteArray.write 0 mem (memLoad
      (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat
      1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 4177) = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 3909) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_3909_taken_memory (mem := mem)
      (x3 := x3) (x4 := x4) (x7 := x7)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 800)
      (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 800)
      (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256))
      (memLoad (UInt256.ofNat 800) ((memLoad (UInt256.ofNat 800) (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32)).toByteArray.write 0 (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) x7) (⟨0⟩ : UInt256)
      (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) x7) (UInt256.ofNat 800)
      (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 4177)
        (midnight_block_3909_taken_stack (ee := ee) (mem := mem) (σ := σ) (x3 := x3) (x4 := x4) (x5
        := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R))
        (midnight_block_3909_taken_memory (mem := mem) (x3 := x3) (x4 := x4) (x7 := x7)) (M (M (M (M
        (M (M (M (M (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800)
        mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ :
        UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) ((memLoad
        (UInt256.ofNat 800) (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
        32)).toByteArray.write 0 (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
        32) (UInt256.ofNat 32).toNat 32)) x7) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32)
        (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) x7) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat
        800) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have hb7 := transferBudgetAt (root := budgetRoot) (credit := credit) r7
    (by transfer_budget hb)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (by transfer_budget hb7)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have hb10 := transferBudgetAt (root := budgetRoot) (credit := credit) r10
    (by transfer_budget hb8)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have hb12 := transferBudgetAt (root := budgetRoot) (credit := credit) r12
    (by transfer_budget hb10)
  have r13 := r12.dup5 (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have hb15 := transferBudgetAt (root := budgetRoot) (credit := credit) r15
    (by transfer_budget hb12)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have hb16 := transferBudgetAt (root := budgetRoot) (credit := credit) r16
    (by transfer_budget hb15)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have hb19 := transferBudgetAt (root := budgetRoot) (credit := credit) r19
    (by transfer_budget hb16)
  have r20 := r19.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have hb21 := transferBudgetAt (root := budgetRoot) (credit := credit) r21
    (by transfer_budget hb19)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by native_decide) (by evm_ov)
  have hb24 := transferBudgetAt (root := budgetRoot) (credit := credit) r24
    (by transfer_budget hb21)
  have r25 := r24.swap3 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have hb27 := transferBudgetAt (root := budgetRoot) (credit := credit) r27
    (by transfer_budget hb24)
  have r28 := r27.pop (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have hb30 := transferBudgetAt (root := budgetRoot) (credit := credit) r30
    (by transfer_budget hb27)
  have r31 := r30.swap4 (by native_decide) (by evm_ov)
  have r32 := r31.dup10 (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc34, r34⟩ := RD.sloadMono r33 (by native_decide) (by evm_ov)
  have hb34 := transferBudgetAt (root := budgetRoot) (credit := credit) r34
    (hb30.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
      3).trans hc34))))
  have r35 := r34.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r38 := r37.shl (by native_decide) (by evm_ov)
  have r39 := r38.sub (by native_decide) (by evm_ov)
  have r40 := r39.dup2 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.swap1 (by native_decide) (by evm_ov)
  have r43 := r42.dup2 (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 4177) (by native_decide) (by evm_ov)
  have r45 := r44.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4177)) r45 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb34.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
    3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
    3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
    3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 10).trans le_rfl)))))))))))

theorem withdraw_units_block_3909_fallthrough_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5
  x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD
      (keccakWord (⟨0⟩ : UInt256) x7 ((keccakWord (memLoad (UInt256.ofNat 800) ((memLoad
      (UInt256.ofNat 800) (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
      32)).toByteArray.write 0 (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
      32) (UInt256.ofNat 32).toNat 32)) x7 ((memLoad (UInt256.ofNat 800) (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32)).toByteArray.write 0 (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
      (x4.toByteArray.write 0 ((memLoad (UInt256.ofNat 800) (x3.toByteArray.write 0 mem (memLoad
      (UInt256.ofNat 800) mem).toNat 32)).toByteArray.write 0 (x3.toByteArray.write 0 mem (memLoad
      (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat
      1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 3909) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_3909_fallthrough_memory (mem
      := mem) (x3 := x3) (x4 := x4) (x7 := x7)) (M (M (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat
      800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 800)
      (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256))
      (memLoad (UInt256.ofNat 800) ((memLoad (UInt256.ofNat 800) (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32)).toByteArray.write 0 (x3.toByteArray.write 0 mem
      (memLoad (UInt256.ofNat 800) mem).toNat 32) (UInt256.ofNat 32).toNat 32)) x7) (⟨0⟩ : UInt256)
      (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) x7) (UInt256.ofNat 800)
      (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 3971)
        (midnight_block_3909_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x3 := x3) (x4 :=
        x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R))
        (midnight_block_3909_fallthrough_memory (mem := mem) (x3 := x3) (x4 := x4) (x7 := x7)) (M (M
        (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat
        800) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ :
        UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 800) ((memLoad
        (UInt256.ofNat 800) (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
        32)).toByteArray.write 0 (x3.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat
        32) (UInt256.ofNat 32).toNat 32)) x7) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32)
        (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) x7) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) (UInt256.ofNat
        800) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have hb7 := transferBudgetAt (root := budgetRoot) (credit := credit) r7
    (by transfer_budget hb)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (by transfer_budget hb7)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have hb10 := transferBudgetAt (root := budgetRoot) (credit := credit) r10
    (by transfer_budget hb8)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have hb12 := transferBudgetAt (root := budgetRoot) (credit := credit) r12
    (by transfer_budget hb10)
  have r13 := r12.dup5 (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  have hb15 := transferBudgetAt (root := budgetRoot) (credit := credit) r15
    (by transfer_budget hb12)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have hb16 := transferBudgetAt (root := budgetRoot) (credit := credit) r16
    (by transfer_budget hb15)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genMstore r18 (by native_decide) (by evm_ov)
  have hb19 := transferBudgetAt (root := budgetRoot) (credit := credit) r19
    (by transfer_budget hb16)
  have r20 := r19.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r21 := RD.genMstore r20 (by native_decide) (by evm_ov)
  have hb21 := transferBudgetAt (root := budgetRoot) (credit := credit) r21
    (by transfer_budget hb19)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by native_decide) (by evm_ov)
  have hb24 := transferBudgetAt (root := budgetRoot) (credit := credit) r24
    (by transfer_budget hb21)
  have r25 := r24.swap3 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r27 := RD.genMload r26 (by native_decide) (by evm_ov)
  have hb27 := transferBudgetAt (root := budgetRoot) (credit := credit) r27
    (by transfer_budget hb24)
  have r28 := r27.pop (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have hb30 := transferBudgetAt (root := budgetRoot) (credit := credit) r30
    (by transfer_budget hb27)
  have r31 := r30.swap4 (by native_decide) (by evm_ov)
  have r32 := r31.dup10 (by native_decide) (by evm_ov)
  have r33 := r32.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc34, r34⟩ := RD.sloadMono r33 (by native_decide) (by evm_ov)
  have hb34 := transferBudgetAt (root := budgetRoot) (credit := credit) r34
    (hb30.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
      3).trans hc34))))
  have r35 := r34.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r38 := r37.shl (by native_decide) (by evm_ov)
  have r39 := r38.sub (by native_decide) (by evm_ov)
  have r40 := r39.dup2 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.swap1 (by native_decide) (by evm_ov)
  have r43 := r42.dup2 (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 4177) (by native_decide) (by evm_ov)
  have r45 := r44.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3971)) r45 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb34.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
    3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
    3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
    3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 10).trans le_rfl)))))))))))

end Benchmarks.Midnight
