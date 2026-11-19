import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_018
import Benchmarks.Midnight.RuntimeBlocks_019

/-! Withdrawal blocks retain the gas available for the final token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem withdraw_units_block_4088_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7
  x8 x9 x10 : UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23236) = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 4088) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_4088_memory (ee := ee) (mem :=
      mem) (x5 := x5) (x7 := x7) (x10 := x10)) (M (M (M (M (M (M aw x7 (⟨32⟩ : UInt256)) (memLoad x7
      mem) (⟨32⟩ : UInt256)) ((memLoad x7 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad x7
      mem) + x7) (⟨32⟩ : UInt256)) (memLoad x7 mem) (UInt256.ofNat 96)) (x6 + x7) (⟨32⟩ : UInt256))
      C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23236)
        (midnight_block_4088_stack (ee := ee) (mem := mem) (x5 := x5) (x6 := x6) (x7 := x7) (x8 :=
        x8) (x9 := x9) (x10 := x10) (R := R)) (midnight_block_4088_memory (ee := ee) (mem := mem)
        (x5 := x5) (x7 := x7) (x10 := x10)) (M (M (M (M (M (M aw x7 (⟨32⟩ : UInt256)) (memLoad x7
        mem) (⟨32⟩ : UInt256)) ((memLoad x7 mem) + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) ((memLoad
        x7 mem) + x7) (⟨32⟩ : UInt256)) (memLoad x7 mem) (UInt256.ofNat 96)) (x6 + x7) (⟨32⟩ :
        UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get?
        ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256)))
        (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc10, r10⟩ := RD.sloadMono r9 (by native_decide) (by evm_ov)
  have hb10 := transferBudgetAt (root := budgetRoot) (credit := credit) r10
    (hb.mono ((Nat.le_add_right _ 1).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
      3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
      3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
      3).trans hc10))))))))))
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc14, r14⟩ := sstoreMono r13 hperm (by native_decide) (by evm_ov)
  have hb14 := transferBudgetAt (root := budgetRoot) (credit := credit) r14
    (hb10.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
      3).trans hc14))))
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.dup6 (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have hb21 := transferBudgetAt (root := budgetRoot) (credit := credit) r21
    (by transfer_budget hb14)
  have r22 := r21.swap4 (by native_decide) (by evm_ov)
  have r23 := r22.caller (by native_decide) (by evm_ov)
  have r24 := r23.dup6 (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have hb25 := transferBudgetAt (root := budgetRoot) (credit := credit) r25
    (by transfer_budget hb21)
  have r26 := r25.dup10 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r28 := r27.dup7 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := RD.genMstore r29 (by native_decide) (by evm_ov)
  have hb30 := transferBudgetAt (root := budgetRoot) (credit := credit) r30
    (by transfer_budget hb25)
  have r31 := r30.and (by native_decide) (by evm_ov)
  have r32 := r31.dup6 (by native_decide) (by evm_ov)
  have r33 := r32.dup5 (by native_decide) (by evm_ov)
  have r34 := r33.add (by native_decide) (by evm_ov)
  have r35 := RD.genMstore r34 (by native_decide) (by evm_ov)
  have hb35 := transferBudgetAt (root := budgetRoot) (credit := credit) r35
    (by transfer_budget hb30)
  have r36 := r35.pushConst (UInt256.ofNat
    55349231824570235169958754798976578437414630908295036187169997154993190744023) (width := 32) (op
    := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r38 := r37.dup8 (by native_decide) (by evm_ov)
  have r39 := r38.dup10 (by native_decide) (by evm_ov)
  have r40 := r39.and (by native_decide) (by evm_ov)
  have r41 := r40.swap5 (by native_decide) (by evm_ov)
  have r42 := RD.genLog4 r41 (by native_decide) hperm (by evm_ov)
  have hb42 := transferBudgetAt (root := budgetRoot) (credit := credit) r42
    (by transfer_budget hb35)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := RD.genMload r43 (by native_decide) (by evm_ov)
  have hb44 := transferBudgetAt (root := budgetRoot) (credit := credit) r44
    (by transfer_budget hb42)
  have r45 := r44.and (by native_decide) (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 23236) (by native_decide) (by evm_ov)
  have r47 := r46.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23236)) r47 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb44.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _
    8).trans le_rfl)))

end Benchmarks.Midnight
