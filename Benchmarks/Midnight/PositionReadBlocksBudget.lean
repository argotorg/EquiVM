import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_085

/-! Position-update read blocks retain the caller's memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem position_block_22775_taken_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256}
  {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.lt (UInt256.land (σ.get? ee.codeOwner |>.option
      (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0
      (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat
      32)).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((⟨0⟩ :
      UInt256).toByteArray.write 0 (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) +
      (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23108) = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22775) (x0 :: x1 :: x2 :: x3
      :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_22775_taken_memory (mem :=
      mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256))
      (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩
      : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23108)
        (midnight_block_22775_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2
        := x2) (x3 := x3) (R := R)) (midnight_block_22775_taken_memory (mem := mem) (x1 := x1) (x2
        := x2)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ :
        UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have hb7 := transferBudgetAt (root := budgetRoot) (credit := credit) r7
    (by transfer_budget hb)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have hb10 := transferBudgetAt (root := budgetRoot) (credit := credit) r10
    (by transfer_budget hb7)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.push0 (by native_decide) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
  have hb18 := transferBudgetAt (root := budgetRoot) (credit := credit) r18
    (by transfer_budget hb10)
  have r19 := r18.swap2 (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have hb22 := transferBudgetAt (root := budgetRoot) (credit := credit) r22
    (by transfer_budget hb18)
  have r23 := r22.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have hb24 := transferBudgetAt (root := budgetRoot) (credit := credit) r24
    (by transfer_budget hb22)
  have r25 := r24.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r26 := r25.push0 (by native_decide) (by evm_ov)
  have r27 := RD.genKeccak256 r26 (by native_decide) (by evm_ov)
  have hb27 := transferBudgetAt (root := budgetRoot) (credit := credit) r27
    (by transfer_budget hb24)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc30, r30⟩ := RD.sloadMono r29 (by native_decide) (by evm_ov)
  have hb30 := transferBudgetAt (root := budgetRoot) (credit := credit) r30
    (hb27.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans hc30)))
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.sub (by native_decide) (by evm_ov)
  have r37 := r36.dup3 (by native_decide) (by evm_ov)
  have r38 := r37.and (by native_decide) (by evm_ov)
  have r39 := r38.swap5 (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc41, r41⟩ := RD.sloadMono r40 (by native_decide) (by evm_ov)
  have hb41 := transferBudgetAt (root := budgetRoot) (credit := credit) r41
    (hb30.mono (by omega))
  have r42 := r41.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r45 := r44.shl (by native_decide) (by evm_ov)
  have r46 := r45.sub (by native_decide) (by evm_ov)
  have r47 := r46.dup2 (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.swap3 (by native_decide) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r53 := r52.shl (by native_decide) (by evm_ov)
  have r54 := r53.sub (by native_decide) (by evm_ov)
  have r55 := r54.dup5 (by native_decide) (by evm_ov)
  have r56 := r55.lt (by native_decide) (by evm_ov)
  have r57 := r56.push0 (by native_decide) (by evm_ov)
  have r58 := r57.eq (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 23108) (by native_decide) (by evm_ov)
  have r60 := r59.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23108)) r60 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb41.mono (by omega)


theorem position_block_22775_fallthrough_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256}
  {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 10 ≤ 1024)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.lt (UInt256.land (σ.get? ee.codeOwner |>.option
      (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0
      (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat
      32)).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((⟨0⟩ :
      UInt256).toByteArray.write 0 (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) +
      (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22775) (x0 :: x1 :: x2 :: x3
      :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_22775_fallthrough_memory (mem
      := mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256))
      (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩
      : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22854)
        (midnight_block_22775_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 :=
        x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_22775_fallthrough_memory (mem := mem)
        (x1 := x1) (x2 := x2)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat
        32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256))
        (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have hb7 := transferBudgetAt (root := budgetRoot) (credit := credit) r7
    (by transfer_budget hb)
  have r8 := r7.push0 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have hb10 := transferBudgetAt (root := budgetRoot) (credit := credit) r10
    (by transfer_budget hb7)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.push0 (by native_decide) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
  have hb18 := transferBudgetAt (root := budgetRoot) (credit := credit) r18
    (by transfer_budget hb10)
  have r19 := r18.swap2 (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have hb22 := transferBudgetAt (root := budgetRoot) (credit := credit) r22
    (by transfer_budget hb18)
  have r23 := r22.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have hb24 := transferBudgetAt (root := budgetRoot) (credit := credit) r24
    (by transfer_budget hb22)
  have r25 := r24.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r26 := r25.push0 (by native_decide) (by evm_ov)
  have r27 := RD.genKeccak256 r26 (by native_decide) (by evm_ov)
  have hb27 := transferBudgetAt (root := budgetRoot) (credit := credit) r27
    (by transfer_budget hb24)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc30, r30⟩ := RD.sloadMono r29 (by native_decide) (by evm_ov)
  have hb30 := transferBudgetAt (root := budgetRoot) (credit := credit) r30
    (hb27.mono ((Nat.le_add_right _ 3).trans ((Nat.le_add_right _ 3).trans hc30)))
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.sub (by native_decide) (by evm_ov)
  have r37 := r36.dup3 (by native_decide) (by evm_ov)
  have r38 := r37.and (by native_decide) (by evm_ov)
  have r39 := r38.swap5 (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc41, r41⟩ := RD.sloadMono r40 (by native_decide) (by evm_ov)
  have hb41 := transferBudgetAt (root := budgetRoot) (credit := credit) r41
    (hb30.mono (by omega))
  have r42 := r41.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r45 := r44.shl (by native_decide) (by evm_ov)
  have r46 := r45.sub (by native_decide) (by evm_ov)
  have r47 := r46.dup2 (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.swap3 (by native_decide) (by evm_ov)
  have r50 := r49.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r53 := r52.shl (by native_decide) (by evm_ov)
  have r54 := r53.sub (by native_decide) (by evm_ov)
  have r55 := r54.dup5 (by native_decide) (by evm_ov)
  have r56 := r55.lt (by native_decide) (by evm_ov)
  have r57 := r56.push0 (by native_decide) (by evm_ov)
  have r58 := r57.eq (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 23108) (by native_decide) (by evm_ov)
  have r60 := r59.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22854)) r60 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb41.mono (by omega)


theorem position_block_22854_fallthrough_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256}
  {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option
      (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 128))) (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat
      0))
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22854) (x0 :: x1 :: x2 :: x3
      :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_22854_fallthrough_memory (mem
      := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ :
      UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 22893)
        (midnight_block_22854_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 :=
        x1) (x2 := x2) (x3 := x3) (R := R)) (midnight_block_22854_fallthrough_memory (mem := mem)
        (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ :
        UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have hb2 := transferBudgetAt (root := budgetRoot) (credit := credit) r2
    (by transfer_budget hb)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have hb5 := transferBudgetAt (root := budgetRoot) (credit := credit) r5
    (by transfer_budget hb2)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := RD.genKeccak256 r7 (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (by transfer_budget hb5)
  obtain ⟨_, _, hc9, r9⟩ := RD.sloadMono r8 (by native_decide) (by evm_ov)
  have hb9 := transferBudgetAt (root := budgetRoot) (credit := credit) r9
    (hb8.mono (by omega))
  have r10 := r9.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r11 := r10.shr (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.sub (by native_decide) (by evm_ov)
  have r18 := r17.swap3 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r22 := r21.shl (by native_decide) (by evm_ov)
  have r23 := r22.sub (by native_decide) (by evm_ov)
  have r24 := r23.dup5 (by native_decide) (by evm_ov)
  have r25 := r24.gt (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r27 := r26.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 22893)) r27 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb9.mono (by omega)

end Benchmarks.Midnight
