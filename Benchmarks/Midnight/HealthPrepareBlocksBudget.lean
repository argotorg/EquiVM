import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_075

variable {fork : Ethereum.Fork}

/-! The health-check position lookup retains funding through its storage read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem health_block_19775_taken_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19839) = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19775) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_19775_taken_memory (mem := mem) (x1 := x1) (x2 := x2))
      (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19839) (midnight_block_19775_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (midnight_block_19775_taken_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.swap2 (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r24 := r23.push0 (by native_decide) (by evm_ov)
  have r25 := RD.genKeccak256 r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r27 := r26.dup2 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (by transfer_budget hb)
  have hb16 := transferBudgetAt (root := budgetRoot) (credit := credit) r16
    (by transfer_budget hb8)
  have hb22 := transferBudgetAt (root := budgetRoot) (credit := credit) r22
    (by transfer_budget hb16)
  have hb28 := transferBudgetAt (root := budgetRoot) (credit := credit) r28
    (by transfer_budget hb22)
  obtain ⟨_, _, hc29, r29⟩ := RD.sloadMono r28 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.dup3 (by native_decide) (by evm_ov)
  have r37 := r36.and (by native_decide) (by evm_ov)
  have r38 := r37.swap3 (by native_decide) (by evm_ov)
  have r39 := r38.push0 (by native_decide) (by evm_ov)
  have r40 := r39.swap3 (by native_decide) (by evm_ov)
  have r41 := r40.dup5 (by native_decide) (by evm_ov)
  have r42 := r41.push2 (UInt256.ofNat 19839) (by native_decide) (by evm_ov)
  have r43 := r42.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19839)) r43 (by native_decide)
  exact ⟨_, _, hb28.mono (by omega), rFinal⟩


theorem health_block_19775_fallthrough_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) ((⟨0⟩ : UInt256).toByteArray.write 0 (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)).toByteArray.write 0 ((UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 ((⟨0⟩ : UInt256).toByteArray.write 0 (x1.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19775) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_19775_fallthrough_memory (mem := mem) (x1 := x1) (x2 := x2))
      (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19831) (midnight_block_19775_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (midnight_block_19775_fallthrough_memory (mem := mem) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.sub (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.swap2 (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r24 := r23.push0 (by native_decide) (by evm_ov)
  have r25 := RD.genKeccak256 r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r27 := r26.dup2 (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (by transfer_budget hb)
  have hb16 := transferBudgetAt (root := budgetRoot) (credit := credit) r16
    (by transfer_budget hb8)
  have hb22 := transferBudgetAt (root := budgetRoot) (credit := credit) r22
    (by transfer_budget hb16)
  have hb28 := transferBudgetAt (root := budgetRoot) (credit := credit) r28
    (by transfer_budget hb22)
  obtain ⟨_, _, hc29, r29⟩ := RD.sloadMono r28 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.dup3 (by native_decide) (by evm_ov)
  have r37 := r36.and (by native_decide) (by evm_ov)
  have r38 := r37.swap3 (by native_decide) (by evm_ov)
  have r39 := r38.push0 (by native_decide) (by evm_ov)
  have r40 := r39.swap3 (by native_decide) (by evm_ov)
  have r41 := r40.dup5 (by native_decide) (by evm_ov)
  have r42 := r41.push2 (UInt256.ofNat 19839) (by native_decide) (by evm_ov)
  have r43 := r42.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19831)) r43 (by native_decide)
  exact ⟨_, _, hb28.mono (by omega), rFinal⟩

end Benchmarks.Midnight
