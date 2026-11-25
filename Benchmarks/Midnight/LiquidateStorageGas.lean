import Benchmarks.Midnight.RuntimeBlocks_030
import Benchmarks.Midnight.PositionUpdateStorage
import Benchmarks.Midnight.StorageWriteGas
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! Paid memory growth and storage gas in the liquidation bad-debt branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks
set_option maxRecDepth 2000000

-- GENERALIZES the generated storage block with its transfer memory budget.
theorem liquidate_block_7541_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    {root : UInt256} {credit : Nat}
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7541) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget root credit mem (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_7541_stack (R := R)) mem (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (memLoad (UInt256.ofNat 672) mem) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (memLoad (UInt256.ofNat 672) mem) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.shiftLeft x0 (UInt256.ofNat 128)) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr11, r11⟩ := RD.sloadMono r10 (by native_decide) (by evm_ov)
  have r12 := r11.swap2 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.not (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.swap2 (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.or (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr23, r23⟩ := sstoreMono r22 hperm (by native_decide) (by evm_ov)
  have r24 := r23.jump (by native_decide) hvalid (by evm_ov)
  simp only [memExpansionCost] at hcr11 hcr23
  exact ⟨_, _, by transfer_budget hb, r24⟩

-- GENERALIZES the generated storage block with its transfer memory budget.
theorem liquidate_block_7591_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    {root : UInt256} {credit : Nat}
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7591) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget root credit mem (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743) (midnight_block_7591_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr5, r5⟩ := RD.sloadMono r4 (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r8 (by native_decide)
  simp only [memExpansionCost] at hcr5
  exact ⟨_, _, by transfer_budget hb, rFinal⟩

-- GENERALIZES the generated storage block with its transfer memory budget.
theorem liquidate_block_7603_taken_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.lt (UInt256.shiftRight x2 (UInt256.ofNat 128)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 7774) = true)
    {root : UInt256} {credit : Nat}
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7603) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget root credit mem (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7774) (midnight_block_7603_taken_stack (x2 := x2) (R := R)) mem (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (memLoad (UInt256.ofNat 672) mem) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (memLoad (UInt256.ofNat 672) mem) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr11, r11⟩ := RD.sloadMono r10 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.or (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr16, r16⟩ := sstoreMono r15 hperm (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r18 := RD.genMload r17 (by native_decide) (by evm_ov)
  have r19 := r18.pop (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r23 := r22.shl (by native_decide) (by evm_ov)
  have r24 := r23.sub (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r27 := r26.shr (by native_decide) (by evm_ov)
  have r28 := r27.lt (by native_decide) (by evm_ov)
  have r29 := r28.push0 (by native_decide) (by evm_ov)
  have r30 := r29.eq (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 7774) (by native_decide) (by evm_ov)
  have r32 := r31.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7774)) r32 (by native_decide)
  simp only [memExpansionCost] at hcr11 hcr16
  exact ⟨_, _, by transfer_budget hb, rFinal⟩

-- GENERALIZES the generated storage block with its transfer memory budget.
theorem liquidate_block_7603_fallthrough_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.eq (⟨0⟩ : UInt256) (UInt256.lt (UInt256.shiftRight x2 (UInt256.ofNat 128)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    {root : UInt256} {credit : Nat}
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7603) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget root credit mem (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7650) (midnight_block_7603_fallthrough_stack (x2 := x2) (R := R)) mem (M (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 800) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ (memLoad (UInt256.ofNat 672) mem) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (memLoad (UInt256.ofNat 672) mem) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr11, r11⟩ := RD.sloadMono r10 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.or (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r15 := RD.genMload r14 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr16, r16⟩ := sstoreMono r15 hperm (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r18 := RD.genMload r17 (by native_decide) (by evm_ov)
  have r19 := r18.pop (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r23 := r22.shl (by native_decide) (by evm_ov)
  have r24 := r23.sub (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r27 := r26.shr (by native_decide) (by evm_ov)
  have r28 := r27.lt (by native_decide) (by evm_ov)
  have r29 := r28.push0 (by native_decide) (by evm_ov)
  have r30 := r29.eq (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 7774) (by native_decide) (by evm_ov)
  have r32 := r31.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7650)) r32 (by native_decide)
  simp only [memExpansionCost] at hcr11 hcr16
  exact ⟨_, _, by transfer_budget hb, rFinal⟩

-- GENERALIZES the generated storage block with its transfer memory budget.
theorem liquidate_block_7650_fallthrough_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.sub (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (memLoad (UInt256.ofNat 672) mem) (⟨0⟩ : UInt256))) (UInt256.ofNat 128))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) = (UInt256.ofNat 0))
    {root : UInt256} {credit : Nat}
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7650) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget root credit mem (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7694) (midnight_block_7650_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) (UInt256.ofNat 672) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr5, r5⟩ := RD.sloadMono r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr11, r11⟩ := RD.sloadMono r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r13 := r12.shr (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.sub (by native_decide) (by evm_ov)
  have r26 := r25.dup4 (by native_decide) (by evm_ov)
  have r27 := r26.gt (by native_decide) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 7276) (by native_decide) (by evm_ov)
  have r29 := r28.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7694)) r29 (by native_decide)
  simp only [memExpansionCost] at hcr5 hcr11
  exact ⟨_, _, by transfer_budget hb, rFinal⟩

-- GENERALIZES the generated storage block with its transfer memory budget.
theorem liquidate_block_7735_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    {root : UInt256} {credit : Nat}
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7735) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget root credit mem (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_7735_stack (R := R)) mem (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ ((memLoad (UInt256.ofNat 672) mem) + (UInt256.ofNat 1)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD ((memLoad (UInt256.ofNat 672) mem) + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.shiftLeft x0 (UInt256.ofNat 128)) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr13, r13⟩ := RD.sloadMono r12 (by native_decide) (by evm_ov)
  have r14 := r13.swap2 (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.not (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.swap2 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.or (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr25, r25⟩ := sstoreMono r24 hperm (by native_decide) (by evm_ov)
  have r26 := r25.jump (by native_decide) hvalid (by evm_ov)
  simp only [memExpansionCost] at hcr13 hcr25
  exact ⟨_, _, by transfer_budget hb, r26⟩

end Benchmarks.Midnight
