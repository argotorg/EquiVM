import Benchmarks.Midnight.RuntimeBlocks_028
import Benchmarks.Midnight.StorageWriteGas

variable {fork : Ethereum.Fork}

/-! Storage blocks preserve the gas needed for liquidation's final balance updates. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

-- GENERALIZES the generated block at 6845 with gas-payment information.
theorem liquidate_block_6845_paid {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6845) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C + memExpansionCost aw (UInt256.ofNat 672) ⟨32⟩ ≤ C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456) (midnight_block_6845_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) mem (M aw (UInt256.ofNat 672) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 6873) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 672) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.swap3 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := r13.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc15, r15⟩ := RD.sloadMono r14 (by native_decide) (by evm_ov)
  have r16 := r15.and (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r18 := r17.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20456)) r18 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

-- GENERALIZES the generated block at 6873 with gas-payment information.
theorem liquidate_block_6873_paid {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6873) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C + memExpansionCost aw (UInt256.ofNat 608) ⟨32⟩ ≤ C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_6873_stack (mem := mem) (R := R)) mem (M aw (UInt256.ofNat 608) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
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
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc14, r14⟩ := sstoreMono r13 hperm (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 6925) (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 6914) (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 608) (by native_decide) (by evm_ov)
  have r24 := RD.genMload r23 (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r26 := r25.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r26 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

-- GENERALIZES the generated block at 6914 with gas-payment information.
theorem liquidate_block_6914_paid {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6914) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743) (midnight_block_6914_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  have r4 := r3.dup7 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc6, r6⟩ := RD.sloadMono r5 (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r9 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

-- GENERALIZES the generated block at 6925 with gas-payment information.
theorem liquidate_block_6925_paid {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 5480) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6925) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 5480) (midnight_block_6925_stack (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (x3 + x2) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x3 + x2) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
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
  have r10 := r9.dup5 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc12, r12⟩ := RD.sloadMono r11 (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.or (by native_decide) (by evm_ov)
  have r15 := r14.swap2 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc17, r17⟩ := sstoreMono r16 hperm (by native_decide) (by evm_ov)
  have r18 := r17.dup7 (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.dup1 (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 5480) (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5480)) r22 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

end Benchmarks.Midnight
