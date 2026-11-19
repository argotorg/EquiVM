import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_018
import Benchmarks.Midnight.RuntimeBlocks_019

/-! Withdrawal blocks retain the gas available for the final token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem withdraw_units_block_4002_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7
  x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 4002) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403)
      (midnight_block_4002_stack (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8)
      (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ
      x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac =>
      ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft
      (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
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
  have r15 := r14.push2 (UInt256.ofNat 4027) (by native_decide) (by evm_ov)
  have r16 := r15.dup10 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r18 := r17.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r18 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  omega

theorem withdraw_units_block_4027_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R :
  List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 4027) (x0 :: x1 :: R) mem aw
      rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743)
      (midnight_block_4027_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ
      k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 4052) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.swap3 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc14, r14⟩ := RD.sloadMono r13 (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r17 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  omega

theorem withdraw_units_block_4052_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7
  x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 4052) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403)
      (midnight_block_4052_stack (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8)
      (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ
      x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac =>
      ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft
      (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
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
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 4088) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 3993) (by native_decide) (by evm_ov)
  have r22 := r21.dup12 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r24 := r23.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r24 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  omega

theorem withdraw_units_block_4216_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem :
  ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R :
  List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 4216) (x0 :: x1 :: x2 :: R)
      mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 x1
      (midnight_block_4216_stack (x2 := x2) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ
      x2 (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.shiftLeft x0 (UInt256.ofNat 128)))
      (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD
      x2 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.not (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.or (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc24, r24⟩ := sstoreMono r23 hperm (by native_decide) (by evm_ov)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  refine ⟨_, _, ?_, r25⟩
  omega

end Benchmarks.Midnight
