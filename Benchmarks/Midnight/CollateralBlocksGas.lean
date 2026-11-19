import Benchmarks.Midnight.RuntimeBlocks_064
import Benchmarks.Midnight.RuntimeBlocks_065
import Benchmarks.Midnight.RuntimeBlocks_020
import Benchmarks.Midnight.StorageWriteGas

/-! Collateral reads and writes retain the cumulative gas already paid. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks
set_option maxRecDepth 2000000

theorem collateral_block_17102_taken_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))) x2)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 17536) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17102) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17536) (midnight_block_17102_taken_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 17536) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17536)) r14 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩


theorem collateral_block_17102_fallthrough_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))) x2)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17102) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17119) (midnight_block_17102_fallthrough_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.swap2 (by native_decide) (by evm_ov)
  have r10 := r9.dup3 (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 17536) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17119)) r14 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩


theorem collateral_block_17274_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 17385) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17274) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17385) (midnight_block_17274_stack (ee := ee) (σ := σ) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ (x1 + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.land (UInt256.shiftLeft (UInt256.land (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) x2) (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x1 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 128))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.ofNat 128)) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1334440654591915542993625911497130241) (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 20016609818878733144904388672456953615) (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r8 := r7.swap5 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 113427455640312821154458202477256070485) (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr12, r12⟩ := RD.sloadMono r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r14 := r13.shr (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.dup9 (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 17385) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r23 := r22.shl (by native_decide) (by evm_ov)
  have r24 := r23.sub (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.dup1 (by native_decide) (by evm_ov)
  have r28 := r27.swap5 (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r33 := r32.shl (by native_decide) (by evm_ov)
  have r34 := r33.sub (by native_decide) (by evm_ov)
  have r35 := r34.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr36, r36⟩ := RD.sloadMono r35 (by native_decide) (by evm_ov)
  have r37 := r36.swap2 (by native_decide) (by evm_ov)
  have r38 := r37.dup2 (by native_decide) (by evm_ov)
  have r39 := r38.not (by native_decide) (by evm_ov)
  have r40 := r39.swap1 (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r42 := r41.shl (by native_decide) (by evm_ov)
  have r43 := r42.and (by native_decide) (by evm_ov)
  have r44 := r43.swap2 (by native_decide) (by evm_ov)
  have r45 := r44.and (by native_decide) (by evm_ov)
  have r46 := r45.or (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr48, r48⟩ := sstoreMono r47 hperm (by native_decide) (by evm_ov)
  have r49 := r48.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17385)) r49 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩


theorem collateral_block_4593_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x3 = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 4593) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 x3 (midnight_block_4593_stack (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x1 (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (UInt256.shiftLeft x0 (UInt256.ofNat 3)))) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256)))) (UInt256.shiftLeft (UInt256.land x2 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.shiftLeft x0 (UInt256.ofNat 3))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.sub (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr12, r12⟩ := RD.sloadMono r11 (by native_decide) (by evm_ov)
  have r13 := r12.swap3 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.swap4 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.dup4 (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.swap3 (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.not (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.or (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcr26, r26⟩ := sstoreMono r25 hperm (by native_decide) (by evm_ov)
  have r27 := r26.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, by omega, r27⟩


end Benchmarks.Midnight
