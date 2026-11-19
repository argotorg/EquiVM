import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_088

/-! Position-update write blocks retain the caller's memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem position_block_23680_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 :
  UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 19 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23680) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit mem aw C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743)
        (midnight_block_23680_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)
        (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw rdata σ
        k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap8 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.swap6 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.swap9 (by native_decide) (by evm_ov)
  have r7 := r6.dup6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc8, r8⟩ := RD.sloadMono r7 (by native_decide) (by evm_ov)
  have hb8 := transferBudgetAt (root := budgetRoot) (credit := credit) r8
    (hb.mono (by omega))
  have r9 := r8.swap6 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 23855) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 23723) (by native_decide) (by evm_ov)
  have r12 := r11.dup13 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 23714) (by native_decide) (by evm_ov)
  have r14 := r13.dup12 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.dup13 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r23 := r22.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r23 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb8.mono (by omega)


theorem position_block_23723_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  x11 x12 : UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 20 ≤ 1024)
    (hperm : ee.perm = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23723) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_23723_memory (mem := mem) (x7
      := x7)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256))
      (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23809)
        (midnight_block_23723_stack (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 :=
        x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (x12 := x12) (R :=
        R)) (midnight_block_23723_memory (mem := mem) (x7 := x7)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩
        : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata
        (sstoreAccountMap ee.codeOwner (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor
        (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2
        (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x9 (UInt256.sub (UInt256.shiftLeft
        (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))) (x2 + (UInt256.ofNat 1))
        (UInt256.lor (UInt256.land ((sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ :
        UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat
        128)) (UInt256.ofNat 1)))) (UInt256.land x9 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat
        1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))).get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac => ac.storage.getD (x2 + (UInt256.ofNat 1)) (⟨0⟩ : UInt256))) (UInt256.lnot
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))
        (UInt256.land (UInt256.shiftRight ((sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor
        (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2
        (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x9 (UInt256.sub (UInt256.shiftLeft
        (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))).get? ee.codeOwner |>.option
        (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
        ((UInt256.ofNat 1).toByteArray.write 0 (x7.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32)) (⟨0⟩ : UInt256))) (UInt256.ofNat 128)) (UInt256.sub
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup11 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r13 := r12.shl (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.not (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc17, r17⟩ := RD.sloadMono r16 (by native_decide) (by evm_ov)
  have hb17 := transferBudgetAt (root := budgetRoot) (credit := credit) r17
    (hb.mono (by omega))
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc21, r21⟩ := sstoreMono r20 hperm (by native_decide) (by evm_ov)
  have hb21 := transferBudgetAt (root := budgetRoot) (credit := credit) r21
    (hb17.mono (by omega))
  have r22 := r21.dup8 (by native_decide) (by evm_ov)
  have r23 := r22.push0 (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have hb24 := transferBudgetAt (root := budgetRoot) (credit := credit) r24
    (by transfer_budget hb21)
  have r25 := r24.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r27 := RD.genMstore r26 (by native_decide) (by evm_ov)
  have hb27 := transferBudgetAt (root := budgetRoot) (credit := credit) r27
    (by transfer_budget hb24)
  have r28 := r27.push2 (UInt256.ofNat 23825) (by native_decide) (by evm_ov)
  have r29 := r28.dup14 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r31 := r30.push0 (by native_decide) (by evm_ov)
  have r32 := RD.genKeccak256 r31 (by native_decide) (by evm_ov)
  have hb32 := transferBudgetAt (root := budgetRoot) (credit := credit) r32
    (by transfer_budget hb27)
  obtain ⟨_, _, hc33, r33⟩ := RD.sloadMono r32 (by native_decide) (by evm_ov)
  have hb33 := transferBudgetAt (root := budgetRoot) (credit := credit) r33
    (hb32.mono (by omega))
  have r34 := r33.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r35 := r34.shr (by native_decide) (by evm_ov)
  have r36 := r35.swap3 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r40 := r39.shl (by native_decide) (by evm_ov)
  have r41 := r40.sub (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r43 := r42.dup3 (by native_decide) (by evm_ov)
  have r44 := r43.add (by native_decide) (by evm_ov)
  have r45 := r44.swap5 (by native_decide) (by evm_ov)
  have r46 := r45.and (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r48 := r47.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r49 := r48.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r50 := r49.shl (by native_decide) (by evm_ov)
  have r51 := r50.sub (by native_decide) (by evm_ov)
  have r52 := r51.not (by native_decide) (by evm_ov)
  have r53 := r52.dup6 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc54, r54⟩ := RD.sloadMono r53 (by native_decide) (by evm_ov)
  have hb54 := transferBudgetAt (root := budgetRoot) (credit := credit) r54
    (hb33.mono (by omega))
  have r55 := r54.and (by native_decide) (by evm_ov)
  have r56 := r55.or (by native_decide) (by evm_ov)
  have r57 := r56.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc58, r58⟩ := sstoreMono r57 hperm (by native_decide) (by evm_ov)
  have hb58 := transferBudgetAt (root := budgetRoot) (credit := credit) r58
    (hb54.mono (by omega))
  have r59 := r58.swap1 (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r61 := r60.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r62 := r61.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r63 := r62.shl (by native_decide) (by evm_ov)
  have r64 := r63.sub (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23809)) r64 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb58.mono (by omega)


theorem position_block_23809_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List
  UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x3 = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23809) (x0 :: x1 :: x2 :: x3
      :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit mem aw C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 x3 (midnight_block_23809_stack (R := R)) mem
        aw rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner
        |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) x0) (UInt256.land
        (UInt256.shiftLeft x1 (UInt256.ofNat 128)) (UInt256.lnot x0)))) k' C' := by
  let r0 := h
  have r1 := r0.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc2, r2⟩ := RD.sloadMono r1 (by native_decide) (by evm_ov)
  have hb2 := transferBudgetAt (root := budgetRoot) (credit := credit) r2
    (hb.mono (by omega))
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.not (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc14, r14⟩ := sstoreMono r13 hperm (by native_decide) (by evm_ov)
  have hb14 := transferBudgetAt (root := budgetRoot) (credit := credit) r14
    (hb2.mono (by omega))
  have r15 := r14.jump (by native_decide) hvalid (by evm_ov)
  refine ⟨_, _, ?_, r15⟩
  exact hb14.mono (by omega)


theorem position_block_23825_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23825) (x0 :: x1 :: R) mem
      aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit mem aw C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_23825_stack (R := R)) mem
        aw rdata (sstoreAccountMap ee.codeOwner σ x0 (UInt256.lor (UInt256.land (UInt256.lnot
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))
        (UInt256.shiftLeft (UInt256.ofNat ee.header.timestamp) (UInt256.ofNat 128))) (UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x0 (⟨0⟩ :
        UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have hb3 := transferBudgetAt (root := budgetRoot) (credit := credit) r3
    (hb.mono (by omega))
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.timestamp (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r16 := r15.shl (by native_decide) (by evm_ov)
  have r17 := r16.sub (by native_decide) (by evm_ov)
  have r18 := r17.not (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.or (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc22, r22⟩ := sstoreMono r21 hperm (by native_decide) (by evm_ov)
  have hb22 := transferBudgetAt (root := budgetRoot) (credit := credit) r22
    (hb3.mono (by omega))
  have r23 := r22.jump (by native_decide) hvalid (by evm_ov)
  refine ⟨_, _, ?_, r23⟩
  exact hb22.mono (by omega)


theorem position_block_23879_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 :
  UInt256} {R : List UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20456) = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23879) (x0 :: x1 :: x2 :: x3
      :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit (midnight_block_23879_memory (mem := mem) (x9
      := x9)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256))
      (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20456)
        (midnight_block_23879_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 :=
        x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R))
        (midnight_block_23879_memory (mem := mem) (x9 := x9)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ :
        UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ
        k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup10 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have hb4 := transferBudgetAt (root := budgetRoot) (credit := credit) r4
    (by transfer_budget hb)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have hb7 := transferBudgetAt (root := budgetRoot) (credit := credit) r7
    (by transfer_budget hb4)
  have r8 := r7.push2 (UInt256.ofNat 23908) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push0 (by native_decide) (by evm_ov)
  have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
  have hb12 := transferBudgetAt (root := budgetRoot) (credit := credit) r12
    (by transfer_budget hb7)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.swap2 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc16, r16⟩ := RD.sloadMono r15 (by native_decide) (by evm_ov)
  have hb16 := transferBudgetAt (root := budgetRoot) (credit := credit) r16
    (hb12.mono (by omega))
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shr (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r20 := r19.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20456)) r20 (by native_decide)
  refine ⟨_, _, ?_, rFinal⟩
  exact hb16.mono (by omega)


theorem position_block_23908_budget {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List
  UInt256}
    {budgetRoot : UInt256} {credit : Nat}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x2 = true)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23908) (x0 :: x1 :: x2 :: R)
      mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), TransferBudget budgetRoot credit mem aw C' ∧
      RD Benchmarks.Midnight.midnightBytecode ee g s0 x2 (midnight_block_23908_stack (R := R)) mem
        aw rdata (sstoreAccountMap ee.codeOwner σ x1 (UInt256.lor (UInt256.land (UInt256.lnot
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))
        (UInt256.shiftLeft x0 (UInt256.ofNat 128))) (UInt256.land (UInt256.sub (UInt256.shiftLeft
        (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option
        (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x1 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have hb3 := transferBudgetAt (root := budgetRoot) (credit := credit) r3
    (hb.mono (by omega))
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
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc24, r24⟩ := sstoreMono r23 hperm (by native_decide) (by evm_ov)
  have hb24 := transferBudgetAt (root := budgetRoot) (credit := credit) r24
    (hb3.mono (by omega))
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  refine ⟨_, _, ?_, r25⟩
  exact hb24.mono (by omega)

end Benchmarks.Midnight
