import Benchmarks.Midnight.RuntimeBlocks_058
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.StorageWriteGas

variable {fork : Ethereum.Fork}

/-! Claim-fee blocks retaining the memory budget across warm or cold storage accesses. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

open midnightBlocks

set_option maxRecDepth 2000000

theorem claim_block_15549_fallthrough_funded {root : UInt256} {credit : Nat} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.sub (UInt256.ofNat ee.source.val) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (UInt256.ofNat 11) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15549) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ),
      TransferBudget root credit (midnight_block_15549_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15580) (midnight_block_15549_fallthrough_stack (mem := mem) (x0 := x0) (R := R)) (midnight_block_15549_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 11) (by native_decide) (by evm_ov)
  have br16 := transferBudgetAt (root := root) (credit := credit) r16 (by transfer_budget hb)
  obtain ⟨_, _, cr17, r17⟩ := RD.sloadMono r16 (by native_decide) (by evm_ov)
  have br17 := transferBudgetAt (root := root) (credit := credit) r17 (br16.mono cr17)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.caller (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 15788) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15580)) r22 (by native_decide)
  have bFinal := transferBudgetAt (root := root) (credit := credit) rFinal (by transfer_budget br17)
  exact ⟨_, _, bFinal, rFinal⟩

theorem claim_block_15604_funded {root : UInt256} {credit : Nat} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 19743) = true)
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15604) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ),
      TransferBudget root credit mem aw C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 19743) (midnight_block_15604_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 15658) (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 15626) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.swap4 (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have br9 := transferBudgetAt (root := root) (credit := credit) r9 (by transfer_budget hb)
  obtain ⟨_, _, cr10, r10⟩ := RD.sloadMono r9 (by native_decide) (by evm_ov)
  have br10 := transferBudgetAt (root := root) (credit := credit) r10 (br9.mono cr10)
  have r11 := r10.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r12 := r11.shr (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19743)) r14 (by native_decide)
  have bFinal := transferBudgetAt (root := root) (credit := credit) rFinal (by transfer_budget br10)
  exact ⟨_, _, bFinal, rFinal⟩

theorem claim_block_15626_funded {root : UInt256} {credit : Nat} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains x1 = true)
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15626) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ),
      TransferBudget root credit mem aw C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 x1 (midnight_block_15626_stack (x2 := x2) (x3 := x3) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x3 (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.shiftLeft x0 (UInt256.ofNat 128))) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x3 (⟨0⟩ : UInt256)))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have br2 := transferBudgetAt (root := root) (credit := credit) r2 (by transfer_budget hb)
  obtain ⟨_, _, cr3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have br3 := transferBudgetAt (root := root) (credit := credit) r3 (br2.mono cr3)
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
  have r23 := r22.dup4 (by native_decide) (by evm_ov)
  have br23 := transferBudgetAt (root := root) (credit := credit) r23 (by transfer_budget br3)
  obtain ⟨_, _, cr24, r24⟩ := sstoreMono r23 hperm (by native_decide) (by evm_ov)
  have br24 := transferBudgetAt (root := root) (credit := credit) r24 (br23.mono cr24)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  have bFinal := transferBudgetAt (root := root) (credit := credit) r25 (by transfer_budget br24)
  exact ⟨_, _, bFinal, r25⟩

theorem claim_block_15678_funded {root : UInt256} {credit : Nat} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15678) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ),
      TransferBudget root credit mem aw C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_15678_stack (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) mem aw rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
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
  have br9 := transferBudgetAt (root := root) (credit := credit) r9 (by transfer_budget hb)
  obtain ⟨_, _, cr10, r10⟩ := RD.sloadMono r9 (by native_decide) (by evm_ov)
  have br10 := transferBudgetAt (root := root) (credit := credit) r10 (br9.mono cr10)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have br13 := transferBudgetAt (root := root) (credit := credit) r13 (by transfer_budget br10)
  obtain ⟨_, _, cr14, r14⟩ := sstoreMono r13 hperm (by native_decide) (by evm_ov)
  have br14 := transferBudgetAt (root := root) (credit := credit) r14 (br13.mono cr14)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 15714) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 3993) (by native_decide) (by evm_ov)
  have r22 := r21.dup10 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r24 := r23.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r24 (by native_decide)
  have bFinal := transferBudgetAt (root := root) (credit := credit) rFinal (by transfer_budget br14)
  exact ⟨_, _, bFinal, rFinal⟩

theorem claim_block_15714_funded {root : UInt256} {credit : Nat} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23236) = true)
    (hb : TransferBudget root credit mem aw C)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 15714) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ),
      TransferBudget root credit (midnight_block_15714_memory (mem := mem) (x5 := x5) (x8 := x8)) (M (M (M (M aw x5 (⟨32⟩ : UInt256)) (memLoad x5 mem) (⟨32⟩ : UInt256)) (memLoad x5 mem) (UInt256.ofNat 32)) (x4 + x5) (⟨32⟩ : UInt256)) C' ∧
      RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23236) (midnight_block_15714_stack (mem := mem) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (R := R)) (midnight_block_15714_memory (mem := mem) (x5 := x5) (x8 := x8)) (M (M (M (M aw x5 (⟨32⟩ : UInt256)) (memLoad x5 mem) (⟨32⟩ : UInt256)) (memLoad x5 mem) (UInt256.ofNat 32)) (x4 + x5) (⟨32⟩ : UInt256)) rdata (sstoreAccountMap ee.codeOwner σ x2 (UInt256.lor (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD x2 (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)))) (UInt256.land x0 x1))) k' C' := by
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
  have br9 := transferBudgetAt (root := root) (credit := credit) r9 (by transfer_budget hb)
  obtain ⟨_, _, cr10, r10⟩ := RD.sloadMono r9 (by native_decide) (by evm_ov)
  have br10 := transferBudgetAt (root := root) (credit := credit) r10 (br9.mono cr10)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have br13 := transferBudgetAt (root := root) (credit := credit) r13 (by transfer_budget br10)
  obtain ⟨_, _, cr14, r14⟩ := sstoreMono r13 hperm (by native_decide) (by evm_ov)
  have br14 := transferBudgetAt (root := root) (credit := credit) r14 (br13.mono cr14)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.dup7 (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup5 (by native_decide) (by evm_ov)
  have r22 := r21.dup7 (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.swap2 (by native_decide) (by evm_ov)
  have r25 := r24.pushConst (UInt256.ofNat 96915674925541926223314501317878574763644028809191320620553928426722873530747) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r27 := r26.caller (by native_decide) (by evm_ov)
  have r28 := r27.swap3 (by native_decide) (by evm_ov)
  have r29 := RD.genLog4 r28 (by native_decide) hperm (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := RD.genMload r30 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.push2 (UInt256.ofNat 23236) (by native_decide) (by evm_ov)
  have r34 := r33.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23236)) r34 (by native_decide)
  have bFinal := transferBudgetAt (root := root) (credit := credit) rFinal (by transfer_budget br14)
  exact ⟨_, _, bFinal, rFinal⟩

end Benchmarks.Midnight
