import Benchmarks.Midnight.SupplyAuthorizationTrace
import Benchmarks.Midnight.RuntimeBlocks_038
import Benchmarks.Midnight.RuntimeBlocks_039
import Benchmarks.Midnight.RuntimeBlocks_040
import Benchmarks.Midnight.RuntimeBlocks_011

variable {fork : Ethereum.Fork}

/-! Authorization for repayment, including the cached scratch-memory address. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000 in
theorem repayAuthorizationRead_accounted {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 x2 x3 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hvalid : (D_J midnightBytecode 0).contains (UInt256.ofNat 9847) = true)
    (ha : MemoryAccounting mem aw C)
    (h : RD fork midnightBytecode ee g s0 ⟨10360⟩ (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryAccounting (supplyAuthorizationMemory mem ee x3) aw' C' ∧
      RD fork midnightBytecode ee g s0 ⟨9847⟩
        (UInt256.land (solcSlotWordAt (authorizationSlot x3 (solcSourceWord ee)) σ ee) ⟨255⟩ ::
          x1 :: x2 :: x3 :: R) (supplyAuthorizationMemory mem ee x3) aw' rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r5 := RD.genMload r4 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r12 := RD.genMload r11 (by native_decide) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.caller (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r27 := r26.push0 (by native_decide) (by evm_ov)
  have r28 := RD.genKeccak256 r27 (by native_decide) (by evm_ov)
  have ha28 := memoryAccountingAt r28 (by memory_account ha)
  obtain ⟨_, _, hc29, r29⟩ := RD.sloadMono r28 (by native_decide) (by evm_ov)
  have ha29 := memoryAccountingAt r29 ⟨by
    have hp := ha28.paid
    unfold MemoryPaid at hp ⊢
    omega, ha28.covered⟩
  have r30 := r29.and (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 9847) (by native_decide) (by evm_ov)
  have r32 := r31.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9847)) r32 (by native_decide)
  have haFinal := memoryAccountingAt rFinal (by memory_account ha29)
  have hz' : memLoad (UInt256.ofNat 800) (twoWordHashMem x3 (UInt256.ofNat 3) mem) = ⟨0⟩ := by
    rw [memLoad_twoWordHashMem _ _ _ (by decide) (by change 832 ≤ mem.size; exact hmem), hz]
  simp only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    addressMask_computed, solcAddrMask_clean (solcSourceWord_canonical ee)] at rFinal haFinal
  rw [hz'] at rFinal haFinal
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem x3 (UInt256.ofNat 3) mem) =
      solcMappingSlot ⟨3⟩ x3 := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  rw [hh1] at rFinal haFinal
  have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (supplyAuthorizationMemory mem ee x3) =
      authorizationSlot x3 (solcSourceWord ee) :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by
      rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega)
  change RD fork midnightBytecode ee g s0 ⟨9847⟩
    (UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (supplyAuthorizationMemory mem ee x3)) σ ee) ⟨255⟩ :: x1 :: x2 :: x3 :: R)
    (supplyAuthorizationMemory mem ee x3) _ rdata σ _ _ at rFinal
  rw [hh2] at rFinal
  exact ⟨_, _, _, haFinal, rFinal⟩

set_option maxRecDepth 2000000 in
theorem repayAuthorizationGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw user dl dp : UInt256} {k C : Nat} {R : List UInt256}
    (evm : EVM.State) (henv : evm.executionEnv = I)
    (hstack : R.length + 8 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hz800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcanon : user.toNat < EVM.addressModulus) (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨9832⟩ (dl :: dp :: solcAddrMask :: user :: R)
      mem aw rdata evm.accountMap k C) :
    (¬ onBehalfAllowed evm user ∧ RDrev fork midnightBytecode g s0) ∨
    (onBehalfAllowed evm user ∧ ∃ mem' aw' k' C',
      MemoryPrefix mem mem' mem.size ∧ mem'.size = mem.size ∧
      memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem ∧ MemoryAccounting mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨9853⟩ (dp :: dl :: user :: R) mem' aw' rdata evm.accountMap k' C') := by
  have finish {mem' aw' k' C' check}
      (hp : MemoryPrefix mem mem' mem.size) (hs : mem'.size = mem.size)
      (hf : memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem)
      (ha' : MemoryAccounting mem' aw' C')
      (hc : check ≠ ⟨0⟩ ↔ onBehalfAllowed evm user)
      (rd' : RD fork midnightBytecode I g s0 ⟨9847⟩ (check :: dp :: dl :: user :: R)
        mem' aw' rdata evm.accountMap k' C') :
      (¬ onBehalfAllowed evm user ∧ RDrev fork midnightBytecode g s0) ∨
      (onBehalfAllowed evm user ∧ ∃ mem' aw' k' C',
        MemoryPrefix mem mem' mem.size ∧ mem'.size = mem.size ∧
        memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem ∧ MemoryAccounting mem' aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨9853⟩ (dp :: dl :: user :: R) mem' aw' rdata evm.accountMap k' C') := by
    by_cases hz : check = ⟨0⟩
    · have rr := midnight_block_9847_taken (by simp only [List.length_cons]; omega)
        (by rw [hz]; decide) (by jump_dest) rd'
      exact Or.inl ⟨fun h ↦ (hc.mpr h) hz, midnight_block_1943 (by
        simp only [midnight_block_9847_taken_stack, List.length_cons]; omega) rr⟩
    · have rr := midnight_block_9847_fallthrough (by simp only [List.length_cons]; omega)
        (isZero_eq_zero_of_ne hz) rd'
      exact Or.inr ⟨hc.mp hz, _, _, _, _, hp, hs, hf,
        by memory_account ha', rr⟩
  by_cases hself : user = solcSourceWord I
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨1⟩ := by
      rw [hself, uInt256_eq_self]
    have rd1 := midnight_block_9832_fallthrough (by omega)
      (by rw [solcAddrMask_clean hcanon]; change UInt256.isZero (UInt256.eq user (solcSourceWord I)) = _
          rw [heq]; rfl) rd
    simp only [midnight_block_9832_fallthrough_stack, solcAddrMask_clean hcanon] at rd1
    apply finish (MemoryPrefix.refl _ _) rfl rfl (by memory_account ha) _ rd1
    change UInt256.eq user (solcSourceWord I) ≠ ⟨0⟩ ↔ _
    simp only [onBehalfAllowed, henv, hself, true_or, uInt256_eq_self]
    decide
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨0⟩ := u256_eq_of_ne hself
    have rd1 := midnight_block_9832_taken (by omega)
      (by rw [solcAddrMask_clean hcanon]; change UInt256.isZero (UInt256.eq user (solcSourceWord I)) ≠ _
          rw [heq]; decide) (by jump_dest) rd
    simp only [midnight_block_9832_taken_stack, solcAddrMask_clean hcanon] at rd1
    obtain ⟨aw2, k2, C2, ha2, rd2⟩ := repayAuthorizationRead_accounted
      (by omega) hmem hz800 (by jump_dest)
      (by memory_account ha) rd1
    have hs1 : (twoWordHashMem user ⟨3⟩ mem).size = mem.size :=
      twoWordHashMem_size_of_ge_64 _ _ (by omega)
    apply finish ((twoWordHashMem_prefix mem user ⟨3⟩ mem.size).trans
      (twoWordHashMem_prefix _ _ _ mem.size))
      (supplyAuthorizationMemory_size mem I user (by omega)) ?_ ha2 ?_ rd2
    · change memLoad ⟨64⟩ (supplyAuthorizationMemory mem I user) = memLoad ⟨64⟩ mem
      rw [supplyAuthorizationMemory, memLoad_twoWordHashMem _ _ _ (by decide)
        (by change 96 ≤ _; rw [hs1]; omega),
        memLoad_twoWordHashMem user ⟨3⟩ ⟨64⟩ (by decide) (by change 96 ≤ mem.size; omega)]
    · simp only [onBehalfAllowed, henv, hself, false_or, authorizationWord, henv]
      rfl


end Benchmarks.Midnight
