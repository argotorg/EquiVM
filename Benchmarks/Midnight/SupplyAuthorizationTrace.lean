import Benchmarks.Midnight.RuntimeBlocks_064
import Benchmarks.Midnight.RuntimeBlocks_065
import Benchmarks.Midnight.Authorization
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.MemoryAccounting
import Benchmarks.Midnight.MarketBytesMemory
import Benchmarks.Midnight.PositionUpdateMemory

/-! The collateral-supply authorization guard, retaining its decoded memory and gas accounting. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem supplyAuthorizationRead_accounted {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 17015) = true)
    (ha : MemoryAccounting mem aw C)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17559) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), MemoryAccounting (midnight_block_17559_memory (ee := ee) (mem := mem) (x1 := x1)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 17015) (midnight_block_17559_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (R := R)) (midnight_block_17559_memory (ee := ee) (mem := mem) (x1 := x1)) (M (M (M (M (M (M aw (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 64)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.push0 (by native_decide) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r15 := r14.shl (by native_decide) (by evm_ov)
  have r16 := r15.sub (by native_decide) (by evm_ov)
  have r17 := r16.caller (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push0 (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r25 := r24.push0 (by native_decide) (by evm_ov)
  have r26 := RD.genKeccak256 r25 (by native_decide) (by evm_ov)
  have ha26 := memoryAccountingAt r26 (by memory_account ha)
  obtain ⟨_, _, hc27, r27⟩ := RD.sloadMono r26 (by native_decide) (by evm_ov)
  have ha27 := memoryAccountingAt r27 ⟨by
    have hp := ha26.paid
    unfold MemoryPaid at hp ⊢
    omega, ha26.covered⟩
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 17015) (by native_decide) (by evm_ov)
  have r30 := r29.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 17015)) r30 (by native_decide)
  have haFinal := memoryAccountingAt rFinal (by memory_account ha27)
  exact ⟨_, _, haFinal, rFinal⟩


def supplyAuthorizationMemory (mem : ByteArray) (I : ExecutionEnv) (user : UInt256) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (solcMappingSlot ⟨3⟩ user)
    (twoWordHashMem user ⟨3⟩ mem)

theorem supplyAuthorizationMemory_size (mem : ByteArray) (I : ExecutionEnv) (user : UInt256)
    (hs : 64 ≤ mem.size) : (supplyAuthorizationMemory mem I user).size = mem.size := by
  rw [supplyAuthorizationMemory, twoWordHashMem_size_of_ge_64 _ _ (by
    rw [twoWordHashMem_size_of_ge_64 _ _ hs]; exact hs),
    twoWordHashMem_size_of_ge_64 _ _ hs]

theorem supplyAuthorizationGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw user : UInt256} {k C : Nat} {R : List UInt256}
    (evm : EVM.State) (henv : evm.executionEnv = I)
    (hstack : R.length + 6 ≤ 1024) (hmem : 96 ≤ mem.size)
    (hcanon : user.toNat < EVM.addressModulus) (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨17004⟩ (user :: solcAddrMask :: R)
      mem aw rdata evm.accountMap k C) :
    (¬ onBehalfAllowed evm user ∧ RDrev midnightBytecode g s0) ∨
    (onBehalfAllowed evm user ∧ ∃ mem' aw' k' C',
      MemoryPrefix mem mem' mem.size ∧ mem'.size = mem.size ∧
      memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem ∧ MemoryAccounting mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨17021⟩ (user :: R) mem' aw' rdata evm.accountMap k' C') := by
  have finish {mem' aw' k' C' check}
      (hp : MemoryPrefix mem mem' mem.size) (hs : mem'.size = mem.size)
      (hf : memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem)
      (ha' : MemoryAccounting mem' aw' C')
      (hc : check ≠ ⟨0⟩ ↔ onBehalfAllowed evm user)
      (rd' : RD midnightBytecode I g s0 ⟨17015⟩ (check :: user :: R)
        mem' aw' rdata evm.accountMap k' C') :
      (¬ onBehalfAllowed evm user ∧ RDrev midnightBytecode g s0) ∨
      (onBehalfAllowed evm user ∧ ∃ mem' aw' k' C',
        MemoryPrefix mem mem' mem.size ∧ mem'.size = mem.size ∧
        memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem ∧ MemoryAccounting mem' aw' C' ∧
        RD midnightBytecode I g s0 ⟨17021⟩ (user :: R) mem' aw' rdata evm.accountMap k' C') := by
    by_cases hz : check = ⟨0⟩
    · have rr := midnight_block_17015_taken (by simp only [List.length_cons]; omega)
        (by rw [hz]; decide) (by jump_dest) rd'
      exact Or.inl ⟨fun h ↦ (hc.mpr h) hz, midnight_block_17545 (by
        simp only [midnight_block_17015_taken_stack, List.length_cons]; omega) rr⟩
    · have rr := midnight_block_17015_fallthrough (by simp only [List.length_cons]; omega)
        (isZero_eq_zero_of_ne hz) rd'
      exact Or.inr ⟨hc.mp hz, _, _, _, _, hp, hs, hf,
        by memory_account ha', rr⟩
  by_cases hself : user = solcSourceWord I
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨1⟩ := by
      rw [hself, uInt256_eq_self]
    have rd1 := midnight_block_17004_fallthrough (by omega)
      (by rw [solcAddrMask_clean hcanon]; change UInt256.isZero (UInt256.eq user (solcSourceWord I)) = _
          rw [heq]; rfl) rd
    simp only [midnight_block_17004_fallthrough_stack, solcAddrMask_clean hcanon] at rd1
    apply finish (MemoryPrefix.refl _ _) rfl rfl (by memory_account ha) _ rd1
    change UInt256.eq user (solcSourceWord I) ≠ ⟨0⟩ ↔ _
    simp only [onBehalfAllowed, henv, hself, true_or, uInt256_eq_self]
    decide
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨0⟩ := u256_eq_of_ne hself
    have rd1 := midnight_block_17004_taken (by omega)
      (by rw [solcAddrMask_clean hcanon]; change UInt256.isZero (UInt256.eq user (solcSourceWord I)) ≠ _
          rw [heq]; decide) (by jump_dest) rd
    simp only [midnight_block_17004_taken_stack, solcAddrMask_clean hcanon] at rd1
    obtain ⟨k2, C2, ha2, rd2⟩ := supplyAuthorizationRead_accounted
      (by omega) (by jump_dest) (by memory_account ha) rd1
    have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem user (UInt256.ofNat 3) mem) =
        solcMappingSlot ⟨3⟩ user := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
    have hs1 : (twoWordHashMem user ⟨3⟩ mem).size = mem.size :=
      twoWordHashMem_size_of_ge_64 _ _ (by omega)
    have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (supplyAuthorizationMemory mem I user) =
        authorizationSlot user (solcSourceWord I) :=
      twoWordHashMem_mapSlot_of_ge64 _ _ (by rw [hs1]; omega)
    simp only [midnight_block_17559_stack, midnight_block_17559_memory,
      addressMask_computed, solcAddrMask_clean (solcSourceWord_canonical I),
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
      ] at rd2 ha2
    rw [hh1] at rd2 ha2
    change RD midnightBytecode I g s0 ⟨17015⟩
      (UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (supplyAuthorizationMemory mem I user)) evm.accountMap I) ⟨255⟩ :: user :: R)
      (supplyAuthorizationMemory mem I user) _ rdata evm.accountMap k2 C2 at rd2
    rw [hh2] at rd2
    apply finish ((twoWordHashMem_prefix mem user ⟨3⟩ mem.size).trans
      (twoWordHashMem_prefix _ _ _ mem.size))
      (supplyAuthorizationMemory_size mem I user (by omega)) ?_ ha2 ?_ rd2
    · change memLoad ⟨64⟩ (supplyAuthorizationMemory mem I user) = memLoad ⟨64⟩ mem
      rw [supplyAuthorizationMemory, memLoad_twoWordHashMem _ _ _ (by decide)
        (by change 96 ≤ _; rw [hs1]; exact hmem),
        memLoad_twoWordHashMem user ⟨3⟩ ⟨64⟩ (by decide) hmem]
    · simp only [onBehalfAllowed, henv, hself, false_or, authorizationWord, henv]
      rfl

end Benchmarks.Midnight
