import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.HealthStorage
import Benchmarks.Midnight.RuntimeBlocks_022
import Benchmarks.Midnight.RuntimeBlocks_023
import Benchmarks.Midnight.RuntimeBlocks_033

variable {fork : Ethereum.Fork}

/-! Liquidation's debt guard reads the original packed debt word and retains its gas budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

-- GENERALIZES midnight_block_5254_fallthrough with a monotone cost counter.
theorem liquidateDebtRead_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 x2 x3 x4 x5 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hdebt : low128 (solcSlotWordAt (x1 + ⟨2⟩) σ ee) ≠ ⟨0⟩)
    (h : RD fork midnightBytecode ee g s0 ⟨5254⟩ (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode ee g s0 ⟨5275⟩
      (x5 :: x0 :: x1 :: x2 :: x3 :: x4 :: solcSlotWordAt (x1 + ⟨2⟩) σ ee :: R)
      mem aw rdata σ k' C' := by
  have r1 := h.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc4, r4⟩ := RD.sloadMono r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap6 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.dup8 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 8411) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) (by
    rw [uint128Mask_computed]
    exact isZero_eq_zero_of_ne hdebt) (by evm_ov)
  have rf := RD.normalizePC (pc' := (UInt256.ofNat 5275)) r15 (by native_decide)
  exact ⟨_, _, by omega, rf⟩

theorem midnightLiquidateDebtGuard {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id borrower dl dp budgetRoot : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode ee g s0 ⟨5254⟩
      (UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)) ::
        positionSlot id borrower :: dp :: dl :: borrower ::
        UInt256.isZero (calldataWord ee.calldata 100) :: R) mem aw rdata σ k C) :
    let debtWord := solcSlotWordAt (positionSlot id borrower + ⟨2⟩) σ ee
    (low128 debtWord = ⟨0⟩ ∧ RDrev fork midnightBytecode g s0) ∨
    (low128 debtWord ≠ ⟨0⟩ ∧ ∃ k' C', TransferBudget budgetRoot credit mem aw C' ∧
      RD fork midnightBytecode ee g s0 ⟨5275⟩
        (UInt256.isZero (calldataWord ee.calldata 100) ::
          UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)) ::
          positionSlot id borrower :: dp :: dl :: borrower :: debtWord :: R)
        mem aw rdata σ k' C') := by
  dsimp only
  by_cases hd : low128 (solcSlotWordAt (positionSlot id borrower + ⟨2⟩) σ ee) = ⟨0⟩
  · obtain ⟨k1, C1, rd1⟩ := midnight_block_5254_taken hstack (by
      rw [uint128Mask_computed]
      change UInt256.isZero (low128 (solcSlotWordAt (positionSlot id borrower + ⟨2⟩) σ ee)) ≠ ⟨0⟩
      rw [hd]; decide) (by jump_dest) rd
    exact Or.inl ⟨hd, midnight_block_8411 (by
      simp only [midnight_block_5254_taken_stack, List.length_cons]; omega) rd1⟩
  · obtain ⟨k1, C1, hC1, rd1⟩ := liquidateDebtRead_mono hstack hd rd
    exact Or.inr ⟨hd, _, _, hb.mono hC1, rd1⟩

end Benchmarks.Midnight
