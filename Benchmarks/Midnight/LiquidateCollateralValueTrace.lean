import Benchmarks.Midnight.HealthArithmeticBudget
import Benchmarks.Midnight.RuntimeBlocks_031

/-! The collateral-value products and debt-capacity sum in a liquidation iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

-- GENERALIZES the generated storage-read summary by retaining the cost lower bound.
theorem liquidate_block_7988_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 20413) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 7988) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 20413) (midnight_block_7988_stack (ee := ee) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) mem aw rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcLoad, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 8015) (by native_decide) (by evm_ov)
  have r16 := r15.dup8 (by native_decide) (by evm_ov)
  have r17 := r16.dup4 (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 20413) (by native_decide) (by evm_ov)
  have r19 := r18.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20413)) r19 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

theorem midnightLiquidateCollateralValue {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw maxDebt cp badDebt reverseRep rep price savedPrice pos bitmap lltv budgetRoot : UInt256}
    {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hfork : I.fork ≥ .osaka)
    (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
    (hi : (bitmapMsb bitmap).toNat < 128)
    (hlltv : memLoad (cp + UInt256.ofNat 32) mem = lltv)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7967⟩
      (maxDebt :: cp :: badDebt :: reverseRep :: rep :: price :: savedPrice :: pos :: R)
      mem aw rdata σ k C) :
    let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I)
      (pos + ⟨3⟩) (bitmapMsb bitmap)
    (¬ HealthArithmeticSafe collateral price lltv maxDebt ∧ RDrev midnightBytecode g s0) ∨
    (HealthArithmeticSafe collateral price lltv maxDebt ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨8069⟩
        ((maxDebt + healthCollateralCapacity collateral price lltv) :: collateral :: cp ::
          badDebt :: reverseRep :: rep :: price :: savedPrice :: pos :: R)
        mem aw' rdata σ k' C') := by
  dsimp only
  let index := bitmapMsb bitmap
  let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I) (pos + ⟨3⟩) index
  have rd1 := midnight_block_7967 (by omega) hfork (by jump_dest) rd
  simp only [midnight_block_7967_stack, hbitmap] at rd1
  have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1
    (by transfer_budget hb)
  obtain ⟨k2, C2, hc2, rd2⟩ := midnightUint128ArrayLocation_mono
    (by simp only [List.length_cons]; omega) hi (by jump_dest) rd1
  obtain ⟨k3, C3, hc3, rd3⟩ := liquidate_block_7988_mono
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  simp only [midnight_block_7988_stack, uint128Mask_computed,
    (uint128ArrayIndexFacts (bitmapMsb bitmap) hi).2.2,
    u256_land_comm (UInt256.ofNat (2^128-1))] at rd3
  change RD midnightBytecode I g s0 ⟨20413⟩
    (collateral :: price :: ⟨8015⟩ :: maxDebt :: collateral :: cp :: badDebt :: reverseRep ::
      rep :: price :: savedPrice :: pos :: R) mem _ rdata σ k3 C3 at rd3
  have hb3 := hb1.mono (show _ ≤ C3 by omega)
  by_cases hm : collateral.toNat * price.toNat < UInt256.size
  · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedMul_mono
      (by simp only [List.length_cons]; omega) hm (by jump_dest) rd3
    have rd5 := midnight_block_8015
      (by simp only [List.length_cons]; omega) (by jump_dest) rd4
    simp only [midnight_block_8015_stack, hlltv] at rd5
    have hb4 := hb3.mono hc4
    have hb5 := transferBudgetAt (root := budgetRoot) (credit := credit) rd5
      (by transfer_budget hb4)
    by_cases hm2 : (healthPriceValue collateral price).toNat * lltv.toNat < UInt256.size
    · obtain ⟨k6, C6, hc6, rd6⟩ := midnightCheckedMul_mono
        (by simp only [List.length_cons]; omega) hm2 (by jump_dest) rd5
      have rd7 := midnight_block_8047
        (by simp only [List.length_cons]; omega) (by jump_dest) rd6
      simp only [midnight_block_8047_stack] at rd7
      by_cases ha : maxDebt.toNat + (healthCollateralCapacity collateral price lltv).toNat <
          UInt256.size
      · obtain ⟨k8, C8, hc8, rd8⟩ := midnightCheckedAdd_mono
          (by simp only [List.length_cons]; omega) ha (by jump_dest) rd7
        exact Or.inr ⟨⟨hm, hm2, ha⟩, _, _, _, hb5.mono (by omega), rd8⟩
      · exact Or.inl ⟨fun h ↦ ha h.2.2, midnightCheckedAddRevert
          (a := maxDebt) (b := healthCollateralCapacity collateral price lltv)
          (by simp only [List.length_cons]; omega) (by omega) rd7⟩
    · exact Or.inl ⟨fun h ↦ hm2 h.2.1, midnightCheckedMulRevert
        (a := healthPriceValue collateral price) (b := lltv)
        (by simp only [List.length_cons]; omega) (by omega) rd5⟩
  · exact Or.inl ⟨fun h ↦ hm h.1, midnightCheckedMulRevert
      (by simp only [List.length_cons]; omega) (by omega) rd3⟩

end Benchmarks.Midnight
