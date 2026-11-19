import Benchmarks.Midnight.TakeBuyerDebtRead

/-! The buyer is updated when it has credit or the trade exceeds its existing debt. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def TakeBuyerNeedsUpdate (credit debt units : UInt256) : Prop :=
  credit ≠ ⟨0⟩ ∨ debt.toNat < units.toNat

instance (credit debt units : UInt256) : Decidable (TakeBuyerNeedsUpdate credit debt units) :=
  inferInstanceAs (Decidable (credit ≠ ⟨0⟩ ∨ debt.toNat < units.toNat))

def takeBuyerUpdatePC (credit debt units : UInt256) : UInt256 :=
  if TakeBuyerNeedsUpdate credit debt units then ⟨14492⟩ else ⟨11966⟩

theorem midnightTakeBuyerUpdateGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id buyer seller saved units : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hu : calldataWord I.calldata 68 = units)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨11960⟩
      ([UInt256.ofNat 14521, UInt256.isZero (takeHasCreditWord σ I id buyer),
        takeHasCreditWord σ I id buyer, positionSlot id seller, saved, positionSlot id buyer] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', MemoryFunding credit mem aw C' ∧
      RD midnightBytecode I g s0
        (takeBuyerUpdatePC (low128 (solcSlotWordAt (positionSlot id buyer) σ I))
          (low128 (solcSlotWordAt (positionSlot id buyer + ⟨2⟩) σ I)) units)
        (positionSlot id seller :: saved :: positionSlot id buyer :: R)
        mem aw rdata σ k' C' := by
  by_cases hz : low128 (solcSlotWordAt (positionSlot id buyer) σ I) = ⟨0⟩
  · have hw : takeHasCreditWord σ I id buyer = ⟨0⟩ := by
      simp only [takeHasCreditWord, hz]
      rfl
    rw [hw] at rd
    have rd1 := midnightBlocks.midnight_block_11960_taken
      (by change R.length + 4 + 2 ≤ 1024; omega) (by decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_11960_taken_stack] at rd1
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    obtain ⟨k2, C2, hC2, rd2⟩ := midnightTakeBuyerDebtRead_mono hstack rd1
    have ha2 := ha1.mono hC2
    rw [hu] at rd2
    by_cases hd : (low128 (solcSlotWordAt (positionSlot id buyer + ⟨2⟩) σ I)).toNat < units.toNat
    · have hp : TakeBuyerNeedsUpdate (low128 (solcSlotWordAt (positionSlot id buyer) σ I))
          (low128 (solcSlotWordAt (positionSlot id buyer + ⟨2⟩) σ I)) units := Or.inr hd
      have rd3 := midnightBlocks.midnight_block_11961_taken
        (by change R.length + 3 + 2 ≤ 1024; omega)
        (by rw [ugt_one hd]; decide) (by jump_dest) rd2
      simp only [midnightBlocks.midnight_block_11961_taken_stack] at rd3
      simp only [takeBuyerUpdatePC, if_pos hp]
      exact ⟨_, _, by memory_fund ha2, rd3⟩
    · have hp : ¬ TakeBuyerNeedsUpdate (low128 (solcSlotWordAt (positionSlot id buyer) σ I))
          (low128 (solcSlotWordAt (positionSlot id buyer + ⟨2⟩) σ I)) units :=
        fun h ↦ h.elim (fun hn ↦ hn hz) hd
      have rd3 := midnightBlocks.midnight_block_11961_fallthrough
        (by change R.length + 3 + 2 ≤ 1024; omega) (ugt_zero (by omega)) rd2
      simp only [midnightBlocks.midnight_block_11961_fallthrough_stack] at rd3
      simp only [takeBuyerUpdatePC, if_neg hp]
      exact ⟨_, _, by memory_fund ha2, rd3⟩
  · have hw : takeHasCreditWord σ I id buyer = ⟨1⟩ := by
      rw [takeHasCreditWord, isZero_eq_zero_of_ne hz]
      rfl
    rw [hw] at rd
    have hp : TakeBuyerNeedsUpdate (low128 (solcSlotWordAt (positionSlot id buyer) σ I))
        (low128 (solcSlotWordAt (positionSlot id buyer + ⟨2⟩) σ I)) units := Or.inl hz
    have rd1 := midnightBlocks.midnight_block_11960_fallthrough
      (by change R.length + 4 + 2 ≤ 1024; omega) (by decide) rd
    simp only [midnightBlocks.midnight_block_11960_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_11961_taken
      (by change R.length + 3 + 2 ≤ 1024; omega) (by decide) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_11961_taken_stack] at rd2
    simp only [takeBuyerUpdatePC, if_pos hp]
    exact ⟨_, _, by memory_fund ha, rd2⟩

end Benchmarks.Midnight
