import Benchmarks.Midnight.LiquidateRcfQuotient
import Benchmarks.Midnight.LiquidateRcfStorageGas
import Benchmarks.Midnight.CheckedSubGas
import Benchmarks.Midnight.Uint128Arithmetic

/-! Read the current debt and compute the repayment cap used by the recovery-threshold check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateMaxRepaid {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw maxDebt lltv lif price pos : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨7014⟩ (maxDebt :: lltv :: lif :: price :: pos :: R)
      mem aw rdata σ k C) :
    let debt := low128 (solcSlotWordAt (pos + UInt256.ofNat 2) σ I)
    (¬ LiquidateMaxRepaidSafe debt maxDebt lif lltv ∧ RDrev midnightBytecode g s0) ∨
    (LiquidateMaxRepaidSafe debt maxDebt lif lltv ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨7134⟩
        (liquidateMaxRepaid debt maxDebt lif lltv :: lif :: price :: pos :: R)
        mem aw rdata σ k' C') := by
  dsimp only
  let debt := low128 (solcSlotWordAt (pos + UInt256.ofNat 2) σ I)
  obtain ⟨k1, C1, hc1, rd1⟩ := midnight_block_7014_mono (R := R) (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_7014_stack, uint128Mask_computed] at rd1
  change RD midnightBytecode I g s0 ⟨19447⟩
    (debt :: maxDebt :: ⟨7040⟩ :: ⟨7047⟩ :: lltv :: lif :: price :: pos :: R)
    mem aw rdata σ k1 C1 at rd1
  by_cases hd : maxDebt.toNat ≤ debt.toNat
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedSub_mono
      (by simp only [List.length_cons]; omega) hd (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_7040
      (R := price :: pos :: R) (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_7040_stack] at rd3
    by_cases hm : lif.toNat * lltv.toNat < UInt256.size
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedMul_mono
        (by simp only [List.length_cons]; omega) hm (by jump_dest) rd3
      have hshort : (UInt256.sub debt maxDebt).toNat < 2 ^ 128 := by
        rw [usub_toNat hd]
        have hb : debt.toNat < 2 ^ 128 := low128_lt _
        omega
      rcases midnightLiquidateRcfQuotient (R := lif :: price :: pos :: R)
        (by simp only [List.length_cons]; omega) hshort rd4 with
        ⟨hbad, hrev⟩ | ⟨hp, k5, C5, hc5, rd5⟩
      · exact Or.inl ⟨fun h ↦ hbad h.2.2, hrev⟩
      · exact Or.inr ⟨⟨hd, hm, hp⟩, k5, C5, by omega, rd5⟩
    · exact Or.inl ⟨fun h ↦ hm h.2.1, midnightCheckedMulRevert
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hm) rd3⟩
  · exact Or.inl ⟨fun h ↦ hd h.1, midnightCheckedSubRevert
      (by simp only [List.length_cons]; omega) (Nat.lt_of_not_ge hd) rd1⟩

end Benchmarks.Midnight
