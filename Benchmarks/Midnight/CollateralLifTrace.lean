import Benchmarks.Midnight.MaxLifTrace
import Benchmarks.Midnight.RuntimeBlocks_080

/-! The liquidation-factor restrictions for a newly initialized collateral. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def CollateralLifSafe (lltv cursor : UInt256) : Prop :=
  MaxLifSafe lltv cursor ∧ (maxLif lltv cursor).toNat ≤ 2000000000000000000 ∧
    (lltv = lifScale ∨
      (UInt256.mul lltv (maxLif lltv cursor)).toNat ≤ 999000000000000000000000000000000000)

theorem collateralLifProductBound {lltv cursor : UInt256} (hs : MaxLifSafe lltv cursor)
    (hb : (maxLif lltv cursor).toNat ≤ 2000000000000000000) :
    lltv.toNat * (maxLif lltv cursor).toNat < UInt256.size := by
  calc _ ≤ 1000000000000000000 * 2000000000000000000 := Nat.mul_le_mul hs.1 hb
    _ < UInt256.size := by decide

set_option maxRecDepth 2000000 in
theorem midnightCollateralLif {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw lltv cursor : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨20957⟩ (cursor :: lltv :: R) mem aw rdata σ k C) :
    (¬ CollateralLifSafe lltv cursor ∧ RDrev midnightBytecode g s0) ∨
    (CollateralLifSafe lltv cursor ∧ ∃ k' C', RD midnightBytecode I g s0 ⟨21008⟩ R
      mem aw rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_20957 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_20957_stack] at rd1
  rcases midnightMaxLif (by simp only [List.length_cons]; omega) (by jump_dest) rd1 with
    ⟨hbad, hr⟩ | ⟨hs, k2, C2, rd2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, hr⟩
  · by_cases hb : (maxLif lltv cursor).toNat ≤ 2000000000000000000
    · have rd3 := midnightBlocks.midnight_block_20966_fallthrough (by
        simp only [List.length_cons]; omega) (ugt_zero hb) rd2
      by_cases he : lltv = lifScale
      · have hc : UInt256.eq lltv (UInt256.ofNat 1000000000000000000) = ⟨1⟩ := by
          rw [he]; exact uInt256_eq_self _
        have rd4 := midnightBlocks.midnight_block_20982_fallthrough (by omega)
          (by rw [hc]; rfl) rd3
        simp only [midnightBlocks.midnight_block_20982_fallthrough_stack, hc] at rd4
        have rd5 := midnightBlocks.midnight_block_21000_fallthrough (by omega) rfl rd4
        exact Or.inr ⟨⟨hs, hb, Or.inl he⟩, _, _, rd5⟩
      · have hc : UInt256.eq lltv (UInt256.ofNat 1000000000000000000) = ⟨0⟩ := u256_eq_of_ne he
        have rd4 := midnightBlocks.midnight_block_20982_taken (by omega)
          (by rw [hc]; decide) (by jump_dest) rd3
        simp only [midnightBlocks.midnight_block_20982_taken_stack, hc] at rd4
        have rd5 := midnightBlocks.midnight_block_21033 (by omega) (by jump_dest) rd4
        simp only [midnightBlocks.midnight_block_21033_stack] at rd5
        obtain ⟨k6, C6, rd6⟩ := midnightCheckedMul (by simp only [List.length_cons]; omega)
          (collateralLifProductBound hs hb) (by jump_dest) rd5
        have rd7 := midnightBlocks.midnight_block_21061 (by omega) (by jump_dest) rd6
        simp only [midnightBlocks.midnight_block_21061_stack] at rd7
        by_cases hp : (UInt256.mul lltv (maxLif lltv cursor)).toNat ≤
            999000000000000000000000000000000000
        · have hg : UInt256.gt (UInt256.mul lltv (maxLif lltv cursor))
              (UInt256.ofNat 999000000000000000000000000000000000) = ⟨0⟩ := ugt_zero hp
          have rd8 := midnightBlocks.midnight_block_21000_fallthrough (by omega)
            (by rw [hg]; rfl) rd7
          exact Or.inr ⟨⟨hs, hb, Or.inr hp⟩, _, _, rd8⟩
        · left
          refine ⟨fun h ↦ h.2.2.elim he hp, ?_⟩
          have hg : UInt256.gt (UInt256.mul lltv (maxLif lltv cursor))
              (UInt256.ofNat 999000000000000000000000000000000000) = ⟨1⟩ :=
            ugt_one (Nat.lt_of_not_ge hp)
          have rd8 := midnightBlocks.midnight_block_21000_taken (by omega)
            (by rw [hg]; decide) (by jump_dest) rd7
          exact midnightBlocks.midnight_block_21018 (by
            simp only [midnightBlocks.midnight_block_21000_taken_stack]; omega) rd8
    · left
      refine ⟨fun h ↦ hb h.2.1, ?_⟩
      have hg : UInt256.gt (maxLif lltv cursor) (UInt256.ofNat 2000000000000000000) = ⟨1⟩ :=
        ugt_one (Nat.lt_of_not_ge hb)
      have rd3 := midnightBlocks.midnight_block_20966_taken (by
        simp only [List.length_cons]; omega) (by rw [hg]; decide) (by jump_dest) rd2
      exact midnightBlocks.midnight_block_21070 (by simp only [List.length_cons]; omega) rd3

end Benchmarks.Midnight
