import Benchmarks.Midnight.LiquidateRoundedValueTrace
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.RuntimeBlocks_032
import Benchmarks.Midnight.RuntimeBlocks_027

/-! Checked rounded division by the liquidation incentive factor. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem midnightLiquidateRecoveryDivision {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value lif : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨8129⟩ (lif :: value :: R) mem aw rdata σ k C) :
    (¬ MulDivUpSafe value lifScale lif ∧ RDrev midnightBytecode g s0) ∨
    (MulDivUpSafe value lifScale lif ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨8165⟩ (mulDivUp value lifScale lif :: R)
        mem aw rdata σ k' C') := by
  have rd1 := midnight_block_8129 (by omega) (by jump_dest) rd
  rcases midnightMulLifScale (by simp only [List.length_cons]; omega)
    (by jump_dest) rd1 with ⟨hm, hrev⟩ | ⟨hm, k3, C3, hc3, rd3⟩
  · exact Or.inl ⟨fun h ↦ hm h.1, hrev⟩
  · by_cases hp : 0 < lif.toNat
    · have hpred : (UInt256.sub lif ⟨1⟩).toNat = lif.toNat - 1 := usub_toNat hp
      have hguard : UInt256.gt (lif + UInt256.lnot ⟨0⟩) lif = ⟨0⟩ := by
        rw [u256_add_lnot_zero_eq_sub_one]
        exact ugt_zero (by rw [hpred]; omega)
      have rd4 := midnight_block_8139_fallthrough (by omega) hguard rd3
      simp only [midnight_block_8139_fallthrough_stack, u256_add_lnot_zero_eq_sub_one] at rd4
      have rd5 := midnight_block_8153 (by omega) (by jump_dest) rd4
      simp only [midnight_block_8153_stack] at rd5
      by_cases ha : (UInt256.mul value lifScale).toNat + (UInt256.sub lif ⟨1⟩).toNat < UInt256.size
      · obtain ⟨k6, C6, hc6, rd6⟩ := midnightCheckedAdd_mono
          (by simp only [List.length_cons]; omega) ha (by jump_dest) rd5
        have rd7 := midnight_block_6721
          (by simp only [List.length_cons]; omega) (by jump_dest) rd6
        have hnz : lif ≠ ⟨0⟩ := by intro hz; rw [hz] at hp; contradiction
        obtain ⟨k8, C8, hc8, rd8⟩ := midnightCheckedDiv_mono
          (by omega) hnz (by jump_dest) rd7
        exact Or.inr ⟨⟨hm, hp, ha⟩, _, _, by omega, rd8⟩
      · exact Or.inl ⟨fun h ↦ ha h.2.2, midnightCheckedAddRevert
          (a := UInt256.mul value lifScale) (b := UInt256.sub lif ⟨1⟩)
          (by simp only [List.length_cons]; omega) (by omega) rd5⟩
    · have hz : lif = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
      have hguard : UInt256.gt (lif + UInt256.lnot ⟨0⟩) lif ≠ ⟨0⟩ := by rw [hz]; decide +kernel
      have rd4 := midnight_block_8139_taken (by omega) hguard (by jump_dest) rd3
      exact Or.inl ⟨fun h ↦ hp h.2.1, midnight_block_7276
        (by simp only [midnight_block_8139_taken_stack, List.length_cons]; omega) rd4⟩

end Benchmarks.Midnight
