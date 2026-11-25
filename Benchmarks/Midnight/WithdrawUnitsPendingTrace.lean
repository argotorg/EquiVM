import Benchmarks.Midnight.WithdrawUnitsWriteBlocksGas
import Benchmarks.Midnight.MulDivGas
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.PositionUpdateStorage

variable {fork : Ethereum.Fork}

/-! Checked proportional pending-fee reduction in a withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def WithdrawPendingSafe (w units : UInt256) : Prop :=
  let pending := UInt256.shiftRight w (UInt256.ofNat 128)
  let decrease := mulDivUp pending units (low128 w)
  MulDivUpSafe pending units (low128 w) ∧ decrease.toNat < 2^128 ∧
    decrease.toNat ≤ pending.toNat

theorem midnightWithdrawPendingReduction {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw w units slot marketSlot id user extra : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hperm : I.perm = true)
    (rd : RD fork midnightBytecode I g s0 ⟨4177⟩
      ([w, low128 w, units, slot, marketSlot, id, user, extra] ++ R) mem aw rdata σ k C) :
    let pending := UInt256.shiftRight w (UInt256.ofNat 128)
    let decrease := mulDivUp pending units (low128 w)
    (¬ WithdrawPendingSafe w units ∧ RDrev fork midnightBytecode g s0) ∨
    (WithdrawPendingSafe w units ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨4248⟩
        ([slot, marketSlot, id, user, decrease] ++ R) mem aw rdata
        (storeHigh128Accounts σ I slot (UInt256.sub pending decrease)) k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_4177 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_4177_stack] at rd1
  rcases midnightMulDivUp_mono (by simp only [List.length_cons]; omega)
      (by jump_dest) rd1 with ⟨hbad, hr⟩ | ⟨hsafe, k2, C2, hc2, rd2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, hr⟩
  · have rd3 := midnightBlocks.midnight_block_4204
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    by_cases h128 : (mulDivUp (UInt256.shiftRight w (UInt256.ofNat 128)) units
        (low128 w)).toNat < 2^128
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightToUint128_mono
        (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_4209
        (by omega) (by jump_dest) rd4
      simp only [midnightBlocks.midnight_block_4209_stack] at rd5
      by_cases hle : (mulDivUp (UInt256.shiftRight w (UInt256.ofNat 128)) units
          (low128 w)).toNat ≤ (UInt256.shiftRight w (UInt256.ofNat 128)).toNat
      · obtain ⟨k6, C6, hc6, rd6⟩ := midnightCheckedSub128_mono
          (by simp only [List.length_cons]; omega) (shiftRight128_lt _) h128 hle
          (by jump_dest) rd5
        obtain ⟨k7, C7, hc7, rd7⟩ := withdraw_units_block_4216_mono
          (by simp only [List.length_cons]; omega) hperm (by jump_dest) rd6
        simp only [midnightBlocks.midnight_block_4216_stack, uint128Mask_computed,
          u256_land_comm (UInt256.lnot uint128Mask), shiftLeft128_highMask,
          u256_land_comm uint128Mask, u256_lor_comm (UInt256.shiftLeft _ _)] at rd7
        exact Or.inr ⟨⟨hsafe, h128, hle⟩, _, _, by omega, rd7⟩
      · exact Or.inl ⟨fun h ↦ hle h.2.2,
          midnightCheckedSub128Revert (by simp only [List.length_cons]; omega)
            (shiftRight128_lt _) h128 (Nat.lt_of_not_ge hle) rd5⟩
    · exact Or.inl ⟨fun h ↦ h128 h.2.1,
        midnightToUint128Revert (by simp only [List.length_cons]; omega)
          (Nat.le_of_not_lt h128) rd3⟩

end Benchmarks.Midnight
