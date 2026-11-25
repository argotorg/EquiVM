import Benchmarks.Midnight.LiquidateRecoverable
import Benchmarks.Midnight.LiquidateRcfStorageGas
import Benchmarks.Midnight.ArrayIndexGas
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.RuntimeBlocks_027

variable {fork : Ethereum.Fork}

/-! Read a packed collateral balance and compute how much debt it can repay. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateRecoverable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price lif cap flag pos index : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (hi : calldataWord I.calldata 36 = index)
    (rd : RD fork midnightBytecode I g s0 ⟨7188⟩ (price :: lif :: cap :: flag :: pos :: R)
      mem aw rdata σ k C) :
    let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I) (pos + ⟨3⟩) index
    (¬ (index.toNat < 128 ∧ LiquidateRecoverableSafe collateral price lif) ∧
      RDrev fork midnightBytecode g s0) ∨
    (index.toNat < 128 ∧ LiquidateRecoverableSafe collateral price lif ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨7253⟩
        (liquidateRecoverable collateral price lif :: cap :: pos :: R) mem aw rdata σ k' C') := by
  dsimp only
  let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I) (pos + ⟨3⟩) index
  have rd1 := midnightBlocks.midnight_block_7188 (R := R) (by omega) (by jump_dest) rd
  have hi' : uInt256OfByteArray (I.calldata.readBytes 36 32) = index := hi
  simp only [midnightBlocks.midnight_block_7188_stack,
    show (UInt256.ofNat 36).toNat = 36 from rfl, hi', uint128Mask_computed] at rd1
  by_cases hidx : index.toNat < 128
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightUint128ArrayLocation_mono
      (by simp only [List.length_cons]; omega) hidx (by jump_dest) rd1
    obtain ⟨k3, C3, hc3, rd3⟩ := midnight_block_7240_mono
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_7240_stack,
      (uint128ArrayIndexFacts index hidx).2.2] at rd3
    change RD fork midnightBytecode I g s0 ⟨20413⟩
      (collateral :: price :: ⟨6687⟩ :: liquidatePriceScale :: ⟨6721⟩ :: lif ::
        ⟨7253⟩ :: cap :: pos :: R) mem aw rdata σ k3 C3 at rd3
    by_cases hm : collateral.toNat * price.toNat < UInt256.size
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightCheckedMul_mono
        (by simp only [List.length_cons]; omega) hm (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_6687
        (by simp only [List.length_cons]; omega) (by jump_dest) rd4
      simp only [midnightBlocks.midnight_block_6687_stack] at rd5
      rcases midnightMulLifScale (by simp only [List.length_cons]; omega) (by jump_dest) rd5 with
        ⟨hbad, hrev⟩ | ⟨hscaled, k6, C6, hc6, rd6⟩
      · exact Or.inl ⟨fun h ↦ hbad h.2.2.1, hrev⟩
      · have rd7 := midnightBlocks.midnight_block_6721
          (by simp only [List.length_cons]; omega) (by jump_dest) rd6
        by_cases hnz : lif ≠ ⟨0⟩
        · obtain ⟨k8, C8, hc8, rd8⟩ := midnightCheckedDiv_mono
            (by simp only [List.length_cons]; omega) hnz (by jump_dest) rd7
          exact Or.inr ⟨hidx, ⟨hm, hscaled, hnz⟩, k8, C8, by omega, rd8⟩
        · have hz : lif = ⟨0⟩ := not_not.mp hnz
          rw [hz] at rd7
          exact Or.inl ⟨fun h ↦ h.2.2.2 hz, midnightCheckedDivRevert
            (by simp only [List.length_cons]; omega) rd7⟩
    · exact Or.inl ⟨fun h ↦ hm h.2.1, midnightCheckedMulRevert
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hm) rd3⟩
  · exact Or.inl ⟨fun h ↦ hidx h.1, midnightUint128ArrayLocationRevert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hidx) rd1⟩

end Benchmarks.Midnight
