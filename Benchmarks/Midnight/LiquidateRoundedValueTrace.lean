import Benchmarks.Midnight.LiquidateCollateralValueTrace
import Benchmarks.Midnight.MaxLifGas
import Benchmarks.Midnight.LiquidateScaleRoutines

/-! Rounded-up collateral valuation before applying the liquidation incentive factor. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

def liquidateRoundedValue (collateral price : UInt256) : UInt256 :=
  mulDivUp collateral price liquidatePriceScale

theorem midnightLiquidateRoundedValue {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw maxDebt collateral cp badDebt reverseRep rep price savedPrice pos lltv cursor
      budgetRoot : UInt256} {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hlltv : memLoad (cp + UInt256.ofNat 32) mem = lltv)
    (hcursor : memLoad (cp + UInt256.ofNat 64) mem = cursor)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨8069⟩
      (maxDebt :: collateral :: cp :: badDebt :: reverseRep :: rep :: price :: savedPrice :: pos :: R)
      mem aw rdata σ k C) :
    (¬ MulDivUpSafe collateral price liquidatePriceScale ∧ RDrev midnightBytecode g s0) ∨
    (MulDivUpSafe collateral price liquidatePriceScale ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨24250⟩
        (lltv :: cursor :: ⟨8129⟩ :: liquidateRoundedValue collateral price :: badDebt ::
          reverseRep :: rep :: maxDebt :: savedPrice :: pos :: R)
        mem aw' rdata σ k' C') := by
  have rd1 := midnight_block_8069 (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnight_block_8069_stack] at rd1
  by_cases hm : collateral.toNat * price.toNat < UInt256.size
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedMul_mono
      (by simp only [List.length_cons]; omega) hm (by jump_dest) rd1
    have rd3 := midnight_block_8079
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    rcases midnightAddPriceScalePred
      (by simp only [List.length_cons]; omega) (by jump_dest) rd3 with
      ⟨ha, hrev⟩ | ⟨ha, k5, C5, hc5, rd5⟩
    · exact Or.inl ⟨fun h ↦ ha h.2.2, hrev⟩
    · have rd6 := midnight_block_8088
        (by simp only [List.length_cons]; omega) (by jump_dest) rd5
      have hb5 := hb.mono (show C ≤ C5 by omega)
      have hb6 := transferBudgetAt (root := budgetRoot) (credit := credit) rd6
        (by transfer_budget hb5)
      simp only [midnight_block_8088_stack, hlltv, hcursor] at rd6
      exact Or.inr ⟨⟨hm, by decide, ha⟩, _, _, _, hb6, rd6⟩
  · exact Or.inl ⟨fun h ↦ hm h.1, midnightCheckedMulRevert
      (by simp only [List.length_cons]; omega) (by omega) rd1⟩

end Benchmarks.Midnight
