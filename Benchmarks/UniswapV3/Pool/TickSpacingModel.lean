import Benchmarks.UniswapV3.Pool.SnapshotArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: both operands of a fixed-width subtraction may be normalized early.
theorem normalizeInt_sub_both (ty : ABI.IntType) (i j : Int) :
    normalizeInt ty (normalizeInt ty i - normalizeInt ty j) = normalizeInt ty (i - j) := by
  have hr : (normalizeInt ty i - normalizeInt ty j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) =
      (i - j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) := by
    rw [Int.sub_emod, normalizeInt_residue, normalizeInt_residue, ← Int.sub_emod]
  cases ty with
  | uint width => exact hr
  | sint width => simp only [normalizeInt, IntType.bitWidth] at hr ⊢; rw [hr]

def spacingMinProduct (spacing : Int) : Int := (-887272 : Int).tdiv spacing * spacing

def spacingMaxProduct (spacing : Int) : Int := (887272 : Int).tdiv spacing * spacing

def spacingMin (spacing : Int) : Int := normalizeInt (.sint ⟨24, by decide⟩) (spacingMinProduct spacing)

def spacingMax (spacing : Int) : Int := normalizeInt (.sint ⟨24, by decide⟩) (spacingMaxProduct spacing)

def spacingDelta (spacing : Int) : Int :=
  normalizeInt (.sint ⟨24, by decide⟩) (spacingMax spacing - spacingMin spacing)

def spacingCount (spacing : Int) : Int :=
  normalizeInt (.uint ⟨24, by decide⟩)
    (normalizeInt (.uint ⟨24, by decide⟩) ((spacingDelta spacing).tdiv spacing) + 1)

def spacingLiquidity (spacing : Int) : Int := (2 ^ 128 - 1) / spacingCount spacing

theorem spacingCount_bounds (spacing : Int) :
    0 ≤ spacingCount spacing ∧ spacingCount spacing < 2 ^ 24 := by
  unfold spacingCount normalizeInt
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem spacingLiquidity_bounds (spacing : Int) :
    0 ≤ spacingLiquidity spacing ∧ spacingLiquidity spacing < 2 ^ 128 := by
  have hc := spacingCount_bounds spacing
  unfold spacingLiquidity
  constructor
  · exact Int.ediv_nonneg (by decide) hc.1
  · have h := Int.ediv_le_self (spacingCount spacing) (show 0 ≤ (2 ^ 128 - 1 : Int) by decide)
    omega

def tickSpacingFunction : FunctionDecl := contract.functions[27]!

theorem tickSpacingLookup :
    lookupCallable? contract "Tick_tickSpacingToMaxLiquidityPerTick" =
      some tickSpacingFunction.toCallable := rfl

def tickSpacingLocals (spacing : Int) : Store :=
  (∅ : Store).insert "tickSpacing" (.int spacing)

def tickSpacingFrame (imms : Store) (spacing : Int) : Frame :=
  {contract := contract, locals := tickSpacingLocals spacing, immutables := imms}

theorem tickSpacingBind (spacing : Int) :
    bindParams? tickSpacingFunction.params [.int spacing] = some (tickSpacingLocals spacing) := rfl

end Benchmarks.UniswapV3.Pool
