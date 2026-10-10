import Benchmarks.UniswapV3.Pool.ModifyPositionModel
import Benchmarks.UniswapV3.Pool.SafeCast128Source
import Benchmarks.UniswapV3.Pool.Slot0Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure BurnArgs where
  lower : Int
  upper : Int
  amount : UInt256

def BurnArgs.Fits (a : BurnArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.lower ∧ a.lower < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.upper ∧ a.upper < 2 ^ 23) ∧ a.amount.toNat < 2 ^ 128

def burnLocals (a : BurnArgs) : Store :=
  (((∅ : Store).insert "tickLower" (.int a.lower)).insert "tickUpper" (.int a.upper)).insert
    "amount" (.int (Int.ofNat a.amount.toNat))

def burnFrame (v : UniswapV3PoolImmutables) (a : BurnArgs) : Frame :=
  {contract := contract, locals := burnLocals a, immutables := immStore v}

def burnInitFrame (v : UniswapV3PoolImmutables) (a : BurnArgs) : Frame :=
  let locals := ((burnLocals a).insert "amount0" (.int 0)).insert "amount1" (.int 0)
  {contract := contract, locals := locals, immutables := immStore v}

def burnCastFrame (v : UniswapV3PoolImmutables) (a : BurnArgs) : Frame :=
  resumeAfterInternalCall (burnInitFrame v a) "__c0" (some [.int (Int.ofNat a.amount.toNat)])

def burnModifyArgs (a : BurnArgs) (evm : EVM.State) : ModifyPositionArgs :=
  {owner := evm.executionEnv.source, lower := a.lower, upper := a.upper,
    delta := normalizeInt (.sint ⟨128, by decide⟩) (0 - Int.ofNat a.amount.toNat)}

def burnCastExprs : List Expr :=
  [.cast (.var "amount") (.elem (.int (.sint ⟨256, by decide⟩)))]

def burnModifyExprs : List Expr :=
  [.structLit "ModifyPositionParams" [("owner", .env .caller), ("tickLower", .var "tickLower"),
    ("tickUpper", .var "tickUpper"), ("liquidityDelta",
      .cast (.binary .sub (.intLit 0) (.var "__c0")) (.elem (.int (.sint ⟨128, by decide⟩))))]]

theorem burnModifyArgs_fits (a : BurnArgs) (evm : EVM.State) (ha : a.Fits) :
    (burnModifyArgs a evm).Fits := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  exact normalizeSint_bounds ⟨128, by decide⟩ _

macro "burn_prefix_get" : tactic =>
  `(tactic| (simp only [burnCastFrame, burnInitFrame, burnFrame, burnLocals, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

end Benchmarks.UniswapV3.Pool
