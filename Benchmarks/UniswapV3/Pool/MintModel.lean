import Benchmarks.UniswapV3.Pool.PoolEntrySource
import Benchmarks.UniswapV3.Pool.ModifyPositionModel
import Benchmarks.UniswapV3.Pool.SafeCast128Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure MintArgs where
  recipient : AccountAddress
  lower : Int
  upper : Int
  amount : UInt256
  data : ByteArray

def MintArgs.Fits (a : MintArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.lower ∧ a.lower < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.upper ∧ a.upper < 2 ^ 23) ∧ a.amount.toNat < 2 ^ 128

def mintLocals (a : MintArgs) : Store :=
  (((((∅ : Store).insert "recipient" (.address a.recipient)).insert "tickLower" (.int a.lower)).insert
    "tickUpper" (.int a.upper)).insert "amount" (.int (Int.ofNat a.amount.toNat))).insert "data" (.bytes a.data)

def mintFrame (v : UniswapV3PoolImmutables) (a : MintArgs) : Frame :=
  {contract := contract, locals := mintLocals a, immutables := immStore v}

def mintInitFrame (v : UniswapV3PoolImmutables) (a : MintArgs) : Frame :=
  poolAmountsFrame (mintLocals a) (immStore v)

def mintCastFrame (v : UniswapV3PoolImmutables) (a : MintArgs) : Frame :=
  resumeAfterInternalCall (mintInitFrame v a) "__c0" (some [.int (Int.ofNat a.amount.toNat)])

def mintModifyArgs (a : MintArgs) : ModifyPositionArgs :=
  {owner := a.recipient, lower := a.lower, upper := a.upper, delta := Int.ofNat a.amount.toNat}

def mintCastExprs : List Expr :=
  [.cast (.var "amount") (.elem (.int (.sint ⟨256, by decide⟩)))]

def mintModifyExprs : List Expr :=
  [.structLit "ModifyPositionParams" [("owner", .var "recipient"), ("tickLower", .var "tickLower"),
    ("tickUpper", .var "tickUpper"), ("liquidityDelta", .var "__c0")]]

theorem mintModifyArgs_fits (a : MintArgs) (ha : a.Fits)
    (hv : safeCast128Valid (Int.ofNat a.amount.toNat)) : (mintModifyArgs a).Fits :=
  ⟨ha.1, ha.2.1, (safeCast128Valid_iff _).mp hv⟩

macro "mint_prefix_get" : tactic =>
  `(tactic| (simp only [mintCastFrame, mintInitFrame, poolAmountsFrame, mintFrame, mintLocals,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty]; rfl))

end Benchmarks.UniswapV3.Pool
