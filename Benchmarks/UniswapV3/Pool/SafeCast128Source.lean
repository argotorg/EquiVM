import Benchmarks.UniswapV3.Pool.SourceSignedBits
import Benchmarks.UniswapV3.Pool.CheckedCastSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000
attribute [local instance] Classical.propDecidable

def safeCast128Function : FunctionDecl := contract.functions[10]!

theorem safeCast128Lookup :
    lookupCallable? contract "SafeCast_toInt128" = some safeCast128Function.toCallable := rfl

def safeCast128Locals (y : Int) : Store := (∅ : Store).insert "y" (.int y)

def safeCast128Frame (imms : Store) (y : Int) : Frame :=
  {contract := contract, locals := safeCast128Locals y, immutables := imms}

def safeCast128ZeroFrame (imms : Store) (y : Int) : Frame :=
  {safeCast128Frame imms y with locals := (safeCast128Locals y).insert "z" (.int 0)}

def safeCast128ReadyFrame (imms : Store) (y : Int) : Frame :=
  {safeCast128ZeroFrame imms y with
    locals := (safeCast128ZeroFrame imms y).locals.insert "z"
      (.int (normalizeInt (.sint ⟨128, by decide⟩) y))}

theorem safeCast128Bind (y : Int) :
    bindParams? safeCast128Function.params [.int y] = some (safeCast128Locals y) := rfl

def safeCast128Valid (y : Int) : Prop := normalizeInt (.sint ⟨128, by decide⟩) y = y

theorem safeCast128ReadySource (imms : Store) (evm : EVM.State) (y : Int) :
    ExecBlock config (safeCast128Frame imms y) evm (safeCast128Function.body.take 2)
      (.ok (safeCast128ReadyFrame imms y) evm) :=
  checkedCastReadySource (safeCast128Frame imms y) evm "y" "z" (.sint ⟨128, by decide⟩) y
    (by decide) Std.HashMap.getElem?_insert_self

theorem evalSafeCast128Guard (imms : Store) (evm : EVM.State) (y : Int) :
    evalExpr? config (safeCast128ReadyFrame imms y) evm
      (.binary .eq (.var "z") (.var "y")) =
      .ok (.bool (decide (safeCast128Valid y))) := by
  have he := evalCheckedCastGuard (cfg := config) (safeCast128Frame imms y) evm
    "y" "z" (.sint ⟨128, by decide⟩) y (by decide) Std.HashMap.getElem?_insert_self
  apply he.trans
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, safeCast128Valid]

theorem safeCast128Returns (imms : Store) (evm : EVM.State) (y : Int) (hy : safeCast128Valid y) :
    ExecFuncBody config (safeCast128Frame imms y) evm safeCast128Function.body
      (.returned (safeCast128ReadyFrame imms y) evm (some [.int y])) :=
  checkedCastReturns (safeCast128Frame imms y) evm "y" "z" (.sint ⟨128, by decide⟩) y
    (by decide) Std.HashMap.getElem?_insert_self hy

theorem safeCast128Reverts (imms : Store) (evm : EVM.State) (y : Int) (hy : ¬ safeCast128Valid y) :
    ExecFuncBody config (safeCast128Frame imms y) evm safeCast128Function.body .reverted :=
  checkedCastReverts (safeCast128Frame imms y) evm "y" "z" (.sint ⟨128, by decide⟩) y
    (by decide) Std.HashMap.getElem?_insert_self hy

theorem safeCast128Valid_iff (y : Int) :
    safeCast128Valid y ↔ -(2 ^ 127 : Int) ≤ y ∧ y < 2 ^ 127 := by
  constructor
  · intro hy
    have hb := normalizeSint_bounds ⟨128, by decide⟩ y
    change -(2 ^ 127 : Int) ≤ normalizeInt (.sint ⟨128, by decide⟩) y ∧
      normalizeInt (.sint ⟨128, by decide⟩) y < 2 ^ 127 at hb
    rwa [hy] at hb
  · rintro ⟨hlo, hhi⟩
    exact normalizeSint_eq_self ⟨128, by decide⟩ y hlo hhi

end Benchmarks.UniswapV3.Pool
