import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: relate Solm's list accessors to Lean's list operations.
theorem lookupNth_eq_getElem? {α : Type} (xs : List α) (i : Nat) :
    lookupNth? xs i = xs[i]? := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons a xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem updateNth_eq_set {α : Type} (xs : List α) (i : Nat) (v : α) (hi : i < xs.length) :
    updateNth? xs i v = some (xs.set i v) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih => cases i with
    | zero => rfl
    | succ i =>
        simp only [updateNth?, ih i (by simpa using hi), bind, Option.bind, pure]
        rfl

-- LIBRARY CANDIDATE: integer memory-array allocation in an arbitrary frame.
theorem evalExpr_newIntArray {cfg : Config} {frame : Frame} {evm : EVM.State}
    {len : Expr} (ty : ABI.IntType) (n : Nat)
    (he : evalExpr? cfg frame evm len = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg frame evm (.newArray (.elem (.int ty)) len) =
      .ok (.array (List.replicate n (.int 0))) := by
  have hn : ¬ Int.ofNat n < 0 := not_lt.mpr (Int.natCast_nonneg n)
  simp only [evalExpr?, he, bind, EvalResult.bind, if_neg hn, defaultValue?, pure]
  rfl

theorem evalExpr_arrayIndexInt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {arr idx : Expr} {values : List Value} {i : Nat} {value : Int}
    (ha : evalExpr? cfg frame evm arr = .ok (.array values))
    (hi : evalExpr? cfg frame evm idx = .ok (.int (Int.ofNat i)))
    (hb : i < values.length) (hv : values[i]? = some (.int value)) :
    evalExpr? cfg frame evm (.index arr idx) = .ok (.int value) := by
  have hbound : 0 ≤ Int.ofNat i ∧ Int.ofNat i < (values.length : Int) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hb⟩
  simp only [evalExpr?, ha, hi, bind, EvalResult.bind, evalIndex?, if_pos hbound,
    show (Int.ofNat i).toNat = i from rfl, lookupNth_eq_getElem?, hv, normalizeRawBoolWord?]

theorem assignLocalArrayIndex {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {values : List Value} {idx : Expr} {i : Nat} {value : Value}
    (ha : frame.locals.get? name = some (.array values))
    (hi : evalExpr? cfg frame evm idx = .ok (.int (Int.ofNat i))) (hb : i < values.length) :
    assignStorageRef? cfg frame evm .localVar ⟨name, [.aindex idx]⟩ value =
      .ok ({frame with locals := frame.locals.insert name (.array (values.set i value))}, evm) := by
  have hbound : 0 ≤ Int.ofNat i ∧ Int.ofNat i < (values.length : Int) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hb⟩
  have hn : ¬ Int.ofNat i < 0 := not_lt.mpr hbound.1
  have hget : lookupNth? values i = some values[i] := by
    rw [lookupNth_eq_getElem?, List.getElem?_eq_getElem hb]
  simp only [assignStorageRef?, ha, updateLocalPath?, hi, bind, EvalResult.bind, if_pos hbound,
    lookupIndex?, intToNat?, if_neg hn, show (Int.ofNat i).toNat = i from rfl, Option.bind,
    hget, EvalResult.ofOption, updateIndex?, updateNth_eq_set values i value hb, pure]

theorem evalExpr_localArrayLength {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {values : List Value} (ha : frame.locals.get? name = some (.array values)) :
    evalExpr? cfg frame evm (.arrayLength .localVar ⟨name, []⟩) =
      .ok (.int (Int.ofNat values.length)) := by
  simp only [evalExpr?, ha, readLocalPath?, pure, bind, EvalResult.bind]
  rfl

end Benchmarks.UniswapV3.Pool
