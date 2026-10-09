import Benchmarks.Safe.Common
import Reasoning.SolmArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def addressArrayValue (w : UInt256) : Value := .address (AccountAddress.ofNat w.toNat)

-- LIBRARY CANDIDATE: read a known local value without fixing its type.
theorem evalLocalValue {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {value : Value} (h : frame.locals[name]? = some value) :
    evalExpr? cfg frame evm (.var name) = .ok value := by
  simp [evalExpr?, h, EvalResult.ofOption]

-- LIBRARY CANDIDATE: a local bytes length is the natural size of the byte array.
theorem evalLocalBytesLength {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {bytes : ByteArray} (hb : frame.locals[name]? = some (.bytes bytes)) :
    evalExpr? cfg frame evm (.arrayLength .localVar { base := name }) =
      .ok (.int (Int.ofNat bytes.size)) := by
  simp [evalExpr?, hb, readLocalPath?, EvalResult.ofOption, EvalResult.bind, bind, pure]

-- LIBRARY CANDIDATE: combine successful Boolean evaluations with source short-circuiting.
theorem evalBoolAnd {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Bool}
    (ha : evalExpr? cfg frame evm lhs = .ok (.bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.bool b)) :
    evalExpr? cfg frame evm (.binary .and lhs rhs) = .ok (.bool (a && b)) := by
  cases a <;> simp [evalExpr?, ha, hb, EvalResult.bind, bind, pure]

-- LIBRARY CANDIDATE: combine successful Boolean evaluations with source short-circuiting.
theorem evalBoolOr {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Bool}
    (ha : evalExpr? cfg frame evm lhs = .ok (.bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.bool b)) :
    evalExpr? cfg frame evm (.binary .or lhs rhs) = .ok (.bool (a || b)) := by
  cases a <;> simp [evalExpr?, ha, hb, EvalResult.bind, bind, pure]

-- LIBRARY CANDIDATE: a checked increment of a known natural-valued expression.
theorem evalNatIncrement {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {i : Nat}
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat i)))
    (hfit : i + 1 < UInt256.size) :
    evalExpr? cfg frame evm (sourceAdd256 expr (.intLit 1)) =
      .ok (.int (Int.ofNat (i + 1))) := by
  have hiword := ulit_toNat' i (by omega)
  have h := checkedAddSourceOk (a := UInt256.ofNat i) (b := ⟨1⟩)
    (by simpa only [hiword] using he) (lhs := expr) (rhs := .intLit 1)
    (by simp [evalExpr?]; rfl)
    (by simpa only [hiword, show (⟨1⟩ : UInt256).toNat = 1 from rfl] using hfit)
  have hsum : (UInt256.ofNat i + (⟨1⟩ : UInt256)).toNat = i + 1 := by
    rw [uadd_toNat, hiword]
    exact Nat.mod_eq_of_lt hfit
  simpa only [hsum] using h

-- LIBRARY CANDIDATE: relate Solm's checked list lookup to Lean's list indexing.
theorem lookupNth_eq_getElem {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    lookupNth? xs i = some xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)

-- LIBRARY CANDIDATE: relate Solm's checked list update to List.set.
theorem updateNth_eq_set {α : Type} (xs : List α) (i : Nat) (value : α)
    (hi : i < xs.length) : updateNth? xs i value = some (xs.set i value) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simp [updateNth?, ih i (by simpa using hi)]

-- LIBRARY CANDIDATE: assignment to a local memory-array element, including the bounds check.
theorem assignLocalArray {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {expr : Expr} {xs : List Value} {i : Nat} (value : Value)
    (ha : frame.locals[name]? = some (.array xs))
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat i)))
    (hi : i < xs.length) :
    assignStorageRef? cfg frame evm .localVar { base := name, steps := [.aindex expr] } value =
      .ok ({ frame with locals := frame.locals.insert name (.array (xs.set i value)) }, evm) := by
  have hi0 : ¬ (i : Int) < 0 := by omega
  simp [assignStorageRef?, ha, updateLocalPath?, he, lookupIndex?, intToNat?,
    lookupNth_eq_getElem xs i hi, updateIndex?, updateNth_eq_set xs i value hi,
    EvalResult.ofOption, EvalResult.bind, bind, pure, hi, hi0, Option.bind]

-- LIBRARY CANDIDATE: an out-of-bounds local memory-array assignment reverts.
theorem assignLocalArrayRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {expr : Expr} {xs : List Value} {i : Nat} (value : Value)
    (ha : frame.locals[name]? = some (.array xs))
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat i)))
    (hi : xs.length ≤ i) :
    assignStorageRef? cfg frame evm .localVar { base := name, steps := [.aindex expr] } value =
      .revert := by
  simp [assignStorageRef?, ha, updateLocalPath?, he, EvalResult.bind, bind, pure, not_lt.mpr hi]

end Benchmarks.Safe
