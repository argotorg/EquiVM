import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: local memory-array reads, writes, and checked loop increments.
theorem lookupNth_eq_getElem {α : Type} (values : List α) (i : Nat) :
    lookupNth? values i = values[i]? := by
  induction values generalizing i with
  | nil => simp [lookupNth?]
  | cons v vs ih => cases i <;> simp [lookupNth?, ih]

theorem updateNth_eq_set {α : Type} (values : List α) (i : Nat) (value : α)
    (hi : i < values.length) : updateNth? values i value = some (values.set i value) := by
  induction values generalizing i with
  | nil => simp at hi
  | cons v vs ih =>
      cases i with
      | zero => simp [updateNth?]
      | succ i => simp [updateNth?, ih i (by simpa using hi)]

theorem evalLocalArrayLength {cfg solm evm name} {values : List Value}
    (h : solm.locals.get? name = some (.array values)) :
    evalExpr? cfg solm evm (.arrayLength .localVar ⟨name, []⟩) =
      .ok (.int (Int.ofNat values.length)) := by
  simp only [evalExpr?, h, readLocalPath?, pure, bind, EvalResult.bind, Int.ofNat_eq_natCast]

theorem evalLocalNatLt {cfg solm evm left right} {i n : Nat}
    (hi : solm.locals.get? left = some (.int (Int.ofNat i)))
    (hn : solm.locals.get? right = some (.int (Int.ofNat n))) :
    evalExpr? cfg solm evm (.binary .lt (.var left) (.var right)) =
      .ok (.bool (decide (i < n))) := by
  simp only [evalExpr?, hi, hn, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, Nat.cast_lt]

theorem evalLocalArrayIndex {cfg solm evm array index} {values : List Value} {i : Nat} {v : Value}
    (ha : solm.locals.get? array = some (.array values))
    (hi : solm.locals.get? index = some (.int (Int.ofNat i)))
    (hv : values[i]? = some v) (hnorm : normalizeRawBoolWord? v = .ok v) :
    evalExpr? cfg solm evm (.index (.var array) (.var index)) = .ok v := by
  have hib : i < values.length := (List.getElem?_eq_some_iff.mp hv).1
  simp only [evalExpr?, ha, hi, EvalResult.ofOption, bind, EvalResult.bind,
    evalIndex?, lookupIndex?, lookupNth_eq_getElem, intToNat?, Int.ofNat_eq_natCast,
    Int.toNat_natCast,
    show ¬ (i : Int) < 0 by omega, show 0 ≤ (i : Int) by omega,
    show (i : Int) < values.length by omega, and_self, if_true, if_false, hv, hnorm]

theorem assignLocalArrayAt {cfg solm evm array value} {index : Expr} {values : List Value} {i : Nat}
    (ha : solm.locals.get? array = some (.array values))
    (hi : evalExpr? cfg solm evm index = .ok (.int (Int.ofNat i))) (hib : i < values.length) :
    assignStorageRef? cfg solm evm .localVar ⟨array, [.aindex index]⟩ value =
      .ok ({ solm with locals := solm.locals.insert array (.array (values.set i value)) },
          evm) := by
  have hv := List.getElem?_eq_getElem hib
  simp only [assignStorageRef?, ha, updateLocalPath?, hi, EvalResult.ofOption,
    bind, EvalResult.bind, pure, Int.ofNat_eq_natCast, Int.toNat_natCast,
    show 0 ≤ (i : Int) by omega, show (i : Int) < values.length by omega, and_self,
    if_true, lookupIndex?, show ¬ (i : Int) < 0 by omega, if_false, hv, updateIndex?,
    lookupNth_eq_getElem, intToNat?, updateNth_eq_set _ _ _ hib, hib, Int.toNat_natCast,
    Option.bind]

theorem assignLocalArrayIndex {cfg solm evm array index value} {values : List Value} {i : Nat}
    (ha : solm.locals.get? array = some (.array values))
    (hi : solm.locals.get? index = some (.int (Int.ofNat i))) (hib : i < values.length) :
    assignStorageRef? cfg solm evm .localVar ⟨array, [.aindex (.var index)]⟩ value =
      .ok ({ solm with locals := solm.locals.insert array (.array (values.set i value)) },
          evm) :=
  assignLocalArrayAt ha (evalLocalValue hi) hib

theorem evalLocalNatNeZero {cfg solm evm name} {n : Nat}
    (hn : solm.locals.get? name = some (.int (Int.ofNat n))) :
    evalExpr? cfg solm evm (.binary .ne (.var name) (.intLit 0)) =
      .ok (.bool (decide (n ≠ 0))) := by
  simp only [evalExpr?, hn, EvalResult.ofOption, bind, EvalResult.bind, pure, evalBinaryOp?]
  by_cases hz : n = 0
  · subst n
    have hb : (Value.int (Int.ofNat 0) == Value.int 0) = true := by
      apply beq_iff_eq.mpr; rfl
    simp only [hb, Bool.not_true, ne_eq, not_true_eq_false, decide_false]
  · have hb : (Value.int (Int.ofNat n) == Value.int 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      simp only [ne_eq, Value.int.injEq, Int.ofNat_eq_natCast, Nat.cast_eq_zero]
      exact hz
    simp only [hb, Bool.not_false, decide_eq_true hz]

theorem evalLocalNewArray {cfg solm evm name ty value} {n : Nat}
    (hn : solm.locals.get? name = some (.int (Int.ofNat n)))
    (hd : defaultValue? ty = .ok value) :
    evalExpr? cfg solm evm (.newArray ty (.var name)) = .ok (.array (List.replicate n value)) := by
  simp only [evalExpr?, hn, EvalResult.ofOption, bind, EvalResult.bind, Int.ofNat_eq_natCast,
    show ¬ (n : Int) < 0 by omega, if_false, hd, pure, Int.toNat_natCast]

end Benchmarks.UniswapV4PoolManager
