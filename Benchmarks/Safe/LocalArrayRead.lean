import Benchmarks.Safe.LocalArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: the length of a known local array.
theorem evalLocalArrayLength {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {xs : List Value} (hx : frame.locals[name]? = some (.array xs)) :
    evalExpr? cfg frame evm (.arrayLength .localVar { base := name }) =
      .ok (.int (Int.ofNat xs.length)) := by
  simp [evalExpr?, hx, readLocalPath?, EvalResult.ofOption, EvalResult.bind, bind, pure]

-- LIBRARY CANDIDATE: an in-bounds local array index evaluates to the corresponding element.
theorem evalLocalArrayIndex {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {expr : Expr} {xs : List Value} {i : Nat}
    (hx : frame.locals[name]? = some (.array xs))
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat i))) (hi : i < xs.length) :
    evalExpr? cfg frame evm (.index (.var name) expr) = normalizeRawBoolWord? xs[i] := by
  rw [evalExpr?, evalLocalValue hx, he]
  simp [EvalResult.bind, bind, pure, evalIndex?, lookupNth_eq_getElem xs i hi, hi]

end Benchmarks.Safe
