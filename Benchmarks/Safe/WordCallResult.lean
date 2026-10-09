import Benchmarks.Safe.LocalArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: only evaluate a return-word check after success and exact-size checks.
theorem evalWordCallResult {cfg : Config} {frame : Frame} {evm : EVM.State}
    {successName dataName : Ident} {check : Expr} {z b : Bool} {out : ByteArray}
    (hs : frame.locals[successName]? = some (.bool z))
    (hd : frame.locals[dataName]? = some (.bytes out))
    (hc : out.size = 32 → evalExpr? cfg frame evm check = .ok (.bool b)) :
    evalExpr? cfg frame evm
      (andE (.var successName) (andE (eqE (localLength dataName) (.intLit 32)) check)) =
      .ok (.bool (z && (decide (out.size = 32) && b))) := by
  cases z with
  | false => simp [andE, evalExpr?, hs, EvalResult.ofOption, EvalResult.bind, bind, pure]
  | true =>
      by_cases ho : out.size = 32
      · simp [andE, eqE, localLength, evalExpr?, hs, hd, hc ho, varRef, readLocalPath?,
          EvalResult.ofOption, EvalResult.bind, bind, pure, ho, evalBinaryOp_eq_int_ok]
      · have hlen : (Value.int (out.size : Int) == Value.int 32) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq, Value.int.injEq]
          omega
        simp [andE, eqE, localLength, evalExpr?, hs, hd, varRef, readLocalPath?,
          EvalResult.ofOption, EvalResult.bind, bind, pure, ho, evalBinaryOp_eq_int_ok, hlen]

-- LIBRARY CANDIDATE: equality of two source bytes32 values is equality of their EVM words.
theorem wordBytes32Value_beq (a b : UInt256) :
    (wordBytes32Value a == wordBytes32Value b) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    apply word_toBytesBE_inj
    simpa only [wordBytes32Value, Value.fixedBytes.injEq, true_and] using h
  · intro h
    rw [h]

end Benchmarks.Safe
