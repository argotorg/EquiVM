import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: a bytes-length guard depends only on the decoded byte array.
theorem evalLocalBytesNonempty {cfg : Config} {frame : Frame} {evm : EVM.State} {name : Ident} {data : ByteArray}
    (he : frame.locals.get? name = some (.bytes data)) :
    evalExpr? cfg frame evm (.binary .gt (.arrayLength .localVar ⟨name, []⟩) (.intLit 0)) =
      .ok (.bool (decide (0 < data.size))) := by
  simp only [evalExpr?, he, readLocalPath?, evalBinaryOp?, pure, bind, EvalResult.bind]
  congr 2
  simp

-- LIBRARY CANDIDATE: a local bytes-length inequality in any source frame.
theorem evalLocalBytesLengthNeZero {cfg : Config} {frame : Frame} {name : Ident} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? name = some (.bytes out)) :
    evalExpr? cfg frame evm (.binary .ne (.arrayLength .localVar ⟨name, []⟩) (.intLit 0)) =
      .ok (.bool (decide (out.size ≠ 0))) := by
  simp only [evalExpr?, hout, readLocalPath?,
    evalBinaryOp?, pure, bind, EvalResult.bind]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [bne, Bool.not_eq_true', beq_iff_eq, Value.int.injEq,
    Int.natCast_eq_zero, decide_eq_true_eq, Bool.eq_false_iff]
  have he : (Value.int (Int.ofNat out.size) == Value.int 0) = true ↔ out.size = 0 := by
    rw [beq_iff_eq, Value.int.injEq]
    constructor
    · exact Int.ofNat.inj
    · intro h; rw [h]; rfl
  exact not_congr he

end Benchmarks.Morpho.MorphoBlue
