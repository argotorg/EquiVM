import Benchmarks.EAS.Attester.LocalArray

/-! Boolean tests of source memory-array elements. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: negate a boolean element held in a source local array.
theorem evalLocalArrayBoolNot {cfg : Config} {frame : Frame} {evm : State}
    {array index : Ident} {values : List Bool} {i : Nat} {b : Bool}
    (ha : frame.locals.get? array = some (.array (values.map Value.bool)))
    (hi : frame.locals.get? index = some (.int (Int.ofNat i)))
    (hb : values[i]? = some b) :
    evalExpr? cfg frame evm (.unary .not (.index (.var array) (.var index))) =
      .ok (.bool (!b)) := by
  have he := evalLocalArrayIndex (cfg := cfg) (evm := evm) (v := .bool b) ha hi
    (by simp only [List.getElem?_map, hb, Option.map_some]) rfl
  simp only [evalExpr?, he, bind, EvalResult.bind, evalUnaryOp?, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1
