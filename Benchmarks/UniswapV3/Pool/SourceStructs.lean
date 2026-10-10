import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: assigning one field of a struct stored in a local variable.
theorem assignLocalField_frame {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base field : Ident} {root child value result : Value}
    (hget : frame.locals.get? base = some root)
    (hfield : lookupField? root field = some child)
    (hupdate : updateField? root field value = some result) :
    assignStorageRef? cfg frame evm .localVar ⟨base, [.field field]⟩ value =
      .ok ({frame with locals := frame.locals.insert base result}, evm) := by
  simp only [assignStorageRef?, hget, updateLocalPath?, hfield, hupdate,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
