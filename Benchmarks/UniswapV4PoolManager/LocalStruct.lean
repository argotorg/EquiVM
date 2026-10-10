import Benchmarks.UniswapV4PoolManager.PoolKeySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: update one field of a struct held in a local variable.
theorem assignLocalField {cfg : Config} {f : Frame} {evm : State}
    {name field : Ident} {root old value updated : Value}
    (hget : f.locals.get? name = some root) (hfield : lookupField? root field = some old)
    (hupdate : updateField? root field value = some updated) :
    assignStorageRef? cfg f evm .localVar {base := name, steps := [.field field]} value =
      .ok ({f with locals := f.locals.insert name updated}, evm) := by
  simp only [assignStorageRef?, hget, updateLocalPath?, hfield, hupdate,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV4PoolManager
