import Benchmarks.UniswapV4PoolManager.WordArraySource
import Benchmarks.UniswapV4PoolManager.ExttloadArrayLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem exttloadArraySource (evm : EVM.State) (slots : List Value) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hd : WordArrayDecoded evm.executionEnv.calldata slots) :
    ∃ f, ExecTransitionBody config contract evm (wordArrayArgs slots)
      exttload_bytes32_arrayTransition.body
      (.returned f evm (some [.array (wordArrayValues (exttloadArrayValue evm) 0 slots.length)])) imms :=
  wordArraySource true evm slots imms hwv hd

end Benchmarks.UniswapV4PoolManager
