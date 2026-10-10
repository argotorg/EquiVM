import Benchmarks.UniswapV4PoolManager.WordArraySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
abbrev extsloadArrayValue := wordArrayValue false

theorem extsloadArraySource (evm : EVM.State) (slots : List Value) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hd : WordArrayDecoded evm.executionEnv.calldata slots) :
    ∃ f, ExecTransitionBody config contract evm (wordArrayArgs slots)
      extsload_bytes32_arrayTransition.body
      (.returned f evm (some [.array (wordArrayValues (extsloadArrayValue evm) 0 slots.length)])) imms :=
  wordArraySource false evm slots imms hwv hd

end Benchmarks.UniswapV4PoolManager
