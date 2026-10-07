import Benchmarks.Scaffolds.UniswapV2Router02.Bytecode
import Solm.Refine

/-!
# UniswapV2Router02 constructor correctness stub

The constructor sets `factory` and `WETH`.  `typedConstructorRefinement` checks that the runtime the EVM returns
is the template patched with the constructor's final immutables (`deployedRuntime`), and that those
are well typed.  Proof left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV2Router02.Immutables

namespace Benchmarks.UniswapV2Router02

theorem uniswapV2Router02ConstructorCorrect :
    typedConstructorRefinement config uniswapV2Router02CreationBytecode contract
      (deployedRuntime uniswapV2Router02Bytecode) := by
  sorry

end Benchmarks.UniswapV2Router02
