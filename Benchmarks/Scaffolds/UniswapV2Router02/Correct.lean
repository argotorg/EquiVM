import Benchmarks.Scaffolds.UniswapV2Router02.Constructor
import Solm.Refine

/-!
# UniswapV2Router02 benchmark correctness stub

For every well-typed assignment of `factory` and `WETH`, the runtime deployed for it (the template patched with
it) refines the spec run with those immutables.  With the constructor target this gives the
contract refinement.  Proofs are the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV2Router02.Immutables

namespace Benchmarks.UniswapV2Router02

theorem uniswapV2Router02Correct (imms : Store) (_hfit : immutablesFit contract imms) :
    runtimeRefinement config (deployedRuntime uniswapV2Router02Bytecode imms) contract
      (restrictImmutables contract imms) := by
  sorry

theorem uniswapV2Router02ContractCorrect : contractRefinement config uniswapV2Router02CreationBytecode contract :=
  .of_runtime uniswapV2Router02ConstructorCorrect uniswapV2Router02Correct

end Benchmarks.UniswapV2Router02
