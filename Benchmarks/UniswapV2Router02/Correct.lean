import Benchmarks.UniswapV2Router02.Constructor
import Solm.Equiv

/-!
# UniswapV2Router02 benchmark correctness stub

Parameterized over the router's immutable values `v`.  For each `v`, the deployed runtime is the
solc template patched with `v` (`patchRuntime uniswapV2Router02Bytecode (patches v) = some code`),
and runtime equivalence is stated against `contract v`.  The whole-contract bundle pairs this with
the parameterized constructor target.  Proofs are intentionally left as targets.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV2Router02.Immutables

namespace Benchmarks.UniswapV2Router02

theorem uniswapV2Router02Correct (v : RouterImmutables) {code : ByteArray}
    (hcode : patchRuntime uniswapV2Router02Bytecode (patches v) = some code) :
    runtimeEquivalence!?! (config v) code (contract v) := by
  sorry

theorem uniswapV2Router02ContractCorrect (v : RouterImmutables) {code : ByteArray}
    (hcode : patchRuntime uniswapV2Router02Bytecode (patches v) = some code) :
    contractEquivalenceWith (config v) uniswapV2Router02CreationBytecode code (contract v)
      (runtimeCodeOf uniswapV2Router02Bytecode) :=
  contractEquivalenceWith.intro
    (uniswapV2Router02ConstructorCorrect v)
    (uniswapV2Router02Correct v hcode)

end Benchmarks.UniswapV2Router02
