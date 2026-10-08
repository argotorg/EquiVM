import Benchmarks.Morpho.MetaMorphoV1_1.Common

/-!
# MetaMorphoV1_1 constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

theorem metaMorphoV1_1ConstructorCorrect :
    typedConstructorRefinement config metaMorphoV1_1CreationBytecode contract (immutableLayout.deployed metaMorphoV1_1Bytecode) := by
  sorry

end Benchmarks.Morpho.MetaMorphoV1_1
