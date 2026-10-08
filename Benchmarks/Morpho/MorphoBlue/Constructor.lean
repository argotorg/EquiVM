import Benchmarks.Morpho.MorphoBlue.Common

/-!
# Morpho constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

theorem morphoConstructorCorrect :
    typedConstructorRefinement config morphoCreationBytecode contract (immutableLayout.deployed morphoBytecode) := by
  sorry

end Benchmarks.Morpho.MorphoBlue
