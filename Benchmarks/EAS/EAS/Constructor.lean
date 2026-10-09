import Benchmarks.EAS.EAS.Common

/-!
# EAS constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.EAS.EAS.Immutables

namespace Benchmarks.EAS.EAS

theorem easConstructorCorrect :
    typedConstructorRefinement config easCreationBytecode contract (immutableLayout.deployed easBytecode) := by
  sorry

end Benchmarks.EAS.EAS
