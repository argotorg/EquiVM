import Benchmarks.Midnight.Common

/-!
# Midnight constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Stele constructor body, composed from the creation summaries.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightConstructorCorrect :
    typedConstructorRefinement config midnightCreationBytecode contract (fun _ => midnightBytecode) := by
  sorry

end Benchmarks.Midnight
