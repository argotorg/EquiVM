import Benchmarks.CompoundIII.Comet.Common

/-!
# CometWithExtendedAssetList constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometWithExtendedAssetListConstructorCorrect :
    typedConstructorRefinement config cometWithExtendedAssetListCreationBytecode contract (immutableLayout.deployed cometWithExtendedAssetListBytecode) := by
  sorry

end Benchmarks.CompoundIII.Comet
