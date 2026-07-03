import Benchmarks.CompoundIII.Comet.Constructor
import Solm.Equiv

/-!
# Compound III CometWithExtendedAssetList runtime correctness stub

The upstream Solidity source closure, optimized runtime bytecode, Solm AST spec, and Solm syntax
spec are present. The runtime-equivalence proof below is for solc's unpatched `--bin-runtime`
template.

There is intentionally no whole-contract wrapper in this file: Comet's constructor patches immutable
values into the returned runtime, so `contractEquivalence ... cometBytecode ...` would be a false
target for arbitrary constructor arguments.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.Comet

theorem cometCorrect :
    runtimeEquivalence!?! config cometBytecode contract := by
  sorry

end Benchmarks.CompoundIII.Comet
