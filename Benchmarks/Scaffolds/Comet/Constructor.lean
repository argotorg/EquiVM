import Benchmarks.Scaffolds.Comet.Bytecode
import Solm.Refine

/-!
# Compound III CometWithExtendedAssetList constructor correctness stub

The constructor sets Comet's 25 immutables.  `typedConstructorRefinement` checks that the runtime the EVM returns
is the template patched with the constructor's final immutables (`deployedRuntime`), and that those
are well typed.  Proof left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometConstructorCorrect :
    typedConstructorRefinement config cometCreationBytecode contract
      (deployedRuntime cometBytecode) := by
  sorry

end Benchmarks.CompoundIII.Comet
