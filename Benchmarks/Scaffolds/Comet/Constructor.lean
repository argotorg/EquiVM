import Benchmarks.Scaffolds.Comet.Bytecode
import Solm.Equiv

/-!
# Compound III CometWithExtendedAssetList constructor stub

Parameterized over Comet's 25 immutable values.  The constructor patches those into the runtime;
`constructorEquivalenceWith` checks that the runtime the EVM returns equals `runtimeCodeOf` applied to
the constructor's final `imm_<name>` locals.  Proof left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometConstructorCorrect (v : CometImmutables) :
    constructorEquivalenceWith (config v) cometCreationBytecode (contract v)
      (runtimeCodeOf cometBytecode) := by
  sorry

end Benchmarks.CompoundIII.Comet
