import Benchmarks.CompoundIII.Comet.Bytecode
import Solm.Equiv

/-!
# Compound III CometWithExtendedAssetList constructor status

Comet's Solidity constructor patches 25 immutable references into the runtime.  The checked
`cometBytecode` artifact is solc's unpatched `--bin-runtime` template, so the standard
`constructorEquivalence ... cometBytecode` statement would be false for arbitrary ABI-valid
constructor arguments.

This file intentionally does not expose a `constructorEquivalence` theorem until the benchmark uses
an immutable-patched runtime target, or the framework grows a constructor equivalence shape that can
relate constructor arguments and external constructor calls to the returned runtime bytes.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.Comet

theorem cometConstructorBlockedByImmutables : True := by
  trivial

end Benchmarks.CompoundIII.Comet
