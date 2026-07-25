import Benchmarks.CompoundIII.Comet.Constructor
import Solm.Equiv

/-!
# Compound III CometWithExtendedAssetList correctness stub

Parameterized over Comet's 25 immutable values `v`.  For each `v`, the deployed runtime is the
template patched with `v` (`patchRuntime cometBytecode (patches v) = some code`), and runtime
equivalence is stated against `contract v` (whose immutable getters return `v`'s values).  The
whole-contract bundle pairs this with the parameterized constructor target.  All proofs are targets.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometCorrect (v : CometImmutables) {code : ByteArray}
    (hcode : patchRuntime cometBytecode (patches v) = some code) :
    runtimeEquivalence (config v) code (contract v) := by
  sorry

theorem cometContractCorrect (v : CometImmutables) {code : ByteArray}
    (hcode : patchRuntime cometBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) cometCreationBytecode code (contract v)
      (runtimeCodeOf cometBytecode) :=
  contractEquivalenceWith.intro (cometConstructorCorrect v) (cometCorrect v hcode)

end Benchmarks.CompoundIII.Comet
