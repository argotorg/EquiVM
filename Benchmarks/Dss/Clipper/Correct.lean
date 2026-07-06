import Benchmarks.Dss.Clipper.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Clipper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperCorrect (v : ClipperImmutables) {code : ByteArray}
    (hcode : patchRuntime clipperBytecode (patches v) = some code) :
    runtimeEquivalence!?! (config v) code (contract v) := by
  sorry

theorem clipperContractCorrect (v : ClipperImmutables) {code : ByteArray}
    (hcode : patchRuntime clipperBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) clipperCreationBytecode code (contract v)
      (runtimeCodeOf clipperBytecode) :=
  contractEquivalenceWith.intro
    (clipperConstructorCorrect v)
    (clipperCorrect v hcode)

end Benchmarks.Dss.Clipper
