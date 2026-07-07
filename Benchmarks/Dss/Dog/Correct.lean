import Benchmarks.Dss.Dog.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Dog benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

theorem dogCorrect (v : DogImmutables) {code : ByteArray}
    (hcode : patchRuntime dogBytecode (patches v) = some code) :
    runtimeEquivalence!?! (config v) code (contract v) := by
  sorry

theorem dogContractCorrect (v : DogImmutables) {code : ByteArray}
    (hcode : patchRuntime dogBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) dogCreationBytecode code (contract v)
      (runtimeCodeOf dogBytecode) :=
  contractEquivalenceWith.intro
    (dogConstructorCorrect v)
    (dogCorrect v hcode)

end Benchmarks.Dss.Dog
