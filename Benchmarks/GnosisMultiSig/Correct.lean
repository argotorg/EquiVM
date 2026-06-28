import Benchmarks.GnosisMultiSig.Constructor
import Solm.Equiv

/-!
# Gnosis MultiSigWallet benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present.  The runtime-equivalence proof is intentionally left as the benchmark target.  This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.GnosisMultiSig

theorem gnosisMultiSigCorrect :
    runtimeEquivalence!?! config gnosisMultiSigBytecode contract := by
  sorry

theorem gnosisMultiSigContractCorrect :
    contractEquivalence config gnosisMultiSigCreationBytecode gnosisMultiSigBytecode contract :=
  contractEquivalence.intro gnosisMultiSigConstructorCorrect gnosisMultiSigCorrect

end Benchmarks.GnosisMultiSig
