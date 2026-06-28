import Benchmarks.GnosisMultiSig.Bytecode
import Solm.Equiv

/-!
# Gnosis MultiSigWallet constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present.  The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.GnosisMultiSig

theorem gnosisMultiSigConstructorCorrect :
    constructorEquivalence config gnosisMultiSigCreationBytecode contract gnosisMultiSigBytecode := by
  sorry

end Benchmarks.GnosisMultiSig
