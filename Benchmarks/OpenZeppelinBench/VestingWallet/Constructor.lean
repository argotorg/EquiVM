import Benchmarks.OpenZeppelinBench.VestingWallet.Bytecode
import Solm.Equiv

/-!
# OpenZeppelin VestingWallet constructor correctness stub

The optimized creation bytecode returns the runtime bytecode with the concrete immutable values
`start = 0` and `duration = 365 days`. The proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.VestingWallet

theorem vestingWalletBenchConstructorCorrect :
    constructorEquivalence config vestingWalletBenchCreationBytecode contract vestingWalletBenchBytecode := by
  sorry

end OpenZeppelinBench.VestingWallet
