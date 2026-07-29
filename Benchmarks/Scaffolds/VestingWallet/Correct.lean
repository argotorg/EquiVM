import Benchmarks.Scaffolds.VestingWallet.Constructor
import Solm.Equiv

/-!
# OpenZeppelin VestingWallet benchmark correctness stub

The source closure, optimized runtime bytecode, creation bytecode, storage layout, external ABI
model, and receive/SafeERC20 semantics are present. The runtime-equivalence proof is intentionally
left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.VestingWallet

theorem vestingWalletBenchCorrect :
    runtimeEquivalence config vestingWalletBenchBytecode contract := by
  sorry

theorem vestingWalletBenchContractCorrect :
    contractEquivalence config vestingWalletBenchCreationBytecode vestingWalletBenchBytecode contract :=
  contractEquivalence.intro vestingWalletBenchConstructorCorrect vestingWalletBenchCorrect

end OpenZeppelinBench.VestingWallet
