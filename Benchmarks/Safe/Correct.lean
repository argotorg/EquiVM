import Benchmarks.Safe.AddOwnerWithThreshold
import Benchmarks.Safe.ApproveHash
import Benchmarks.Safe.ApprovedHashes
import Benchmarks.Safe.ChangeThreshold
import Benchmarks.Safe.CheckNSignatures
import Benchmarks.Safe.CheckNSignaturesWithExecutor
import Benchmarks.Safe.CheckSignatures
import Benchmarks.Safe.CheckSignaturesWithExecutor
import Benchmarks.Safe.Constructor
import Benchmarks.Safe.DisableModule
import Benchmarks.Safe.DomainSeparator
import Benchmarks.Safe.EnableModule
import Benchmarks.Safe.ExecTransaction
import Benchmarks.Safe.ExecTransactionFromModule
import Benchmarks.Safe.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.Fallback
import Benchmarks.Safe.GetModulesPaginated
import Benchmarks.Safe.GetOwners
import Benchmarks.Safe.GetStorageAt
import Benchmarks.Safe.GetThreshold
import Benchmarks.Safe.GetTransactionHash
import Benchmarks.Safe.IsModuleEnabled
import Benchmarks.Safe.IsOwner
import Benchmarks.Safe.Nonce
import Benchmarks.Safe.Receive
import Benchmarks.Safe.RemoveOwner
import Benchmarks.Safe.SetFallbackHandler
import Benchmarks.Safe.SetGuard
import Benchmarks.Safe.SetModuleGuard
import Benchmarks.Safe.Setup
import Benchmarks.Safe.SignedMessages
import Benchmarks.Safe.SimulateAndRevert
import Benchmarks.Safe.SwapOwner
import Benchmarks.Safe.Version
import Solm.Equiv

/-!
# Safe benchmark correctness

The upstream Solidity source tree, optimized runtime bytecode, Solm AST spec, and Solm syntax
spec are present. This file wires the runtime dispatcher to one leaf proof per ABI entry, plus
receive and fallback, and exposes the whole-contract wrapper combining the constructor and runtime
targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Safe

/-- Convert the accumulated selector negations into the indexed no-match predicate. -/
theorem safeNoSelectorMatches {I : ExecutionEnv}
    (hVersion : ¬ selIs I (safeSelBytes 0))
    (hAddOwnerWithThreshold : ¬ selIs I (safeSelBytes 1))
    (hApproveHash : ¬ selIs I (safeSelBytes 2))
    (hApprovedHashes : ¬ selIs I (safeSelBytes 3))
    (hChangeThreshold : ¬ selIs I (safeSelBytes 4))
    (hCheckNSignatures : ¬ selIs I (safeSelBytes 5))
    (hCheckNSignaturesWithExecutor : ¬ selIs I (safeSelBytes 6))
    (hCheckSignatures : ¬ selIs I (safeSelBytes 7))
    (hCheckSignaturesWithExecutor : ¬ selIs I (safeSelBytes 8))
    (hDisableModule : ¬ selIs I (safeSelBytes 9))
    (hDomainSeparator : ¬ selIs I (safeSelBytes 10))
    (hEnableModule : ¬ selIs I (safeSelBytes 11))
    (hExecTransaction : ¬ selIs I (safeSelBytes 12))
    (hExecTransactionFromModule : ¬ selIs I (safeSelBytes 13))
    (hExecModuleReturnData : ¬ selIs I (safeSelBytes 14))
    (hGetModulesPaginated : ¬ selIs I (safeSelBytes 15))
    (hGetOwners : ¬ selIs I (safeSelBytes 16))
    (hGetStorageAt : ¬ selIs I (safeSelBytes 17))
    (hGetThreshold : ¬ selIs I (safeSelBytes 18))
    (hGetTransactionHash : ¬ selIs I (safeSelBytes 19))
    (hIsModuleEnabled : ¬ selIs I (safeSelBytes 20))
    (hIsOwner : ¬ selIs I (safeSelBytes 21))
    (hNonce : ¬ selIs I (safeSelBytes 22))
    (hRemoveOwner : ¬ selIs I (safeSelBytes 23))
    (hSetFallbackHandler : ¬ selIs I (safeSelBytes 24))
    (hSetGuard : ¬ selIs I (safeSelBytes 25))
    (hSetModuleGuard : ¬ selIs I (safeSelBytes 26))
    (hSetup : ¬ selIs I (safeSelBytes 27))
    (hSignedMessages : ¬ selIs I (safeSelBytes 28))
    (hSimulateAndRevert : ¬ selIs I (safeSelBytes 29))
    (hSwapOwner : ¬ selIs I (safeSelBytes 30)) :
    ∀ i, i < 31 → (safeSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [safeSelBytes, selIs] using hVersion
  · simpa [safeSelBytes, selIs] using hAddOwnerWithThreshold
  · simpa [safeSelBytes, selIs] using hApproveHash
  · simpa [safeSelBytes, selIs] using hApprovedHashes
  · simpa [safeSelBytes, selIs] using hChangeThreshold
  · simpa [safeSelBytes, selIs] using hCheckNSignatures
  · simpa [safeSelBytes, selIs] using hCheckNSignaturesWithExecutor
  · simpa [safeSelBytes, selIs] using hCheckSignatures
  · simpa [safeSelBytes, selIs] using hCheckSignaturesWithExecutor
  · simpa [safeSelBytes, selIs] using hDisableModule
  · simpa [safeSelBytes, selIs] using hDomainSeparator
  · simpa [safeSelBytes, selIs] using hEnableModule
  · simpa [safeSelBytes, selIs] using hExecTransaction
  · simpa [safeSelBytes, selIs] using hExecTransactionFromModule
  · simpa [safeSelBytes, selIs] using hExecModuleReturnData
  · simpa [safeSelBytes, selIs] using hGetModulesPaginated
  · simpa [safeSelBytes, selIs] using hGetOwners
  · simpa [safeSelBytes, selIs] using hGetStorageAt
  · simpa [safeSelBytes, selIs] using hGetThreshold
  · simpa [safeSelBytes, selIs] using hGetTransactionHash
  · simpa [safeSelBytes, selIs] using hIsModuleEnabled
  · simpa [safeSelBytes, selIs] using hIsOwner
  · simpa [safeSelBytes, selIs] using hNonce
  · simpa [safeSelBytes, selIs] using hRemoveOwner
  · simpa [safeSelBytes, selIs] using hSetFallbackHandler
  · simpa [safeSelBytes, selIs] using hSetGuard
  · simpa [safeSelBytes, selIs] using hSetModuleGuard
  · simpa [safeSelBytes, selIs] using hSetup
  · simpa [safeSelBytes, selIs] using hSignedMessages
  · simpa [safeSelBytes, selIs] using hSimulateAndRevert
  · simpa [safeSelBytes, selIs] using hSwapOwner

theorem safeCorrect :
    runtimeEquivalence!?! config safeBytecode contract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hVersion : selIs I (safeSelBytes 0)
  · exact safeVersionBodyCore hcode hsize hperm hVersion hAccounts
  · by_cases hAddOwnerWithThreshold : selIs I (safeSelBytes 1)
    · exact safeAddOwnerWithThresholdBodyCore hcode hsize hperm hAddOwnerWithThreshold
        hAccounts
    · by_cases hApproveHash : selIs I (safeSelBytes 2)
      · exact safeApproveHashBodyCore hcode hsize hperm hApproveHash hAccounts
      · by_cases hApprovedHashes : selIs I (safeSelBytes 3)
        · exact safeApprovedHashesBodyCore hcode hsize hperm hApprovedHashes hAccounts
        · by_cases hChangeThreshold : selIs I (safeSelBytes 4)
          · exact safeChangeThresholdBodyCore hcode hsize hperm hChangeThreshold hAccounts
          · by_cases hCheckNSignatures : selIs I (safeSelBytes 5)
            · exact safeCheckNSignaturesBodyCore hcode hsize hperm hCheckNSignatures
                hAccounts
            · by_cases hCheckNSignaturesWithExecutor : selIs I (safeSelBytes 6)
              · exact safeCheckNSignaturesWithExecutorBodyCore hcode hsize hperm
                  hCheckNSignaturesWithExecutor hAccounts
              · by_cases hCheckSignatures : selIs I (safeSelBytes 7)
                · exact safeCheckSignaturesBodyCore hcode hsize hperm hCheckSignatures
                    hAccounts
                · by_cases hCheckSignaturesWithExecutor : selIs I (safeSelBytes 8)
                  · exact safeCheckSignaturesWithExecutorBodyCore hcode hsize hperm
                      hCheckSignaturesWithExecutor hAccounts
                  · by_cases hDisableModule : selIs I (safeSelBytes 9)
                    · exact safeDisableModuleBodyCore hcode hsize hperm hDisableModule
                        hAccounts
                    · by_cases hDomainSeparator : selIs I (safeSelBytes 10)
                      · exact safeDomainSeparatorBodyCore hcode hsize hperm
                          hDomainSeparator hAccounts
                      · by_cases hEnableModule : selIs I (safeSelBytes 11)
                        · exact safeEnableModuleBodyCore hcode hsize hperm hEnableModule
                            hAccounts
                        · by_cases hExecTransaction : selIs I (safeSelBytes 12)
                          · exact safeExecTransactionBodyCore hcode hsize hperm
                              hExecTransaction hAccounts
                          · by_cases hExecTransactionFromModule : selIs I (safeSelBytes 13)
                            · exact safeExecTransactionFromModuleBodyCore hcode hsize hperm
                                hExecTransactionFromModule hAccounts
                            · by_cases hExecModuleReturnData :
                                selIs I (safeSelBytes 14)
                              · exact safeExecTransactionFromModuleReturnDataBodyCore hcode
                                  hsize hperm hExecModuleReturnData hAccounts
                              · by_cases hGetModulesPaginated : selIs I (safeSelBytes 15)
                                · exact safeGetModulesPaginatedBodyCore hcode hsize hperm
                                    hGetModulesPaginated hAccounts
                                · by_cases hGetOwners : selIs I (safeSelBytes 16)
                                  · exact safeGetOwnersBodyCore hcode hsize hperm
                                      hGetOwners hAccounts
                                  · by_cases hGetStorageAt : selIs I (safeSelBytes 17)
                                    · exact safeGetStorageAtBodyCore hcode hsize hperm
                                        hGetStorageAt hAccounts
                                    · by_cases hGetThreshold : selIs I (safeSelBytes 18)
                                      · exact safeGetThresholdBodyCore hcode hsize hperm
                                          hGetThreshold hAccounts
                                      · by_cases hGetTransactionHash :
                                          selIs I (safeSelBytes 19)
                                        · exact safeGetTransactionHashBodyCore hcode hsize
                                            hperm hGetTransactionHash hAccounts
                                        · by_cases hIsModuleEnabled :
                                            selIs I (safeSelBytes 20)
                                          · exact safeIsModuleEnabledBodyCore hcode hsize
                                              hperm hIsModuleEnabled hAccounts
                                          · by_cases hIsOwner : selIs I (safeSelBytes 21)
                                            · exact safeIsOwnerBodyCore hcode hsize hperm
                                                hIsOwner hAccounts
                                            · by_cases hNonce : selIs I (safeSelBytes 22)
                                              · exact safeNonceBodyCore hcode hsize hperm
                                                  hNonce hAccounts
                                              · by_cases hRemoveOwner :
                                                  selIs I (safeSelBytes 23)
                                                · exact safeRemoveOwnerBodyCore hcode hsize
                                                    hperm hRemoveOwner hAccounts
                                                · by_cases hSetFallbackHandler :
                                                    selIs I (safeSelBytes 24)
                                                  · exact safeSetFallbackHandlerBodyCore hcode
                                                      hsize hperm hSetFallbackHandler hAccounts
                                                  · by_cases hSetGuard :
                                                      selIs I (safeSelBytes 25)
                                                    · exact safeSetGuardBodyCore hcode hsize
                                                        hperm hSetGuard hAccounts
                                                    · by_cases hSetModuleGuard :
                                                        selIs I (safeSelBytes 26)
                                                      · exact safeSetModuleGuardBodyCore hcode
                                                          hsize hperm hSetModuleGuard hAccounts
                                                      · by_cases hSetup :
                                                          selIs I (safeSelBytes 27)
                                                        · exact safeSetupBodyCore hcode hsize
                                                            hperm hSetup hAccounts
                                                        · by_cases hSignedMessages :
                                                            selIs I (safeSelBytes 28)
                                                          · exact safeSignedMessagesBodyCore
                                                              hcode hsize hperm
                                                              hSignedMessages hAccounts
                                                          · by_cases hSimulateAndRevert :
                                                              selIs I (safeSelBytes 29)
                                                            · exact
                                                                safeSimulateAndRevertBodyCore
                                                                  hcode hsize hperm
                                                                  hSimulateAndRevert
                                                                  hAccounts
                                                            · by_cases hSwapOwner :
                                                                selIs I (safeSelBytes 30)
                                                              · exact safeSwapOwnerBodyCore
                                                                  hcode hsize hperm hSwapOwner
                                                                  hAccounts
                                                              · by_cases hcalldata :
                                                                  I.calldata.size = 0
                                                                · exact safeReceiveBodyCore
                                                                    hcode hsize hperm
                                                                    hcalldata hAccounts
                                                                · exact safeFallbackBodyCore
                                                                    hcode hsize hperm
                                                                    hcalldata
                                                                    (safeNoSelectorMatches
                                                                      hVersion
                                                                      hAddOwnerWithThreshold
                                                                      hApproveHash
                                                                      hApprovedHashes
                                                                      hChangeThreshold
                                                                      hCheckNSignatures
                                                                      hCheckNSignaturesWithExecutor
                                                                      hCheckSignatures
                                                                      hCheckSignaturesWithExecutor
                                                                      hDisableModule
                                                                      hDomainSeparator
                                                                      hEnableModule
                                                                      hExecTransaction
                                                                      hExecTransactionFromModule
                                                                      hExecModuleReturnData
                                                                      hGetModulesPaginated
                                                                      hGetOwners
                                                                      hGetStorageAt
                                                                      hGetThreshold
                                                                      hGetTransactionHash
                                                                      hIsModuleEnabled
                                                                      hIsOwner
                                                                      hNonce
                                                                      hRemoveOwner
                                                                      hSetFallbackHandler
                                                                      hSetGuard
                                                                      hSetModuleGuard
                                                                      hSetup
                                                                      hSignedMessages
                                                                      hSimulateAndRevert
                                                                      hSwapOwner)
                                                                    hAccounts

theorem safeContractCorrect :
    contractEquivalence config safeCreationBytecode safeBytecode contract :=
  contractEquivalence.intro safeConstructorCorrect safeCorrect

end Benchmarks.Safe
