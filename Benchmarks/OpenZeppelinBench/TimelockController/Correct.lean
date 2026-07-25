import Benchmarks.OpenZeppelinBench.TimelockController.CancellerRole
import Benchmarks.OpenZeppelinBench.TimelockController.Cancel
import Benchmarks.OpenZeppelinBench.TimelockController.DefaultAdminRole
import Benchmarks.OpenZeppelinBench.TimelockController.ExecuteBatch
import Benchmarks.OpenZeppelinBench.TimelockController.Execute
import Benchmarks.OpenZeppelinBench.TimelockController.ExecutorRole
import Benchmarks.OpenZeppelinBench.TimelockController.GetMinDelay
import Benchmarks.OpenZeppelinBench.TimelockController.GetOperationState
import Benchmarks.OpenZeppelinBench.TimelockController.GetRoleAdmin
import Benchmarks.OpenZeppelinBench.TimelockController.GetTimestamp
import Benchmarks.OpenZeppelinBench.TimelockController.GrantRole
import Benchmarks.OpenZeppelinBench.TimelockController.HasRole
import Benchmarks.OpenZeppelinBench.TimelockController.HashOperationBatch
import Benchmarks.OpenZeppelinBench.TimelockController.HashOperation
import Benchmarks.OpenZeppelinBench.TimelockController.IsOperationDone
import Benchmarks.OpenZeppelinBench.TimelockController.IsOperationPending
import Benchmarks.OpenZeppelinBench.TimelockController.IsOperationReady
import Benchmarks.OpenZeppelinBench.TimelockController.IsOperation
import Benchmarks.OpenZeppelinBench.TimelockController.OnERC1155BatchReceived
import Benchmarks.OpenZeppelinBench.TimelockController.OnERC1155Received
import Benchmarks.OpenZeppelinBench.TimelockController.OnERC721Received
import Benchmarks.OpenZeppelinBench.TimelockController.ProposerRole
import Benchmarks.OpenZeppelinBench.TimelockController.RenounceRole
import Benchmarks.OpenZeppelinBench.TimelockController.RevokeRole
import Benchmarks.OpenZeppelinBench.TimelockController.ScheduleBatch
import Benchmarks.OpenZeppelinBench.TimelockController.Schedule
import Benchmarks.OpenZeppelinBench.TimelockController.SupportsInterface
import Benchmarks.OpenZeppelinBench.TimelockController.UpdateDelay
import Benchmarks.OpenZeppelinBench.TimelockController.Fallback
import Benchmarks.OpenZeppelinBench.TimelockController.Constructor
import Solm.Equiv

/-!
# OpenZeppelin TimelockController benchmark correctness

Thin top-level: the balanced depth-3 binary-search dispatcher routes each of the 28 selectors to
that function's `…BodyCore`; a non-matching selector (calldata ≥ 4) reverts (no fallback), and
calldata < 4 routes to the payable `receive` (empty calldata) or reverts (1–3 bytes).  There is no
shared callvalue guard — each non-payable function guards its own callvalue.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.TimelockController

theorem timelockControllerBenchCorrect :
    runtimeEquivalence config timelockControllerBenchBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases h0 : selIs I (tlcSelBytes 0)
    · exact tlcCancellerRoleBodyCore hcode hsize hperm h0 hAccounts
    · by_cases h1 : selIs I (tlcSelBytes 1)
      · exact tlcCancelBodyCore hcode hsize hperm h1 hAccounts
      · by_cases h2 : selIs I (tlcSelBytes 2)
        · exact tlcDefaultAdminRoleBodyCore hcode hsize hperm h2 hAccounts
        · by_cases h3 : selIs I (tlcSelBytes 3)
          · exact tlcExecuteBatchBodyCore hcode hsize hperm h3 hAccounts
          · by_cases h4 : selIs I (tlcSelBytes 4)
            · exact tlcExecuteBodyCore hcode hsize hperm h4 hAccounts
            · by_cases h5 : selIs I (tlcSelBytes 5)
              · exact tlcExecutorRoleBodyCore hcode hsize hperm h5 hAccounts
              · by_cases h6 : selIs I (tlcSelBytes 6)
                · exact tlcGetMinDelayBodyCore hcode hsize hperm h6 hAccounts
                · by_cases h7 : selIs I (tlcSelBytes 7)
                  · exact tlcGetOperationStateBodyCore hcode hsize hperm h7 hAccounts
                  · by_cases h8 : selIs I (tlcSelBytes 8)
                    · exact tlcGetRoleAdminBodyCore hcode hsize hperm h8 hAccounts
                    · by_cases h9 : selIs I (tlcSelBytes 9)
                      · exact tlcGetTimestampBodyCore hcode hsize hperm h9 hAccounts
                      · by_cases h10 : selIs I (tlcSelBytes 10)
                        · exact tlcGrantRoleBodyCore hcode hsize hperm h10 hAccounts
                        · by_cases h11 : selIs I (tlcSelBytes 11)
                          · exact tlcHasRoleBodyCore hcode hsize hperm h11 hAccounts
                          · by_cases h12 : selIs I (tlcSelBytes 12)
                            · exact tlcHashOperationBatchBodyCore hcode hsize hperm h12 hAccounts
                            · by_cases h13 : selIs I (tlcSelBytes 13)
                              · exact tlcHashOperationBodyCore hcode hsize hperm h13 hAccounts
                              · by_cases h14 : selIs I (tlcSelBytes 14)
                                · exact tlcIsOperationDoneBodyCore hcode hsize hperm h14 hAccounts
                                · by_cases h15 : selIs I (tlcSelBytes 15)
                                  · exact tlcIsOperationPendingBodyCore hcode hsize hperm h15 hAccounts
                                  · by_cases h16 : selIs I (tlcSelBytes 16)
                                    · exact tlcIsOperationReadyBodyCore hcode hsize hperm h16 hAccounts
                                    · by_cases h17 : selIs I (tlcSelBytes 17)
                                      · exact tlcIsOperationBodyCore hcode hsize hperm h17 hAccounts
                                      · by_cases h18 : selIs I (tlcSelBytes 18)
                                        · exact tlcOnERC1155BatchReceivedBodyCore hcode hsize hperm h18 hAccounts
                                        · by_cases h19 : selIs I (tlcSelBytes 19)
                                          · exact tlcOnERC1155ReceivedBodyCore hcode hsize hperm h19 hAccounts
                                          · by_cases h20 : selIs I (tlcSelBytes 20)
                                            · exact tlcOnERC721ReceivedBodyCore hcode hsize hperm h20 hAccounts
                                            · by_cases h21 : selIs I (tlcSelBytes 21)
                                              · exact tlcProposerRoleBodyCore hcode hsize hperm h21 hAccounts
                                              · by_cases h22 : selIs I (tlcSelBytes 22)
                                                · exact tlcRenounceRoleBodyCore hcode hsize hperm h22 hAccounts
                                                · by_cases h23 : selIs I (tlcSelBytes 23)
                                                  · exact tlcRevokeRoleBodyCore hcode hsize hperm h23 hAccounts
                                                  · by_cases h24 : selIs I (tlcSelBytes 24)
                                                    · exact tlcScheduleBatchBodyCore hcode hsize hperm h24 hAccounts
                                                    · by_cases h25 : selIs I (tlcSelBytes 25)
                                                      · exact tlcScheduleBodyCore hcode hsize hperm h25 hAccounts
                                                      · by_cases h26 : selIs I (tlcSelBytes 26)
                                                        · exact tlcSupportsInterfaceBodyCore hcode hsize hperm h26 hAccounts
                                                        · by_cases h27 : selIs I (tlcSelBytes 27)
                                                          · exact tlcUpdateDelayBodyCore hcode hsize hperm h27 hAccounts
                                                          · refine tlcNoMatchBodyCore hcode hsize hperm hsz ?_ hAccounts
                                                            intro i hi
                                                            interval_cases i
                                                            · simpa [selIs] using h0
                                                            · simpa [selIs] using h1
                                                            · simpa [selIs] using h2
                                                            · simpa [selIs] using h3
                                                            · simpa [selIs] using h4
                                                            · simpa [selIs] using h5
                                                            · simpa [selIs] using h6
                                                            · simpa [selIs] using h7
                                                            · simpa [selIs] using h8
                                                            · simpa [selIs] using h9
                                                            · simpa [selIs] using h10
                                                            · simpa [selIs] using h11
                                                            · simpa [selIs] using h12
                                                            · simpa [selIs] using h13
                                                            · simpa [selIs] using h14
                                                            · simpa [selIs] using h15
                                                            · simpa [selIs] using h16
                                                            · simpa [selIs] using h17
                                                            · simpa [selIs] using h18
                                                            · simpa [selIs] using h19
                                                            · simpa [selIs] using h20
                                                            · simpa [selIs] using h21
                                                            · simpa [selIs] using h22
                                                            · simpa [selIs] using h23
                                                            · simpa [selIs] using h24
                                                            · simpa [selIs] using h25
                                                            · simpa [selIs] using h26
                                                            · simpa [selIs] using h27
  · exact tlcShortBodyCore hcode hsize hperm (by omega) hAccounts

theorem timelockControllerBenchContractCorrect :
    contractEquivalence config timelockControllerBenchCreationBytecode
      timelockControllerBenchBytecode contract :=
  contractEquivalence.intro timelockControllerBenchConstructorCorrect timelockControllerBenchCorrect

end OpenZeppelinBench.TimelockController
