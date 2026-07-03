import Benchmarks.Dss.Dai.Constructor
import Benchmarks.Dss.Dai.Allowance
import Benchmarks.Dss.Dai.Approve
import Benchmarks.Dss.Dai.BalanceOf
import Benchmarks.Dss.Dai.Burn
import Benchmarks.Dss.Dai.Decimals
import Benchmarks.Dss.Dai.Deny
import Benchmarks.Dss.Dai.DomainSeparator
import Benchmarks.Dss.Dai.Mint
import Benchmarks.Dss.Dai.Move
import Benchmarks.Dss.Dai.Name
import Benchmarks.Dss.Dai.Nonces
import Benchmarks.Dss.Dai.Permit
import Benchmarks.Dss.Dai.PermitTypehash
import Benchmarks.Dss.Dai.Pull
import Benchmarks.Dss.Dai.Push
import Benchmarks.Dss.Dai.Rely
import Benchmarks.Dss.Dai.Symbol
import Benchmarks.Dss.Dai.TotalSupply
import Benchmarks.Dss.Dai.Transfer
import Benchmarks.Dss.Dai.TransferFrom
import Benchmarks.Dss.Dai.Version
import Benchmarks.Dss.Dai.Wards

/-!
# MakerDAO DSS Dai benchmark correctness scaffold

The top-level runtime theorem performs the shared Solidity dispatcher split: non-payable guard,
selector-size guard, and one branch per ABI selector.  Each matched branch delegates to that
function's `…BodyCore` lemma in its own file.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Dai

/-- `callvalue != 0` reverts on both sides for every Dai transition. -/
theorem daiNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = daiBytecode) (_hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

/-- Calldata shorter than a selector reverts before runtime dispatch reaches a body. -/
theorem daiShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (_hwv : I.weiValue = ⟨0⟩) (_hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

/-- No selector matches: Solm dispatch fails and the bytecode falls through to the revert stub. -/
theorem daiNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (_hwv : I.weiValue = ⟨0⟩)
    (_hnm : ∀ i, i < 22 → (daiSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  sorry

theorem daiCorrect :
    runtimeEquivalence!?! config daiBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I (daiSelBytes 0)
      · exact daiAllowanceBodyCore hcode hsize hperm hwv h0 hAccounts
      · by_cases h1 : selIs I (daiSelBytes 1)
        · exact daiApproveBodyCore hcode hsize hperm hwv h1 hAccounts
        · by_cases h2 : selIs I (daiSelBytes 2)
          · exact daiBalanceOfBodyCore hcode hsize hperm hwv h2 hAccounts
          · by_cases h3 : selIs I (daiSelBytes 3)
            · exact daiBurnBodyCore hcode hsize hperm hwv h3 hAccounts
            · by_cases h4 : selIs I (daiSelBytes 4)
              · exact daiDecimalsBodyCore hcode hsize hperm hwv h4 hAccounts
              · by_cases h5 : selIs I (daiSelBytes 5)
                · exact daiDenyBodyCore hcode hsize hperm hwv h5 hAccounts
                · by_cases h6 : selIs I (daiSelBytes 6)
                  · exact daiDomainSeparatorBodyCore hcode hsize hperm hwv h6 hAccounts
                  · by_cases h7 : selIs I (daiSelBytes 7)
                    · exact daiMintBodyCore hcode hsize hperm hwv h7 hAccounts
                    · by_cases h8 : selIs I (daiSelBytes 8)
                      · exact daiMoveBodyCore hcode hsize hperm hwv h8 hAccounts
                      · by_cases h9 : selIs I (daiSelBytes 9)
                        · exact daiNameBodyCore hcode hsize hperm hwv h9 hAccounts
                        · by_cases h10 : selIs I (daiSelBytes 10)
                          · exact daiNoncesBodyCore hcode hsize hperm hwv h10 hAccounts
                          · by_cases h11 : selIs I (daiSelBytes 11)
                            · exact daiPermitBodyCore hcode hsize hperm hwv h11 hAccounts
                            · by_cases h12 : selIs I (daiSelBytes 12)
                              · exact daiPermitTypehashBodyCore hcode hsize hperm hwv h12 hAccounts
                              · by_cases h13 : selIs I (daiSelBytes 13)
                                · exact daiPullBodyCore hcode hsize hperm hwv h13 hAccounts
                                · by_cases h14 : selIs I (daiSelBytes 14)
                                  · exact daiPushBodyCore hcode hsize hperm hwv h14 hAccounts
                                  · by_cases h15 : selIs I (daiSelBytes 15)
                                    · exact daiRelyBodyCore hcode hsize hperm hwv h15 hAccounts
                                    · by_cases h16 : selIs I (daiSelBytes 16)
                                      · exact daiSymbolBodyCore hcode hsize hperm hwv h16 hAccounts
                                      · by_cases h17 : selIs I (daiSelBytes 17)
                                        · exact daiTotalSupplyBodyCore hcode hsize hperm hwv h17 hAccounts
                                        · by_cases h18 : selIs I (daiSelBytes 18)
                                          · exact daiTransferBodyCore hcode hsize hperm hwv h18 hAccounts
                                          · by_cases h19 : selIs I (daiSelBytes 19)
                                            · exact daiTransferFromBodyCore hcode hsize hperm hwv h19 hAccounts
                                            · by_cases h20 : selIs I (daiSelBytes 20)
                                              · exact daiVersionBodyCore hcode hsize hperm hwv h20 hAccounts
                                              · by_cases h21 : selIs I (daiSelBytes 21)
                                                · exact daiWardsBodyCore hcode hsize hperm hwv h21 hAccounts
                                                · refine daiNoDispatch hcode hsize hperm hwv ?_
                                                  intro i hi
                                                  interval_cases i
                                                  · simpa [selIs, daiSelBytes] using h0
                                                  · simpa [selIs, daiSelBytes] using h1
                                                  · simpa [selIs, daiSelBytes] using h2
                                                  · simpa [selIs, daiSelBytes] using h3
                                                  · simpa [selIs, daiSelBytes] using h4
                                                  · simpa [selIs, daiSelBytes] using h5
                                                  · simpa [selIs, daiSelBytes] using h6
                                                  · simpa [selIs, daiSelBytes] using h7
                                                  · simpa [selIs, daiSelBytes] using h8
                                                  · simpa [selIs, daiSelBytes] using h9
                                                  · simpa [selIs, daiSelBytes] using h10
                                                  · simpa [selIs, daiSelBytes] using h11
                                                  · simpa [selIs, daiSelBytes] using h12
                                                  · simpa [selIs, daiSelBytes] using h13
                                                  · simpa [selIs, daiSelBytes] using h14
                                                  · simpa [selIs, daiSelBytes] using h15
                                                  · simpa [selIs, daiSelBytes] using h16
                                                  · simpa [selIs, daiSelBytes] using h17
                                                  · simpa [selIs, daiSelBytes] using h18
                                                  · simpa [selIs, daiSelBytes] using h19
                                                  · simpa [selIs, daiSelBytes] using h20
                                                  · simpa [selIs, daiSelBytes] using h21
    · exact daiShortRevert hcode hsize hperm hwv (by omega)
  · exact daiNonPayable hcode hwv

theorem daiContractCorrect :
    contractEquivalence config daiCreationBytecode daiBytecode contract :=
  contractEquivalence.intro daiConstructorCorrect daiCorrect

end Benchmarks.Dss.Dai
