import Benchmarks.Dss.Vat.Cage
import Benchmarks.Dss.Vat.Can
import Benchmarks.Dss.Vat.Constructor
import Benchmarks.Dss.Vat.Dai
import Benchmarks.Dss.Vat.Debt
import Benchmarks.Dss.Vat.Deny
import Benchmarks.Dss.Vat.FileIlk
import Benchmarks.Dss.Vat.FileLine
import Benchmarks.Dss.Vat.Flux
import Benchmarks.Dss.Vat.Fold
import Benchmarks.Dss.Vat.Fork
import Benchmarks.Dss.Vat.Frob
import Benchmarks.Dss.Vat.Gem
import Benchmarks.Dss.Vat.Grab
import Benchmarks.Dss.Vat.Heal
import Benchmarks.Dss.Vat.Hope
import Benchmarks.Dss.Vat.Ilks
import Benchmarks.Dss.Vat.Init
import Benchmarks.Dss.Vat.Line
import Benchmarks.Dss.Vat.Live
import Benchmarks.Dss.Vat.Move
import Benchmarks.Dss.Vat.Nope
import Benchmarks.Dss.Vat.Rely
import Benchmarks.Dss.Vat.Sin
import Benchmarks.Dss.Vat.Slip
import Benchmarks.Dss.Vat.Suck
import Benchmarks.Dss.Vat.Urns
import Benchmarks.Dss.Vat.Vice
import Benchmarks.Dss.Vat.Wards
import Reasoning.Refinement
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vat benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem vatNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (vatX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (vatBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector (`size < 4`) reverts before Solm dispatch. -/
theorem vatShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (vatX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (vatDispatch_none_short hsz)

/-- No selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem vatNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 28 → (vatSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (vatX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (vatDispatch_none_nomatch hnm)
  · exact vatShortRevert hcode hsize ‹I.perm = true› hwv (by omega)

theorem vatNoSelectorMatches {I : ExecutionEnv}
    (hLine : ¬ selIs I (vatSelBytes 0))
    (hcage : ¬ selIs I (vatSelBytes 1))
    (hcan : ¬ selIs I (vatSelBytes 2))
    (hdai : ¬ selIs I (vatSelBytes 3))
    (hdebt : ¬ selIs I (vatSelBytes 4))
    (hdeny : ¬ selIs I (vatSelBytes 5))
    (hfileIlk : ¬ selIs I (vatSelBytes 6))
    (hfileLine : ¬ selIs I (vatSelBytes 7))
    (hflux : ¬ selIs I (vatSelBytes 8))
    (hfold : ¬ selIs I (vatSelBytes 9))
    (hfork : ¬ selIs I (vatSelBytes 10))
    (hfrob : ¬ selIs I (vatSelBytes 11))
    (hgem : ¬ selIs I (vatSelBytes 12))
    (hgrab : ¬ selIs I (vatSelBytes 13))
    (hheal : ¬ selIs I (vatSelBytes 14))
    (hhope : ¬ selIs I (vatSelBytes 15))
    (hilks : ¬ selIs I (vatSelBytes 16))
    (hinit : ¬ selIs I (vatSelBytes 17))
    (hlive : ¬ selIs I (vatSelBytes 18))
    (hmove : ¬ selIs I (vatSelBytes 19))
    (hnope : ¬ selIs I (vatSelBytes 20))
    (hrely : ¬ selIs I (vatSelBytes 21))
    (hsin : ¬ selIs I (vatSelBytes 22))
    (hslip : ¬ selIs I (vatSelBytes 23))
    (hsuck : ¬ selIs I (vatSelBytes 24))
    (hurns : ¬ selIs I (vatSelBytes 25))
    (hvice : ¬ selIs I (vatSelBytes 26))
    (hwards : ¬ selIs I (vatSelBytes 27)) :
    ∀ i, i < 28 → (vatSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs] using hLine
  · simpa [selIs] using hcage
  · simpa [selIs] using hcan
  · simpa [selIs] using hdai
  · simpa [selIs] using hdebt
  · simpa [selIs] using hdeny
  · simpa [selIs] using hfileIlk
  · simpa [selIs] using hfileLine
  · simpa [selIs] using hflux
  · simpa [selIs] using hfold
  · simpa [selIs] using hfork
  · simpa [selIs] using hfrob
  · simpa [selIs] using hgem
  · simpa [selIs] using hgrab
  · simpa [selIs] using hheal
  · simpa [selIs] using hhope
  · simpa [selIs] using hilks
  · simpa [selIs] using hinit
  · simpa [selIs] using hlive
  · simpa [selIs] using hmove
  · simpa [selIs] using hnope
  · simpa [selIs] using hrely
  · simpa [selIs] using hsin
  · simpa [selIs] using hslip
  · simpa [selIs] using hsuck
  · simpa [selIs] using hurns
  · simpa [selIs] using hvice
  · simpa [selIs] using hwards

theorem vatCorrect :
    runtimeEquivalence config vatBytecode contract := by
  refine runtimeEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hLine : selIs I (vatSelBytes 0)
    · exact vatLineBodyCore hcode hsize hperm hwv hLine hAccounts
    · by_cases hcage : selIs I (vatSelBytes 1)
      · exact vatCageBodyCore hcode hsize hperm hwv hcage hAccounts
      · by_cases hcan : selIs I (vatSelBytes 2)
        · exact vatCanBodyCore hcode hsize hperm hwv hcan hAccounts
        · by_cases hdai : selIs I (vatSelBytes 3)
          · exact vatDaiBodyCore hcode hsize hperm hwv hdai hAccounts
          · by_cases hdebt : selIs I (vatSelBytes 4)
            · exact vatDebtBodyCore hcode hsize hperm hwv hdebt hAccounts
            · by_cases hdeny : selIs I (vatSelBytes 5)
              · exact vatDenyBodyCore hcode hsize hperm hwv hdeny hAccounts
              · by_cases hfileIlk : selIs I (vatSelBytes 6)
                · exact vatFileIlkBodyCore hcode hsize hperm hwv hfileIlk hAccounts
                · by_cases hfileLine : selIs I (vatSelBytes 7)
                  · exact vatFileLineBodyCore hcode hsize hperm hwv hfileLine hAccounts
                  · by_cases hflux : selIs I (vatSelBytes 8)
                    · exact vatFluxBodyCore hcode hsize hperm hwv hflux hAccounts
                    · by_cases hfold : selIs I (vatSelBytes 9)
                      · exact vatFoldBodyCore hcode hsize hperm hwv hfold hAccounts
                      · by_cases hfork : selIs I (vatSelBytes 10)
                        · exact vatForkBodyCore hcode hsize hperm hwv hfork hAccounts
                        · by_cases hfrob : selIs I (vatSelBytes 11)
                          · exact vatFrobBodyCore hcode hsize hperm hwv hfrob hAccounts
                          · by_cases hgem : selIs I (vatSelBytes 12)
                            · exact vatGemBodyCore hcode hsize hperm hwv hgem hAccounts
                            · by_cases hgrab : selIs I (vatSelBytes 13)
                              · exact vatGrabBodyCore hcode hsize hperm hwv hgrab hAccounts
                              · by_cases hheal : selIs I (vatSelBytes 14)
                                · exact vatHealBodyCore hcode hsize hperm hwv hheal hAccounts
                                · by_cases hhope : selIs I (vatSelBytes 15)
                                  · exact vatHopeBodyCore hcode hsize hperm hwv hhope hAccounts
                                  · by_cases hilks : selIs I (vatSelBytes 16)
                                    · exact vatIlksBodyCore hcode hsize hperm hwv hilks hAccounts
                                    · by_cases hinit : selIs I (vatSelBytes 17)
                                      · exact vatInitBodyCore hcode hsize hperm hwv hinit hAccounts
                                      · by_cases hlive : selIs I (vatSelBytes 18)
                                        · exact vatLiveBodyCore hcode hsize hperm hwv hlive hAccounts
                                        · by_cases hmove : selIs I (vatSelBytes 19)
                                          · exact vatMoveBodyCore hcode hsize hperm hwv hmove hAccounts
                                          · by_cases hnope : selIs I (vatSelBytes 20)
                                            · exact vatNopeBodyCore hcode hsize hperm hwv hnope hAccounts
                                            · by_cases hrely : selIs I (vatSelBytes 21)
                                              · exact vatRelyBodyCore hcode hsize hperm hwv hrely hAccounts
                                              · by_cases hsin : selIs I (vatSelBytes 22)
                                                · exact vatSinBodyCore hcode hsize hperm hwv hsin hAccounts
                                                · by_cases hslip : selIs I (vatSelBytes 23)
                                                  · exact vatSlipBodyCore hcode hsize hperm hwv hslip hAccounts
                                                  · by_cases hsuck : selIs I (vatSelBytes 24)
                                                    · exact vatSuckBodyCore hcode hsize hperm hwv hsuck hAccounts
                                                    · by_cases hurns : selIs I (vatSelBytes 25)
                                                      · exact vatUrnsBodyCore hcode hsize hperm hwv hurns hAccounts
                                                      · by_cases hvice : selIs I (vatSelBytes 26)
                                                        · exact vatViceBodyCore hcode hsize hperm hwv hvice hAccounts
                                                        · by_cases hwards : selIs I (vatSelBytes 27)
                                                          · exact vatWardsBodyCore hcode hsize hperm hwv hwards hAccounts
                                                          · exact vatNoDispatch hcode hsize hperm hwv
                                                              (vatNoSelectorMatches hLine hcage hcan
                                                                hdai hdebt hdeny hfileIlk hfileLine
                                                                hflux hfold hfork hfrob hgem hgrab
                                                                hheal hhope hilks hinit hlive hmove
                                                                hnope hrely hsin hslip hsuck hurns
                                                                hvice hwards)
                                                              hAccounts
  · exact vatNonPayable hcode hwv

theorem vatContractCorrect :
    contractEquivalence config vatCreationBytecode vatBytecode contract :=
  contractEquivalence.intro vatConstructorCorrect vatCorrect

end Benchmarks.Dss.Vat
