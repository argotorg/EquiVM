import Benchmarks.Dss.Pot.Constructor
import Benchmarks.Dss.Pot.PieTotal
import Benchmarks.Dss.Pot.Cage
import Benchmarks.Dss.Pot.Chi
import Benchmarks.Dss.Pot.Deny
import Benchmarks.Dss.Pot.Drip
import Benchmarks.Dss.Pot.Dsr
import Benchmarks.Dss.Pot.Exit
import Benchmarks.Dss.Pot.FileDsr
import Benchmarks.Dss.Pot.FileVow
import Benchmarks.Dss.Pot.Join
import Benchmarks.Dss.Pot.Live
import Benchmarks.Dss.Pot.Pie
import Benchmarks.Dss.Pot.Rely
import Benchmarks.Dss.Pot.Rho
import Benchmarks.Dss.Pot.Vat
import Benchmarks.Dss.Pot.Vow
import Benchmarks.Dss.Pot.Wards
import Solm.Refine

/-!
# MakerDAO/Sky DSS Pot benchmark correctness

Thin top-level: the dispatcher driver routes each selector to its per-function `…Body` lemma,
adds the shared revert paths (non-payable guard, no-dispatch), and packages the constructor with
the runtime target into the whole-contract equivalence.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem potNonPayable {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact (potX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (potBodyReverts_nonPayable t htmem
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem potNoDispatch {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 17 → (potSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (potX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (potDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (potX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (potDispatch_none_short hshort)

theorem potNoSelectorMatches {I : ExecutionEnv}
    (h0 : ¬ selIs I (potSelBytes 0)) (h1 : ¬ selIs I (potSelBytes 1))
    (h2 : ¬ selIs I (potSelBytes 2)) (h3 : ¬ selIs I (potSelBytes 3))
    (h4 : ¬ selIs I (potSelBytes 4)) (h5 : ¬ selIs I (potSelBytes 5))
    (h6 : ¬ selIs I (potSelBytes 6)) (h7 : ¬ selIs I (potSelBytes 7))
    (h8 : ¬ selIs I (potSelBytes 8)) (h9 : ¬ selIs I (potSelBytes 9))
    (h10 : ¬ selIs I (potSelBytes 10)) (h11 : ¬ selIs I (potSelBytes 11))
    (h12 : ¬ selIs I (potSelBytes 12)) (h13 : ¬ selIs I (potSelBytes 13))
    (h14 : ¬ selIs I (potSelBytes 14)) (h15 : ¬ selIs I (potSelBytes 15))
    (h16 : ¬ selIs I (potSelBytes 16)) :
    ∀ i, i < 17 → (potSelBytes i == I.calldata.extract 0 4) = false := by
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

theorem potCorrect :
    runtimeRefinement config potBytecode contract := by
  refine runtimeRefinement.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases h0 : selIs I (potSelBytes 0)
    · exact potPieTotalBody hcode hsize hwv h0
    · by_cases h1 : selIs I (potSelBytes 1)
      · exact potCageBodyAnyPerm hcode hsize hwv h1
      · by_cases h2 : selIs I (potSelBytes 2)
        · exact potChiBody hcode hsize hwv h2
        · by_cases h3 : selIs I (potSelBytes 3)
          · exact potDenyBodyAnyPerm hcode hsize hwv h3
          · by_cases h4 : selIs I (potSelBytes 4)
            · exact potDripBodyAnyPerm hcode hsize hwv h4
            · by_cases h5 : selIs I (potSelBytes 5)
              · exact potDsrBody hcode hsize hwv h5
              · by_cases h6 : selIs I (potSelBytes 6)
                · exact potExitBodyAnyPerm hcode hsize hwv h6
                · by_cases h7 : selIs I (potSelBytes 7)
                  · exact potFileDsrBodyAnyPerm hcode hsize hwv h7
                  · by_cases h8 : selIs I (potSelBytes 8)
                    · exact potFileVowBodyAnyPerm hcode hsize hwv h8
                    · by_cases h9 : selIs I (potSelBytes 9)
                      · exact potJoinBodyAnyPerm hcode hsize hwv h9
                      · by_cases h10 : selIs I (potSelBytes 10)
                        · exact potLiveBody hcode hsize hwv h10
                        · by_cases h11 : selIs I (potSelBytes 11)
                          · exact potPieBody hcode hsize hwv h11
                          · by_cases h12 : selIs I (potSelBytes 12)
                            · exact potRelyBodyAnyPerm hcode hsize hwv h12
                            · by_cases h13 : selIs I (potSelBytes 13)
                              · exact potRhoBody hcode hsize hwv h13
                              · by_cases h14 : selIs I (potSelBytes 14)
                                · exact potVatBody hcode hsize hwv h14
                                · by_cases h15 : selIs I (potSelBytes 15)
                                  · exact potVowBody hcode hsize hwv h15
                                  · by_cases h16 : selIs I (potSelBytes 16)
                                    · exact potWardsBody hcode hsize hwv h16
                                    · exact potNoDispatch hcode hsize hwv
                                        (potNoSelectorMatches h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
                                          h11 h12 h13 h14 h15 h16)

  · exact potNonPayable hcode hwv

theorem potContractCorrect :
    contractRefinement config potCreationBytecode contract :=
  contractRefinement.of_constant potConstructorCorrect potCorrect

end Benchmarks.Dss.Pot
