import Benchmarks.Dss.Jug.Constructor
import Benchmarks.Dss.Jug.Base
import Benchmarks.Dss.Jug.Deny
import Benchmarks.Dss.Jug.Drip
import Benchmarks.Dss.Jug.FileBase
import Benchmarks.Dss.Jug.FileDuty
import Benchmarks.Dss.Jug.FileVow
import Benchmarks.Dss.Jug.Ilks
import Benchmarks.Dss.Jug.Init
import Benchmarks.Dss.Jug.Rely
import Benchmarks.Dss.Jug.Vat
import Benchmarks.Dss.Jug.Vow
import Benchmarks.Dss.Jug.Wards
import Solm.Refine

/-!
# MakerDAO/Sky DSS Jug benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Jug

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem jugNonPayable {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeRefinementFor config contract
      σ σ₀ g A I := by
  exact (jugX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (jugBodyReverts_nonPayable t htmem
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem jugNoDispatch {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 12 → (jugSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (jugX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (jugDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (jugX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (jugDispatch_none_short hshort)

theorem jugNoSelectorMatches {I : ExecutionEnv}
    (hbase : ¬ selIs I (jugSelBytes 0))
    (hdeny : ¬ selIs I (jugSelBytes 1))
    (hdrip : ¬ selIs I (jugSelBytes 2))
    (hfileBase : ¬ selIs I (jugSelBytes 3))
    (hfileDuty : ¬ selIs I (jugSelBytes 4))
    (hfileVow : ¬ selIs I (jugSelBytes 5))
    (hilks : ¬ selIs I (jugSelBytes 6))
    (hinit : ¬ selIs I (jugSelBytes 7))
    (hrely : ¬ selIs I (jugSelBytes 8))
    (hvat : ¬ selIs I (jugSelBytes 9))
    (hvow : ¬ selIs I (jugSelBytes 10))
    (hwards : ¬ selIs I (jugSelBytes 11)) :
    ∀ i, i < 12 → (jugSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, jugSelBytes] using hbase
  · simpa [selIs, jugSelBytes] using hdeny
  · simpa [selIs, jugSelBytes] using hdrip
  · simpa [selIs, jugSelBytes] using hfileBase
  · simpa [selIs, jugSelBytes] using hfileDuty
  · simpa [selIs, jugSelBytes] using hfileVow
  · simpa [selIs, jugSelBytes] using hilks
  · simpa [selIs, jugSelBytes] using hinit
  · simpa [selIs, jugSelBytes] using hrely
  · simpa [selIs, jugSelBytes] using hvat
  · simpa [selIs, jugSelBytes] using hvow
  · simpa [selIs, jugSelBytes] using hwards

theorem jugCorrect :
    runtimeRefinement config jugBytecode contract := by
  refine runtimeRefinement.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbase : selIs I (jugSelBytes 0)
    · exact jugBaseBody hcode hsize hwv hbase
    · by_cases hdeny : selIs I (jugSelBytes 1)
      · exact jugDenyBodyAnyPerm hcode hsize hwv hdeny
      · by_cases hdrip : selIs I (jugSelBytes 2)
        · exact jugDripBody hcode hsize hwv hdrip
        · by_cases hfileBase : selIs I (jugSelBytes 3)
          · exact jugFileBaseBodyAnyPerm hcode hsize hwv hfileBase
          · by_cases hfileDuty : selIs I (jugSelBytes 4)
            · exact jugFileDutyBodyAnyPerm hcode hsize hwv hfileDuty
            · by_cases hfileVow : selIs I (jugSelBytes 5)
              · exact jugFileVowBodyAnyPerm hcode hsize hwv hfileVow
              · by_cases hilks : selIs I (jugSelBytes 6)
                · exact jugIlksBody hcode hsize hwv hilks
                · by_cases hinit : selIs I (jugSelBytes 7)
                  · exact jugInitBodyAnyPerm hcode hsize hwv hinit
                  · by_cases hrely : selIs I (jugSelBytes 8)
                    · exact jugRelyBodyAnyPerm hcode hsize hwv hrely
                    · by_cases hvat : selIs I (jugSelBytes 9)
                      · exact jugVatBody hcode hsize hwv hvat
                      · by_cases hvow : selIs I (jugSelBytes 10)
                        · exact jugVowBody hcode hsize hwv hvow
                        · by_cases hwards : selIs I (jugSelBytes 11)
                          · exact jugWardsBody hcode hsize hwv hwards
                          · exact jugNoDispatch hcode hsize hwv
                              (jugNoSelectorMatches hbase hdeny hdrip hfileBase hfileDuty
                                hfileVow hilks hinit hrely hvat hvow hwards)

  · exact jugNonPayable hcode hwv

theorem jugContractCorrect :
    contractRefinement config jugCreationBytecode contract :=
  contractRefinement.of_constant jugConstructorCorrect jugCorrect

end Benchmarks.Dss.Jug
