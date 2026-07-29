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
import Solm.Equiv

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
theorem jugNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
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
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem jugNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 12 → (jugSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
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
    runtimeEquivalence config jugBytecode contract := by
  refine runtimeEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbase : selIs I (jugSelBytes 0)
    · exact jugBaseBody hcode hsize hperm hwv hbase hAccounts
    · by_cases hdeny : selIs I (jugSelBytes 1)
      · exact jugDenyBody hcode hsize hperm hwv hdeny hAccounts
      · by_cases hdrip : selIs I (jugSelBytes 2)
        · exact jugDripBody hcode hsize hperm hwv hdrip hAccounts
        · by_cases hfileBase : selIs I (jugSelBytes 3)
          · exact jugFileBaseBody hcode hsize hperm hwv hfileBase hAccounts
          · by_cases hfileDuty : selIs I (jugSelBytes 4)
            · exact jugFileDutyBody hcode hsize hperm hwv hfileDuty hAccounts
            · by_cases hfileVow : selIs I (jugSelBytes 5)
              · exact jugFileVowBody hcode hsize hperm hwv hfileVow hAccounts
              · by_cases hilks : selIs I (jugSelBytes 6)
                · exact jugIlksBody hcode hsize hperm hwv hilks hAccounts
                · by_cases hinit : selIs I (jugSelBytes 7)
                  · exact jugInitBody hcode hsize hperm hwv hinit hAccounts
                  · by_cases hrely : selIs I (jugSelBytes 8)
                    · exact jugRelyBody hcode hsize hperm hwv hrely hAccounts
                    · by_cases hvat : selIs I (jugSelBytes 9)
                      · exact jugVatBody hcode hsize hperm hwv hvat hAccounts
                      · by_cases hvow : selIs I (jugSelBytes 10)
                        · exact jugVowBody hcode hsize hperm hwv hvow hAccounts
                        · by_cases hwards : selIs I (jugSelBytes 11)
                          · exact jugWardsBody hcode hsize hperm hwv hwards hAccounts
                          · exact jugNoDispatch hcode hsize hperm hwv
                              (jugNoSelectorMatches hbase hdeny hdrip hfileBase hfileDuty
                                hfileVow hilks hinit hrely hvat hvow hwards)
                              hAccounts
  · exact jugNonPayable hcode hwv

theorem jugContractCorrect :
    contractEquivalence config jugCreationBytecode jugBytecode contract :=
  contractEquivalence.intro jugConstructorCorrect jugCorrect

end Benchmarks.Dss.Jug
