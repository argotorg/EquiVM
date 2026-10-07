import Benchmarks.Dss.Cat.Bite
import Benchmarks.Dss.Cat.Box
import Benchmarks.Dss.Cat.Cage
import Benchmarks.Dss.Cat.Claw
import Benchmarks.Dss.Cat.Constructor
import Benchmarks.Dss.Cat.Deny
import Benchmarks.Dss.Cat.FileAddress
import Benchmarks.Dss.Cat.FileIlkFlip
import Benchmarks.Dss.Cat.FileIlkUint
import Benchmarks.Dss.Cat.FileUint
import Benchmarks.Dss.Cat.Ilks
import Benchmarks.Dss.Cat.Litter
import Benchmarks.Dss.Cat.Live
import Benchmarks.Dss.Cat.Rely
import Benchmarks.Dss.Cat.Vat
import Benchmarks.Dss.Cat.Vow
import Benchmarks.Dss.Cat.Wards
import Solm.Refine

/-!
# MakerDAO/Sky DSS Cat benchmark correctness

Top-level runtime-equivalence dispatcher: routes each selector to its per-function `cat…Body`
refinement lemma, and handles the shared revert paths (non-payable guard, short calldata, unknown
selector). The whole-contract wrapper combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem catNonPayable {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeRefinementFor config contract
      σ σ₀ g A I := by
  exact (catX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (catBodyReverts_nonPayable t htmem
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector (`size < 4`) reverts before Solm dispatch. -/
theorem catShortRevert {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeRefinementFor config contract
      σ σ₀ g A I := by
  exact (catX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (catDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem catNoDispatch {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 16 → (catSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeRefinementFor config contract
      σ σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (catX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (catDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (catX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (catDispatch_none_short hshort)

theorem catNoSelectorMatches {I : ExecutionEnv}
    (hbite : ¬ selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩)
    (hbox : ¬ selIs I ⟨#[0x75, 0x42, 0x15, 0xa1]⟩)
    (hcage : ¬ selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hclaw : ¬ selIs I ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩)
    (hdeny : ¬ selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩)
    (hfileAddress : ¬ selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hfileIlkFlip : ¬ selIs I ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩)
    (hfileIlkUint : ¬ selIs I ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩)
    (hfileUint : ¬ selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩)
    (hilks : ¬ selIs I ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩)
    (hlitter : ¬ selIs I ⟨#[0xa4, 0xfe, 0x8c, 0xaf]⟩)
    (hlive : ¬ selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩)
    (hrely : ¬ selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩)
    (hvat : ¬ selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩)
    (hvow : ¬ selIs I ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩)
    (hwards : ¬ selIs I ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩) :
    ∀ i, i < 16 → (catSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [catSelBytes, selIs] using hbite
  · simpa [catSelBytes, selIs] using hbox
  · simpa [catSelBytes, selIs] using hcage
  · simpa [catSelBytes, selIs] using hclaw
  · simpa [catSelBytes, selIs] using hdeny
  · simpa [catSelBytes, selIs] using hfileAddress
  · simpa [catSelBytes, selIs] using hfileIlkFlip
  · simpa [catSelBytes, selIs] using hfileIlkUint
  · simpa [catSelBytes, selIs] using hfileUint
  · simpa [catSelBytes, selIs] using hilks
  · simpa [catSelBytes, selIs] using hlitter
  · simpa [catSelBytes, selIs] using hlive
  · simpa [catSelBytes, selIs] using hrely
  · simpa [catSelBytes, selIs] using hvat
  · simpa [catSelBytes, selIs] using hvow
  · simpa [catSelBytes, selIs] using hwards

theorem catCorrect :
    runtimeRefinement config catBytecode contract := by
  refine runtimeRefinement.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbite : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩
    · exact catBiteBody hcode hsize hwv hbite
    · by_cases hbox : selIs I ⟨#[0x75, 0x42, 0x15, 0xa1]⟩
      · exact catBoxBody hcode hsize hwv hbox
      · by_cases hcage : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩
        · exact catCageBody hcode hsize hwv hcage
        · by_cases hclaw : selIs I ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩
          · exact catClawBody hcode hsize hwv hclaw
          · by_cases hdeny : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩
            · exact catDenyBody hcode hsize hwv hdeny
            · by_cases hfileAddress : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩
              · exact catFileAddressBody hcode hsize hwv hfileAddress
              · by_cases hfileIlkFlip : selIs I ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩
                · exact catFileIlkFlipBody hcode hsize hwv hfileIlkFlip
                · by_cases hfileIlkUint : selIs I ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩
                  · exact catFileIlkUintBody hcode hsize hwv hfileIlkUint
                  · by_cases hfileUint : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩
                    · exact catFileUintBody hcode hsize hwv hfileUint
                    · by_cases hilks : selIs I ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩
                      · exact catIlksBody hcode hsize hwv hilks
                      · by_cases hlitter : selIs I ⟨#[0xa4, 0xfe, 0x8c, 0xaf]⟩
                        · exact catLitterBody hcode hsize hwv hlitter
                        · by_cases hlive : selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩
                          · exact catLiveBody hcode hsize hwv hlive
                          · by_cases hrely : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩
                            · exact catRelyBody hcode hsize hwv hrely
                            · by_cases hvat : selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩
                              · exact catVatBody hcode hsize hwv hvat
                              · by_cases hvow : selIs I ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩
                                · exact catVowBody hcode hsize hwv hvow
                                · by_cases hwards : selIs I ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩
                                  · exact catWardsBody hcode hsize hwv hwards
                                  · exact catNoDispatch hcode hsize hwv
                                      (catNoSelectorMatches hbite hbox hcage hclaw hdeny
                                        hfileAddress hfileIlkFlip hfileIlkUint hfileUint hilks
                                        hlitter hlive hrely hvat hvow hwards)
  · exact catNonPayable hcode hwv

theorem catContractCorrect :
    contractRefinement config catCreationBytecode contract :=
  contractRefinement.of_constant catConstructorCorrect catCorrect

end Benchmarks.Dss.Cat
