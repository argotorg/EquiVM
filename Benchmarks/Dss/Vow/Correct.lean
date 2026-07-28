import Benchmarks.Dss.Vow.Ash
import Benchmarks.Dss.Vow.Bump
import Benchmarks.Dss.Vow.Cage
import Benchmarks.Dss.Vow.CageBodyRuntime
import Benchmarks.Dss.Vow.CageBodyRuntimeTail
import Benchmarks.Dss.Vow.Common
import Benchmarks.Dss.Vow.ConstructorTail
import Benchmarks.Dss.Vow.Deny
import Benchmarks.Dss.Vow.Dump
import Benchmarks.Dss.Vow.Fess
import Benchmarks.Dss.Vow.FileAddressFlapperBody
import Benchmarks.Dss.Vow.FileUint
import Benchmarks.Dss.Vow.FlapRuntime
import Benchmarks.Dss.Vow.Flapper
import Benchmarks.Dss.Vow.Flog
import Benchmarks.Dss.Vow.Flop
import Benchmarks.Dss.Vow.FlopDai
import Benchmarks.Dss.Vow.FlopAsh
import Benchmarks.Dss.Vow.FlopKick
import Benchmarks.Dss.Vow.FlopBody
import Benchmarks.Dss.Vow.Flopper
import Benchmarks.Dss.Vow.HealBody
import Benchmarks.Dss.Vow.Hump
import Benchmarks.Dss.Vow.KissSuccess
import Benchmarks.Dss.Vow.Live
import Benchmarks.Dss.Vow.Rely
import Benchmarks.Dss.Vow.Sin
import Benchmarks.Dss.Vow.SinMapping
import Benchmarks.Dss.Vow.Sump
import Benchmarks.Dss.Vow.Vat
import Benchmarks.Dss.Vow.Wait
import Benchmarks.Dss.Vow.Wards
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vow benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem vowNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (vowX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (vowBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector (`size < 4`) reverts before Solm dispatch. -/
theorem vowShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (vowX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (vowDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem vowNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 24 → (vowSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (vowX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (vowDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (vowX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (vowDispatch_none_short hshort)

theorem vowNoSelectorMatches {I : ExecutionEnv}
    (hAsh : ¬ selIs I ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩)
    (hSinCap : ¬ selIs I ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩)
    (hbump : ¬ selIs I ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩)
    (hcage : ¬ selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩)
    (hdeny : ¬ selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩)
    (hdump : ¬ selIs I ⟨#[0xe4, 0x33, 0x05, 0x45]⟩)
    (hfess : ¬ selIs I ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩)
    (hfileUint : ¬ selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩)
    (hfileAddress : ¬ selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hflap : ¬ selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩)
    (hflapper : ¬ selIs I ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩)
    (hflog : ¬ selIs I ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩)
    (hflop : ¬ selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩)
    (hflopper : ¬ selIs I ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩)
    (hheal : ¬ selIs I ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩)
    (hhump : ¬ selIs I ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩)
    (hkiss : ¬ selIs I ⟨#[0x25, 0x06, 0x85, 0x5a]⟩)
    (hlive : ¬ selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩)
    (hrely : ¬ selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩)
    (hsin : ¬ selIs I ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩)
    (hsump : ¬ selIs I ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩)
    (hvat : ¬ selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩)
    (hwait : ¬ selIs I ⟨#[0x64, 0xbd, 0x70, 0x13]⟩)
    (hwards : ¬ selIs I ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩) :
    ∀ i, i < 24 → (vowSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [vowSelBytes, selIs] using hAsh
  · simpa [vowSelBytes, selIs] using hSinCap
  · simpa [vowSelBytes, selIs] using hbump
  · simpa [vowSelBytes, selIs] using hcage
  · simpa [vowSelBytes, selIs] using hdeny
  · simpa [vowSelBytes, selIs] using hdump
  · simpa [vowSelBytes, selIs] using hfess
  · simpa [vowSelBytes, selIs] using hfileUint
  · simpa [vowSelBytes, selIs] using hfileAddress
  · simpa [vowSelBytes, selIs] using hflap
  · simpa [vowSelBytes, selIs] using hflapper
  · simpa [vowSelBytes, selIs] using hflog
  · simpa [vowSelBytes, selIs] using hflop
  · simpa [vowSelBytes, selIs] using hflopper
  · simpa [vowSelBytes, selIs] using hheal
  · simpa [vowSelBytes, selIs] using hhump
  · simpa [vowSelBytes, selIs] using hkiss
  · simpa [vowSelBytes, selIs] using hlive
  · simpa [vowSelBytes, selIs] using hrely
  · simpa [vowSelBytes, selIs] using hsin
  · simpa [vowSelBytes, selIs] using hsump
  · simpa [vowSelBytes, selIs] using hvat
  · simpa [vowSelBytes, selIs] using hwait
  · simpa [vowSelBytes, selIs] using hwards

theorem vowCorrectWith
    (cageBody :
      ∀ {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256},
        I.code = vowBytecode →
        I.calldata.size < UInt256.size →
        I.perm = true →
        I.weiValue = ⟨0⟩ →
        selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩ →
        accountMapEquiv σ_evm σ_solm →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (flapBody :
      ∀ {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256},
        I.code = vowBytecode →
        I.calldata.size < UInt256.size →
        I.perm = true →
        I.weiValue = ⟨0⟩ →
        selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ →
        accountMapEquiv σ_evm σ_solm →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (flopBody :
      ∀ {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256},
        I.code = vowBytecode →
        I.calldata.size < UInt256.size →
        I.perm = true →
        I.weiValue = ⟨0⟩ →
        selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ →
        accountMapEquiv σ_evm σ_solm →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I) :
    runtimeEquivalence config vowBytecode contract := by
  refine runtimeEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hAsh : selIs I ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩
    · exact vowAshBody hcode hsize hperm hwv hAsh hAccounts
    · by_cases hSinCap : selIs I ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩
      · exact vowSinBody hcode hsize hperm hwv hSinCap hAccounts
      · by_cases hbump : selIs I ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩
        · exact vowBumpBody hcode hsize hperm hwv hbump hAccounts
        · by_cases hcage : selIs I ⟨#[0x69, 0x24, 0x50, 0x09]⟩
          · exact cageBody hcode hsize hperm hwv hcage hAccounts
          · by_cases hdeny : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩
            · have hsz4 : 4 ≤ I.calldata.size :=
                calldata_size_ge_of_selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ rfl hdeny
              by_cases hshort : I.calldata.size < 36
              · exact vowDenyShort hcode hsize hperm hwv hsz4 hshort hdeny hAccounts
              · exact vowDenyBody hcode hsize hperm hwv (by omega) hdeny hAccounts
            · by_cases hdump : selIs I ⟨#[0xe4, 0x33, 0x05, 0x45]⟩
              · exact vowDumpBody hcode hsize hperm hwv hdump hAccounts
              · by_cases hfess : selIs I ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩
                · have hsz4 : 4 ≤ I.calldata.size :=
                    calldata_size_ge_of_selIs I ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩ rfl hfess
                  by_cases hshort : I.calldata.size < 36
                  · exact vowFessShort hcode hsize hperm hwv hsz4 hshort hfess hAccounts
                  · exact vowFessBody hcode hsize hperm hwv (by omega) hfess hAccounts
                · by_cases hfileUint : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩
                  · have hsz4 : 4 ≤ I.calldata.size :=
                      calldata_size_ge_of_selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩ rfl
                        hfileUint
                    by_cases hshort : I.calldata.size < 68
                    · exact vowFileUintShort hcode hsize hperm hwv hsz4 hshort hfileUint
                        hAccounts
                    · exact vowFileUintBody hcode hsize hperm hwv (by omega) hfileUint
                        hAccounts
                  · by_cases hfileAddress : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩
                    · exact vowFileAddressBody hcode hsize hperm hwv hfileAddress hAccounts
                    · by_cases hflap : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩
                      · exact flapBody hcode hsize hperm hwv hflap hAccounts
                      · by_cases hflapper : selIs I ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩
                        · exact vowFlapperBody hcode hsize hperm hwv hflapper hAccounts
                        · by_cases hflog : selIs I ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩
                          · have hsz4 : 4 ≤ I.calldata.size :=
                              calldata_size_ge_of_selIs I ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩
                                rfl hflog
                            by_cases hshort : I.calldata.size < 36
                            · exact vowFlogShort hcode hsize hperm hwv hsz4 hshort hflog
                                hAccounts
                            · exact vowFlogBody hcode hsize hperm hwv (by omega) hflog hAccounts
                          · by_cases hflop : selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩
                            · exact flopBody hcode hsize hperm hwv hflop hAccounts
                            · by_cases hflopper : selIs I ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩
                              · exact vowFlopperBody hcode hsize hperm hwv hflopper hAccounts
                              · by_cases hheal : selIs I ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩
                                · exact vowHealBody hcode hsize hperm hwv hheal hAccounts
                                · by_cases hhump : selIs I ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩
                                  · exact vowHumpBody hcode hsize hperm hwv hhump hAccounts
                                  · by_cases hkiss : selIs I ⟨#[0x25, 0x06, 0x85, 0x5a]⟩
                                    · exact vowKissBody hcode hsize hperm hwv hkiss hAccounts
                                    · by_cases hlive : selIs I ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩
                                      · exact vowLiveBody hcode hsize hperm hwv hlive hAccounts
                                      · by_cases hrely : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩
                                        · have hsz4 : 4 ≤ I.calldata.size :=
                                            calldata_size_ge_of_selIs I
                                              ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ rfl hrely
                                          by_cases hshort : I.calldata.size < 36
                                          · exact vowRelyShort hcode hsize hperm hwv hsz4
                                              hshort hrely hAccounts
                                          · exact vowRelyBody hcode hsize hperm hwv (by omega)
                                              hrely hAccounts
                                        · by_cases hsin : selIs I ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩
                                          · have hsz4 : 4 ≤ I.calldata.size :=
                                              calldata_size_ge_of_selIs I
                                                ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩ rfl hsin
                                            by_cases hshort : I.calldata.size < 36
                                            · exact vowSinMappingShort hcode hsize hperm hwv
                                                hsz4 hshort hsin hAccounts
                                            · exact vowSinMappingBody hcode hsize hperm hwv
                                                (by omega) hsin hAccounts
                                          · by_cases hsump : selIs I ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩
                                            · exact vowSumpBody hcode hsize hperm hwv hsump hAccounts
                                            · by_cases hvat : selIs I ⟨#[0x36, 0x56, 0x9e, 0x77]⟩
                                              · exact vowVatBody hcode hsize hperm hwv hvat hAccounts
                                              · by_cases hwait : selIs I ⟨#[0x64, 0xbd, 0x70, 0x13]⟩
                                                · exact vowWaitBody hcode hsize hperm hwv hwait hAccounts
                                                · by_cases hwards :
                                                    selIs I ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩
                                                  · have hsz4 : 4 ≤ I.calldata.size :=
                                                      calldata_size_ge_of_selIs I
                                                        ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ rfl
                                                        hwards
                                                    by_cases hshort : I.calldata.size < 36
                                                    · exact vowWardsShort hcode hsize hperm hwv
                                                        hsz4 hshort hwards hAccounts
                                                    · exact vowWardsBody hcode hsize hperm hwv
                                                        (by omega) hwards hAccounts
                                                  · exact vowNoDispatch hcode hsize hperm hwv
                                                      (vowNoSelectorMatches hAsh hSinCap hbump
                                                        hcage hdeny hdump hfess hfileUint
                                                        hfileAddress hflap hflapper hflog hflop
                                                        hflopper hheal hhump hkiss hlive hrely
                                                        hsin hsump hvat hwait hwards)
  · exact vowNonPayable hcode hwv

theorem vowCorrect :
    runtimeEquivalence config vowBytecode contract := by
  exact vowCorrectWith vowCageBody vowFlapBody vowFlopBody

theorem vowContractCorrect :
    contractEquivalence config vowCreationBytecode vowBytecode contract :=
  contractEquivalence.intro vowConstructorCorrect vowCorrect

end Benchmarks.Dss.Vow
