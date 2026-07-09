import Benchmarks.Dss.Clipper.Active
import Benchmarks.Dss.Clipper.Buf
import Benchmarks.Dss.Clipper.Calc
import Benchmarks.Dss.Clipper.Chip
import Benchmarks.Dss.Clipper.Chost
import Benchmarks.Dss.Clipper.Constructor
import Benchmarks.Dss.Clipper.Count
import Benchmarks.Dss.Clipper.Cusp
import Benchmarks.Dss.Clipper.Deny
import Benchmarks.Dss.Clipper.Dog
import Benchmarks.Dss.Clipper.Fallback
import Benchmarks.Dss.Clipper.FileAddress
import Benchmarks.Dss.Clipper.FileUint
import Benchmarks.Dss.Clipper.GetStatus
import Benchmarks.Dss.Clipper.Ilk
import Benchmarks.Dss.Clipper.Kick
import Benchmarks.Dss.Clipper.Kicks
import Benchmarks.Dss.Clipper.List
import Benchmarks.Dss.Clipper.Redo
import Benchmarks.Dss.Clipper.Rely
import Benchmarks.Dss.Clipper.Sales
import Benchmarks.Dss.Clipper.Spotter
import Benchmarks.Dss.Clipper.Stopped
import Benchmarks.Dss.Clipper.Tail
import Benchmarks.Dss.Clipper.Take
import Benchmarks.Dss.Clipper.Tip
import Benchmarks.Dss.Clipper.Upchost
import Benchmarks.Dss.Clipper.Vat
import Benchmarks.Dss.Clipper.Vow
import Benchmarks.Dss.Clipper.Wards
import Benchmarks.Dss.Clipper.Yank
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Clipper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Clipper

theorem clipperCorrect (v : ClipperImmutables) {code : ByteArray}
    (hcode : patchRuntime clipperBytecode (patches v) = some code) :
    runtimeEquivalenceWithWF clipperStorageWF (config v) code (contract v) := by
  refine runtimeEquivalenceWithWF.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hIcode hsize hperm hAccounts hStorageWF
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hactive : selIs I (clipperSelBytes 0)
    · exact clipperActiveBody v hcode hIcode hsize hperm hwv hactive hAccounts
    · by_cases hbuf : selIs I (clipperSelBytes 1)
      · exact clipperBufBody v hcode hIcode hsize hperm hwv hbuf hAccounts
      · by_cases hcalc : selIs I (clipperSelBytes 2)
        · exact clipperCalcBody v hcode hIcode hsize hperm hwv hcalc hAccounts
        · by_cases hchip : selIs I (clipperSelBytes 3)
          · exact clipperChipBody v hcode hIcode hsize hperm hwv hchip hAccounts
          · by_cases hchost : selIs I (clipperSelBytes 4)
            · exact clipperChostBody v hcode hIcode hsize hperm hwv hchost hAccounts
            · by_cases hcount : selIs I (clipperSelBytes 5)
              · exact clipperCountBody v hcode hIcode hsize hperm hwv hcount hAccounts
              · by_cases hcusp : selIs I (clipperSelBytes 6)
                · exact clipperCuspBody v hcode hIcode hsize hperm hwv hcusp hAccounts
                · by_cases hdeny : selIs I (clipperSelBytes 7)
                  · exact clipperDenyBody v hcode hIcode hsize hperm hwv hdeny hAccounts
                  · by_cases hdog : selIs I (clipperSelBytes 8)
                    · exact clipperDogBody v hcode hIcode hsize hperm hwv hdog hAccounts
                    · by_cases hfileUint : selIs I (clipperSelBytes 9)
                      · exact clipperFileUintBody v hcode hIcode hsize hperm hwv hfileUint
                          hAccounts
                      · by_cases hfileAddress : selIs I (clipperSelBytes 10)
                        · exact clipperFileAddressBody v hcode hIcode hsize hperm hwv
                            hfileAddress hAccounts
                        · by_cases hgetStatus : selIs I (clipperSelBytes 11)
                          · exact clipperGetStatusBody v hcode hIcode hsize hperm hwv
                              hgetStatus hAccounts
                          · by_cases hilk : selIs I (clipperSelBytes 12)
                            · exact clipperIlkBody v hcode hIcode hsize hperm hwv hilk
                                hAccounts
                            · by_cases hkick : selIs I (clipperSelBytes 13)
                              · exact clipperKickBody v hcode hIcode hsize hperm hwv hkick
                                  hAccounts
                              · by_cases hkicks : selIs I (clipperSelBytes 14)
                                · exact clipperKicksBody v hcode hIcode hsize hperm hwv
                                    hkicks hAccounts
                                · by_cases hlist : selIs I (clipperSelBytes 15)
                                  · exact clipperListBody v hcode hIcode hsize hperm hwv
                                      hlist hAccounts hStorageWF
                                  · by_cases hredo : selIs I (clipperSelBytes 16)
                                    · exact clipperRedoBody v hcode hIcode hsize hperm hwv
                                        hredo hAccounts
                                    · by_cases hrely : selIs I (clipperSelBytes 17)
                                      · exact clipperRelyBody v hcode hIcode hsize hperm
                                          hwv hrely hAccounts
                                      · by_cases hsales : selIs I (clipperSelBytes 18)
                                        · exact clipperSalesBody v hcode hIcode hsize hperm
                                            hwv hsales hAccounts
                                        · by_cases hspotter : selIs I (clipperSelBytes 19)
                                          · exact clipperSpotterBody v hcode hIcode hsize
                                              hperm hwv hspotter hAccounts
                                          · by_cases hstopped : selIs I (clipperSelBytes 20)
                                            · exact clipperStoppedBody v hcode hIcode hsize
                                                hperm hwv hstopped hAccounts
                                            · by_cases htail : selIs I (clipperSelBytes 21)
                                              · exact clipperTailBody v hcode hIcode hsize
                                                  hperm hwv htail hAccounts
                                              · by_cases htake : selIs I (clipperSelBytes 22)
                                                · exact clipperTakeBody v hcode hIcode hsize
                                                    hperm hwv htake hAccounts
                                                · by_cases htip : selIs I (clipperSelBytes 23)
                                                  · exact clipperTipBody v hcode hIcode hsize
                                                      hperm hwv htip hAccounts
                                                  · by_cases hupchost :
                                                        selIs I (clipperSelBytes 24)
                                                    · exact clipperUpchostBody v hcode hIcode
                                                        hsize hperm hwv hupchost hAccounts
                                                    · by_cases hvat :
                                                          selIs I (clipperSelBytes 25)
                                                      · exact clipperVatBody v hcode hIcode
                                                          hsize hperm hwv hvat hAccounts
                                                      · by_cases hvow :
                                                            selIs I (clipperSelBytes 26)
                                                        · exact clipperVowBody v hcode hIcode
                                                            hsize hperm hwv hvow hAccounts
                                                        · by_cases hwards :
                                                              selIs I (clipperSelBytes 27)
                                                          · exact clipperWardsBody v hcode
                                                              hIcode hsize hperm hwv hwards
                                                              hAccounts
                                                          · by_cases hyank :
                                                                selIs I (clipperSelBytes 28)
                                                            · exact clipperYankBody v hcode
                                                                hIcode hsize hperm hwv hyank
                                                                hAccounts
                                                            · exact clipperNoDispatch v hcode
                                                                hIcode hsize hperm hwv
                                                                (clipperNoSelectorMatches
                                                                  hactive hbuf hcalc hchip
                                                                  hchost hcount hcusp hdeny
                                                                  hdog hfileUint hfileAddress
                                                                  hgetStatus hilk hkick hkicks
                                                                  hlist hredo hrely hsales
                                                                  hspotter hstopped htail htake
                                                                  htip hupchost hvat hvow hwards
                                                                  hyank)
                                                                hAccounts
  · exact clipperNonPayable v hcode hIcode hwv

theorem clipperContractCorrect (v : ClipperImmutables) {code : ByteArray}
    (hcode : patchRuntime clipperBytecode (patches v) = some code) :
    contractEquivalenceWithWF clipperStorageWF (config v) clipperCreationBytecode code (contract v)
      (runtimeCodeOf clipperBytecode) :=
  contractEquivalenceWithWF.intro
    (clipperConstructorCorrect v)
    (clipperCorrect v hcode)

end Benchmarks.Dss.Clipper
