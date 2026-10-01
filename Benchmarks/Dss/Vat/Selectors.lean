import Benchmarks.Dss.Vat.Common

/-!
# MakerDAO/Sky DSS Vat selector proofs

The selector theorems connect Solm signatures to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Vat

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem LineSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr LineTransition))).extract 0 4 =
      vatSelBytes 0 := by decide +kernel

theorem cageSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      vatSelBytes 1 := by decide +kernel

theorem canSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr canTransition))).extract 0 4 =
      vatSelBytes 2 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, canTransition, addr]; decide +kernel

theorem daiSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr daiTransition))).extract 0 4 =
      vatSelBytes 3 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, daiTransition, addr]; decide +kernel

theorem debtSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr debtTransition))).extract 0 4 =
      vatSelBytes 4 := by decide +kernel

theorem denySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      vatSelBytes 5 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, denyTransition, addr]; decide +kernel

theorem fileIlkSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileIlkTransition))).extract 0 4 =
      vatSelBytes 6 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileIlkTransition, bytes32, uint256]; decide +kernel

theorem fileLineSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fileLineTransition))).extract 0 4 =
      vatSelBytes 7 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fileLineTransition, bytes32, uint256]; decide +kernel

theorem fluxSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr fluxTransition))).extract 0 4 =
      vatSelBytes 8 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, fluxTransition, bytes32, addr, uint256]; decide +kernel

theorem foldSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr foldTransition))).extract 0 4 =
      vatSelBytes 9 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, foldTransition, bytes32, addr, int256]; decide +kernel

theorem forkSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr forkTransition))).extract 0 4 =
      vatSelBytes 10 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, forkTransition, bytes32, addr, int256]; decide +kernel

theorem frobSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr frobTransition))).extract 0 4 =
      vatSelBytes 11 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, frobTransition, bytes32, addr, int256]; decide +kernel

theorem gemSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr gemTransition))).extract 0 4 =
      vatSelBytes 12 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, gemTransition, bytes32, addr]; decide +kernel

theorem grabSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr grabTransition))).extract 0 4 =
      vatSelBytes 13 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, grabTransition, bytes32, addr, int256]; decide +kernel

theorem healSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr healTransition))).extract 0 4 =
      vatSelBytes 14 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, healTransition, uint256]; decide +kernel

theorem hopeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr hopeTransition))).extract 0 4 =
      vatSelBytes 15 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, hopeTransition, addr]; decide +kernel

theorem ilksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      vatSelBytes 16 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ilksTransition, bytes32]; decide +kernel

theorem initSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr initTransition))).extract 0 4 =
      vatSelBytes 17 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, initTransition, bytes32]; decide +kernel

theorem liveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      vatSelBytes 18 := by decide +kernel

theorem moveSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr moveTransition))).extract 0 4 =
      vatSelBytes 19 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, moveTransition, addr, uint256]; decide +kernel

theorem nopeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr nopeTransition))).extract 0 4 =
      vatSelBytes 20 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, nopeTransition, addr]; decide +kernel

theorem relySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      vatSelBytes 21 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, relyTransition, addr]; decide +kernel

theorem sinSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr sinTransition))).extract 0 4 =
      vatSelBytes 22 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, sinTransition, addr]; decide +kernel

theorem slipSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr slipTransition))).extract 0 4 =
      vatSelBytes 23 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, slipTransition, bytes32, addr, int256]; decide +kernel

theorem suckSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr suckTransition))).extract 0 4 =
      vatSelBytes 24 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, suckTransition, addr, uint256]; decide +kernel

theorem urnsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr urnsTransition))).extract 0 4 =
      vatSelBytes 25 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, urnsTransition, bytes32, addr]; decide +kernel

theorem viceSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr viceTransition))).extract 0 4 =
      vatSelBytes 26 := by decide +kernel

theorem wardsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      vatSelBytes 27 := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, wardsTransition, addr]; decide +kernel

end Benchmarks.Dss.Vat
