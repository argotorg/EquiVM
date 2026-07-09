import Benchmarks.Dss.Vat.Common

/-!
# MakerDAO/Sky DSS Vat trusted selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Vat

axiom LineSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr LineTransition))).extract 0 4 =
      vatSelBytes 0

axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      vatSelBytes 1

axiom canSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr canTransition))).extract 0 4 =
      vatSelBytes 2

axiom daiSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr daiTransition))).extract 0 4 =
      vatSelBytes 3

axiom debtSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr debtTransition))).extract 0 4 =
      vatSelBytes 4

axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      vatSelBytes 5

axiom fileIlkSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileIlkTransition))).extract 0 4 =
      vatSelBytes 6

axiom fileLineSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fileLineTransition))).extract 0 4 =
      vatSelBytes 7

axiom fluxSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr fluxTransition))).extract 0 4 =
      vatSelBytes 8

axiom foldSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr foldTransition))).extract 0 4 =
      vatSelBytes 9

axiom forkSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr forkTransition))).extract 0 4 =
      vatSelBytes 10

axiom frobSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr frobTransition))).extract 0 4 =
      vatSelBytes 11

axiom gemSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr gemTransition))).extract 0 4 =
      vatSelBytes 12

axiom grabSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr grabTransition))).extract 0 4 =
      vatSelBytes 13

axiom healSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr healTransition))).extract 0 4 =
      vatSelBytes 14

axiom hopeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr hopeTransition))).extract 0 4 =
      vatSelBytes 15

axiom ilksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ilksTransition))).extract 0 4 =
      vatSelBytes 16

axiom initSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr initTransition))).extract 0 4 =
      vatSelBytes 17

axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      vatSelBytes 18

axiom moveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr moveTransition))).extract 0 4 =
      vatSelBytes 19

axiom nopeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr nopeTransition))).extract 0 4 =
      vatSelBytes 20

axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      vatSelBytes 21

axiom sinSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr sinTransition))).extract 0 4 =
      vatSelBytes 22

axiom slipSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr slipTransition))).extract 0 4 =
      vatSelBytes 23

axiom suckSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr suckTransition))).extract 0 4 =
      vatSelBytes 24

axiom urnsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr urnsTransition))).extract 0 4 =
      vatSelBytes 25

axiom viceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr viceTransition))).extract 0 4 =
      vatSelBytes 26

axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      vatSelBytes 27

end Benchmarks.Dss.Vat
