import Benchmarks.Dss.Vow.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Vow spec through the Solm notation frontend

This file exposes a notation-side presentation for representative parts of the Vow scaffold covered
by the current Solm frontend, and checks by `rfl` that they are definitionally equal to the AST spec
in `Benchmarks.Dss.Vow.Spec`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Vow.Syntax

def storageDeclsSyntax : List StorageDecl :=
  sState% {
    (address => uint256) wards
  } ++
  [ { name := "vat", ty := addrSt },
    { name := "flapper", ty := addrSt },
    { name := "flopper", ty := addrSt },
    { name := "sin", ty := .mapping (.int uint256Int) uint256St },
    { name := "Sin", ty := uint256St },
    { name := "Ash", ty := uint256St },
    { name := "wait", ty := uint256St },
    { name := "dump", ty := uint256St },
    { name := "sump", ty := uint256St },
    { name := "bump", ty := uint256St },
    { name := "hump", ty := uint256St },
    { name := "live", ty := uint256St } ]

def denyTransitionSyntax : TransitionDecl :=
  { name := "deny"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      @wards[usr] := 0
    } }

def vatTransitionSyntax : TransitionDecl :=
  { name := "vat"
    params := []
    returnType := [addr]
    body := sBlock% {
      require msg.value == 0
      return @vat
    } }

def waitTransitionSyntax : TransitionDecl :=
  { name := "wait"
    params := []
    returnType := [uint256]
    body := sBlock% {
      require msg.value == 0
      return @wait
    } }

def liveTransitionSyntax : TransitionDecl :=
  { name := "live"
    params := []
    returnType := [uint256]
    body := sBlock% {
      require msg.value == 0
      return @live
    } }

def transitionsSyntax : List TransitionDecl :=
  [ AshTransition,
    SinTransition,
    bumpTransition,
    cageTransition,
    denyTransitionSyntax,
    dumpTransition,
    fessTransition,
    fileUintTransition,
    fileAddressTransition,
    flapTransition,
    flapperTransition,
    flogTransition,
    flopTransition,
    flopperTransition,
    healTransition,
    humpTransition,
    kissTransition,
    liveTransitionSyntax,
    relyTransition,
    sinTransition,
    sumpTransition,
    vatTransitionSyntax,
    waitTransitionSyntax,
    wardsTransition ]

def contractSyntax : ContractDecl :=
  { name := "Vow"
    storage := storageDeclsSyntax
    ctor := constructorDecl
    functions := functions
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.Dss.Vow.storageDecls := by
  rfl

theorem denyTransitionSyntax_eq : denyTransitionSyntax = Benchmarks.Dss.Vow.denyTransition := by
  rfl

theorem vatTransitionSyntax_eq : vatTransitionSyntax = Benchmarks.Dss.Vow.vatTransition := by
  rfl

theorem waitTransitionSyntax_eq : waitTransitionSyntax = Benchmarks.Dss.Vow.waitTransition := by
  rfl

theorem liveTransitionSyntax_eq : liveTransitionSyntax = Benchmarks.Dss.Vow.liveTransition := by
  rfl

theorem transitionsSyntax_eq : transitionsSyntax = Benchmarks.Dss.Vow.transitions := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Vow.contract := by
  rfl

end Benchmarks.Dss.Vow.Syntax
