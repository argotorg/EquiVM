import Benchmarks.Dss.Vat.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Vat spec through the Solm notation frontend

This file exposes a notation-side presentation for representative parts of the Vat scaffold covered
by the current Solm frontend, and checks by `rfl` that they are definitionally equal to the AST spec
in `Benchmarks.Dss.Vat.Spec`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Vat.Syntax

def storageDeclsSyntax : List StorageDecl :=
  sState% {
    (address => uint256)                 wards
    (address => (address => uint256))    can
  } ++
  [ { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "urns", ty := .mapping (.bytes bytes32Width) (.mapping .address UrnStructTy) },
    { name := "gem", ty := .mapping (.bytes bytes32Width) (.mapping .address uint256St) },
    { name := "dai", ty := .mapping .address uint256St },
    { name := "sin", ty := .mapping .address uint256St },
    { name := "debt", ty := uint256St },
    { name := "vice", ty := uint256St },
    { name := "Line", ty := uint256St },
    { name := "live", ty := uint256St } ]

def hopeTransitionSyntax : TransitionDecl :=
  { name := "hope"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      @can[msg.sender][usr] := 1
    } }

def nopeTransitionSyntax : TransitionDecl :=
  { name := "nope"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      @can[msg.sender][usr] := 0
    } }

def relyTransitionSyntax : TransitionDecl :=
  { name := "rely"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      require @live == 1
      @wards[usr] := 1
    } }

def denyTransitionSyntax : TransitionDecl :=
  { name := "deny"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      require @live == 1
      @wards[usr] := 0
    } }

def cageTransitionSyntax : TransitionDecl :=
  { name := "cage"
    params := []
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      @live := 0
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
  [ LineTransition,
    cageTransitionSyntax,
    canTransition,
    daiTransition,
    debtTransition,
    denyTransitionSyntax,
    fileIlkTransition,
    fileLineTransition,
    fluxTransition,
    foldTransition,
    forkTransition,
    frobTransition,
    gemTransition,
    grabTransition,
    healTransition,
    hopeTransitionSyntax,
    ilksTransition,
    initTransition,
    liveTransitionSyntax,
    moveTransition,
    nopeTransitionSyntax,
    relyTransitionSyntax,
    sinTransition,
    slipTransition,
    suckTransition,
    urnsTransition,
    viceTransition,
    wardsTransition ]

def contractSyntax : ContractDecl :=
  { name := "Vat"
    storage := storageDeclsSyntax
    ctor := constructorDecl
    structs := structs
    functions := []
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.Dss.Vat.storageDecls := by
  rfl

theorem hopeTransitionSyntax_eq : hopeTransitionSyntax = Benchmarks.Dss.Vat.hopeTransition := by
  rfl

theorem nopeTransitionSyntax_eq : nopeTransitionSyntax = Benchmarks.Dss.Vat.nopeTransition := by
  rfl

theorem relyTransitionSyntax_eq : relyTransitionSyntax = Benchmarks.Dss.Vat.relyTransition := by
  rfl

theorem denyTransitionSyntax_eq : denyTransitionSyntax = Benchmarks.Dss.Vat.denyTransition := by
  rfl

theorem cageTransitionSyntax_eq : cageTransitionSyntax = Benchmarks.Dss.Vat.cageTransition := by
  rfl

theorem liveTransitionSyntax_eq : liveTransitionSyntax = Benchmarks.Dss.Vat.liveTransition := by
  rfl

theorem transitionsSyntax_eq : transitionsSyntax = Benchmarks.Dss.Vat.transitions := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Vat.contract := by
  rfl

end Benchmarks.Dss.Vat.Syntax
