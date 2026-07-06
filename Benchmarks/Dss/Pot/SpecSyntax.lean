import Benchmarks.Dss.Pot.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Pot spec through the Solm notation frontend

This file exposes a notation-side presentation for representative parts of the Pot scaffold covered
by the current Solm frontend, and checks by `rfl` that they are definitionally equal to the AST spec
in `Benchmarks.Dss.Pot.Spec`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Pot.Syntax

def storageDeclsSyntax : List StorageDecl :=
  sState% {
    (address => uint256) wards
    (address => uint256) pie
  } ++
  [ { name := "Pie", ty := uint256St },
    { name := "dsr", ty := uint256St },
    { name := "chi", ty := uint256St },
    { name := "vat", ty := addrSt },
    { name := "vow", ty := addrSt },
    { name := "rho", ty := uint256St },
    { name := "live", ty := uint256St } ]

def relyTransitionSyntax : TransitionDecl :=
  { name := "rely"
    params := [{ name := "guy", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      @wards[guy] := 1
    } }

def denyTransitionSyntax : TransitionDecl :=
  { name := "deny"
    params := [{ name := "guy", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      @wards[guy] := 0
    } }

def dsrTransitionSyntax : TransitionDecl :=
  { name := "dsr"
    params := []
    returnType := [uint256]
    body := sBlock% {
      require msg.value == 0
      return @dsr
    } }

def vowTransitionSyntax : TransitionDecl :=
  { name := "vow"
    params := []
    returnType := [addr]
    body := sBlock% {
      require msg.value == 0
      return @vow
    } }

def transitionsSyntax : List TransitionDecl :=
  [ PieTransition,
    cageTransition,
    chiTransition,
    denyTransitionSyntax,
    dripTransition,
    dsrTransitionSyntax,
    exitTransition,
    fileDsrTransition,
    fileVowTransition,
    joinTransition,
    liveTransition,
    pieTransition,
    relyTransitionSyntax,
    rhoTransition,
    vatTransition,
    vowTransitionSyntax,
    wardsTransition ]

def contractSyntax : ContractDecl :=
  { name := "Pot"
    storage := storageDeclsSyntax
    ctor := constructorDecl
    functions := functions
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.Dss.Pot.storageDecls := by
  rfl

theorem relyTransitionSyntax_eq : relyTransitionSyntax = Benchmarks.Dss.Pot.relyTransition := by
  rfl

theorem denyTransitionSyntax_eq : denyTransitionSyntax = Benchmarks.Dss.Pot.denyTransition := by
  rfl

theorem dsrTransitionSyntax_eq : dsrTransitionSyntax = Benchmarks.Dss.Pot.dsrTransition := by
  rfl

theorem vowTransitionSyntax_eq : vowTransitionSyntax = Benchmarks.Dss.Pot.vowTransition := by
  rfl

theorem transitionsSyntax_eq : transitionsSyntax = Benchmarks.Dss.Pot.transitions := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Pot.contract := by
  rfl

end Benchmarks.Dss.Pot.Syntax
