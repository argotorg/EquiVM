import Benchmarks.Dss.Jug.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Jug spec through the Solm notation frontend

This file exposes a notation-side presentation for representative parts of the Jug scaffold covered
by the current Solm frontend, and checks by `rfl` that they are definitionally equal to the AST spec
in `Benchmarks.Dss.Jug.Spec`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Jug.Syntax

def storageDeclsSyntax : List StorageDecl :=
  sState% {
    (address => uint256) wards
  } ++
  [ { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "vat", ty := addrSt },
    { name := "vow", ty := addrSt },
    { name := "base", ty := uint256St } ]

def relyTransitionSyntax : TransitionDecl :=
  { name := "rely"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      @wards[usr] := 1
    } }

def denyTransitionSyntax : TransitionDecl :=
  { name := "deny"
    params := [{ name := "usr", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      @wards[usr] := 0
    } }

def baseTransitionSyntax : TransitionDecl :=
  { name := "base"
    params := []
    returnType := [uint256]
    body := sBlock% {
      require msg.value == 0
      return @base
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
  [ baseTransitionSyntax,
    denyTransitionSyntax,
    dripTransition,
    fileBaseTransition,
    fileDutyTransition,
    fileVowTransition,
    ilksTransition,
    initTransition,
    relyTransitionSyntax,
    vatTransition,
    vowTransitionSyntax,
    wardsTransition ]

def contractSyntax : ContractDecl :=
  { name := "Jug"
    storage := storageDeclsSyntax
    ctor := constructorDecl
    structs := structs
    functions := functions
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.Dss.Jug.storageDecls := by
  rfl

theorem relyTransitionSyntax_eq : relyTransitionSyntax = Benchmarks.Dss.Jug.relyTransition := by
  rfl

theorem denyTransitionSyntax_eq : denyTransitionSyntax = Benchmarks.Dss.Jug.denyTransition := by
  rfl

theorem baseTransitionSyntax_eq : baseTransitionSyntax = Benchmarks.Dss.Jug.baseTransition := by
  rfl

theorem vowTransitionSyntax_eq : vowTransitionSyntax = Benchmarks.Dss.Jug.vowTransition := by
  rfl

theorem transitionsSyntax_eq : transitionsSyntax = Benchmarks.Dss.Jug.transitions := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Jug.contract := by
  rfl

end Benchmarks.Dss.Jug.Syntax
