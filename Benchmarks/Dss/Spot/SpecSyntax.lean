import Benchmarks.Dss.Spot.Spec
import Solm.Notation

/-!
# MakerDAO/Sky DSS Spotter spec through the Solm notation frontend

This file exposes a notation-side presentation for representative parts of the Spotter scaffold
covered by the current Solm frontend, and checks by `rfl` that they are definitionally equal to the
AST spec in `Benchmarks.Dss.Spot.Spec`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Spot.Syntax

def storageDeclsSyntax : List StorageDecl :=
  sState% {
    (address => uint256) wards
  } ++
  [ { name := "ilks", ty := .mapping (.bytes bytes32Width) IlkStructTy },
    { name := "vat", ty := addrSt },
    { name := "par", ty := uint256St },
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

def parTransitionSyntax : TransitionDecl :=
  { name := "par"
    params := []
    returnType := [uint256]
    body := sBlock% {
      require msg.value == 0
      return @par
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
  [ cageTransition,
    denyTransitionSyntax,
    fileMatTransition,
    fileParTransition,
    filePipTransition,
    ilksTransition,
    liveTransitionSyntax,
    parTransitionSyntax,
    pokeTransition,
    relyTransitionSyntax,
    vatTransition,
    wardsTransition ]

def contractSyntax : ContractDecl :=
  { name := "Spotter"
    storage := storageDeclsSyntax
    ctor := constructorDecl
    structs := structs
    functions := functions
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.Dss.Spot.storageDecls := by
  rfl

theorem relyTransitionSyntax_eq : relyTransitionSyntax = Benchmarks.Dss.Spot.relyTransition := by
  rfl

theorem denyTransitionSyntax_eq : denyTransitionSyntax = Benchmarks.Dss.Spot.denyTransition := by
  rfl

theorem parTransitionSyntax_eq : parTransitionSyntax = Benchmarks.Dss.Spot.parTransition := by
  rfl

theorem liveTransitionSyntax_eq : liveTransitionSyntax = Benchmarks.Dss.Spot.liveTransition := by
  rfl

theorem transitionsSyntax_eq : transitionsSyntax = Benchmarks.Dss.Spot.transitions := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Spot.contract := by
  rfl

end Benchmarks.Dss.Spot.Syntax
