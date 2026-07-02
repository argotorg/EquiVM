import Benchmarks.Dss.Dai.Spec
import Solm.Notation

/-!
# MakerDAO DSS Dai spec through the Solm notation frontend

This file exposes a notation-side presentation for the parts of the Dai scaffold covered by the
current Solm frontend, and checks by `rfl` that it is definitionally equal to the AST spec in
`Benchmarks/Dss/Dai/Spec.lean`.
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Dai.Syntax

def storageDeclsSyntax : List StorageDecl :=
  sState% {
    (address => uint256)              wards
    uint256                           totalSupply
    (address => uint256)              balanceOf
    (address => (address => uint256)) allowance
    (address => uint256)              nonces
  } ++
  [ { name := "DOMAIN_SEPARATOR", ty := bytes32St } ]

def relyTransitionSyntax : TransitionDecl :=
  { name := "rely"
    params := [{ name := "guy", ty := addr }]
    returnType := []
    body := sBlock% {
      require msg.value == 0
      require @wards[msg.sender] == 1
      @wards[guy] := 1
    } }

def approveTransitionSyntax : TransitionDecl :=
  solm_transition approve (usr : address) (wad : uint256) -> bool {
    require msg.value == 0
    @allowance[msg.sender][usr] := wad
    return true
  }

def transferTransitionSyntax : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "dst", ty := addr }, { name := "wad", ty := uint256 }]
    returnType := [boolTy]
    body :=
      sBlock% {
        require msg.value == 0
      } ++
      [ .internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok" ] ++
      sBlock% {
        return _ok
      } }

def transitionsSyntax : List TransitionDecl :=
  [ allowanceTransition,
    approveTransitionSyntax,
    balanceOfTransition,
    burnTransition,
    decimalsTransition,
    denyTransition,
    domainSeparatorTransition,
    mintTransition,
    moveTransition,
    nameTransition,
    noncesTransition,
    permitTransition,
    permitTypehashTransition,
    pullTransition,
    pushTransition,
    relyTransitionSyntax,
    symbolTransition,
    totalSupplyTransition,
    transferTransitionSyntax,
    transferFromTransition,
    versionTransition,
    wardsTransition ]

def contractSyntax : ContractDecl :=
  { name := "Dai"
    storage := storageDeclsSyntax
    ctor := constructorDecl
    functions := []
    transitions := transitionsSyntax }

theorem storageDeclsSyntax_eq : storageDeclsSyntax = Benchmarks.Dss.Dai.storageDecls := by
  rfl

theorem relyTransitionSyntax_eq : relyTransitionSyntax = Benchmarks.Dss.Dai.relyTransition := by
  rfl

theorem approveTransitionSyntax_eq :
    approveTransitionSyntax = Benchmarks.Dss.Dai.approveTransition := by
  rfl

theorem transferTransitionSyntax_eq :
    transferTransitionSyntax = Benchmarks.Dss.Dai.transferTransition := by
  rfl

theorem transitionsSyntax_eq : transitionsSyntax = Benchmarks.Dss.Dai.transitions := by
  rfl

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Dai.contract := by
  rfl

end Benchmarks.Dss.Dai.Syntax
