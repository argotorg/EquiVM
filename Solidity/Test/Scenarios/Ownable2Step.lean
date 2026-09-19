import Solidity.Test.Harness
import Solidity.Test.Specs.Ownable2Step
import Solm.Examples.OpenZeppelinBench.Ownable2Step.Bytecode
import Solidity.Test.Fixtures.Ownable2StepSolc

/-! # Differential cases: Ownable2Step. -/

namespace Solidity.Test.Ownable2Step

open Solidity.Test

def O : Nat := 0xA11CE
def N : Nat := 0xB0B

def owner (a : Nat) : Solm.EvaledStorageRef × Nat := (⟨"_owner", []⟩, a)
def pending (a : Nat) : Solm.EvaledStorageRef × Nat := (⟨"_pendingOwner", []⟩, a)

def creation : ByteArray := bytesOfHex Fixtures.ownable2StepCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.ownable2StepRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := _root_.OpenZeppelinBench.Ownable2Step.ownable2StepBenchBytecode }

def cases : List Case :=
  [ rt "owner" { call := some ("owner()", []), refs := [owner O], expect := .success },
    rt "pendingOwner" { call := some ("pendingOwner()", []), refs := [owner O, pending N], expect := .success },
    rt "transferOwnership" { call := some ("transferOwnership(address)", [.address (addr N)]),
                             refs := [owner O], expect := .success },
    rt "transferOwnership-zero" { call := some ("transferOwnership(address)", [.address (addr 0)]),
                                  refs := [owner O, pending N], expect := .success },
    rt "transferOwnership-not-owner" { sender := addr N,
                                       call := some ("transferOwnership(address)", [.address (addr N)]),
                                       refs := [owner O], expect := .revert },
    rt "acceptOwnership" { sender := addr N, call := some ("acceptOwnership()", []),
                           refs := [owner O, pending N], expect := .success },
    rt "acceptOwnership-not-pending" { call := some ("acceptOwnership()", []), refs := [owner O, pending N],
                                       expect := .revert },
    rt "acceptOwnership-none-pending" { sender := addr N, call := some ("acceptOwnership()", []),
                                        refs := [owner O], expect := .revert },
    rt "renounceOwnership" { call := some ("renounceOwnership()", []), refs := [owner O, pending N],
                             expect := .success },
    rt "renounceOwnership-not-owner" { sender := addr N, call := some ("renounceOwnership()", []),
                                       refs := [owner O], expect := .revert },
    rt "owner-nonpayable" { call := some ("owner()", []), refs := [owner O], value := 1, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, refs := [owner O], expect := .revert },
    rt "empty-calldata" { refs := [owner O], expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([.address (addr O)], runtime),
      expect := .success },
    { name := "constructor-other-owner", code := creation, ctorArgs := some ([.address (addr N)], runtime),
      expect := .success },
    { name := "constructor-zero-owner", code := creation, ctorArgs := some ([.address (addr 0)], runtime),
      expect := .revert },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([.address (addr O)], runtime),
      value := 1, expect := .revert } ]

def scenario : Scenario :=
  { name := "Ownable2Step", program := _root_.OpenZeppelinBench.Ownable2Step.SoliditySpec.program, target := "Ownable2StepBench", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "Ownable2Step/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

end Solidity.Test.Ownable2Step
