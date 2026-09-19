import Solidity.Test.Harness
import Solidity.Examples.ERC20.Spec
import Solm.Examples.ERC20.Bytecode
import Solidity.Test.Fixtures.ERC20Solc

/-!
# Differential cases: ERC20

The runtime cases run against the pinned `erc20Bytecode` and against the local solc's runtime;
the deployment cases run the local solc's creation code (the pinned `erc20Initcode` is a
hand-written constructor without the `Transfer` emit, see `Fixtures/ERC20Solc.lean`).
-/

namespace Solidity.Test.ERC20

open Solidity.Test

def S : Nat := 0xA11CE
def T : Nat := 0xB0B
def F : Nat := 0xF00D

def key (a : Nat) : Solm.EvaledStorageRefStep := .mindex (.address (addr a))
def bal (a n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"balanceOf", [key a]⟩, n)
def alw (o s n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"allowance", [key o, key s]⟩, n)
def sup (n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"totalSupply", []⟩, n)

def max256 : Nat := 2 ^ 256 - 1

def transferSig := "transfer(address,uint256)"
def transferFromSig := "transferFrom(address,address,uint256)"

def creation : ByteArray := bytesOfHex Fixtures.erc20CreationHex
def runtime : ByteArray := bytesOfHex Fixtures.erc20RuntimeHex

/-- A runtime case (sender `S` calls the deployed `erc20Bytecode`). -/
def rt (name : String) (c : Case) : Case := { c with name := name, code := erc20Bytecode }

def cases : List Case :=
  [ rt "totalSupply" { call := some ("totalSupply()", []), refs := [sup 5000], expect := .success },
    rt "balanceOf" { call := some ("balanceOf(address)", [.address (addr S)]), refs := [bal S 1000],
                     expect := .success },
    rt "balanceOf-unset" { call := some ("balanceOf(address)", [.address (addr T)]), expect := .success },
    rt "balanceOf-extra-calldata" { calldata := selectorOfSig "balanceOf(address)" ++ wordBytes S ++ ⟨#[1, 2, 3]⟩,
                                    refs := [bal S 7], expect := .success },
    rt "allowance" { call := some ("allowance(address,address)", [.address (addr F), .address (addr S)]),
                     refs := [alw F S 42], expect := .success },
    rt "transfer" { call := some (transferSig, [.address (addr T), .int 300]),
                    refs := [bal S 1000, sup 1000], expect := .success },
    rt "transfer-insufficient" { call := some (transferSig, [.address (addr T), .int 2000]),
                                 refs := [bal S 1000], expect := .revert },
    rt "transfer-zero" { call := some (transferSig, [.address (addr T), .int 0]), refs := [bal S 1000],
                         expect := .success },
    rt "transfer-self" { call := some (transferSig, [.address (addr S), .int 500]), refs := [bal S 1000],
                         expect := .success },
    rt "transfer-all" { call := some (transferSig, [.address (addr T), .int 1000]), refs := [bal S 1000],
                        expect := .success },
    rt "transfer-overflow" { call := some (transferSig, [.address (addr T), .int 1]),
                             refs := [bal S 1, bal T max256], expect := .revert },
    rt "transfer-to-zero" { call := some (transferSig, [.address (addr 0), .int 5]), refs := [bal S 10],
                            expect := .success },
    rt "transfer-nonpayable" { call := some (transferSig, [.address (addr T), .int 5]), refs := [bal S 10],
                               value := 1, expect := .revert },
    rt "transfer-short-calldata" { calldata := selectorOfSig transferSig ++ wordBytes T, refs := [bal S 10],
                                   expect := .revert },
    rt "transfer-dirty-address" { calldata := selectorOfSig transferSig ++ wordBytes (2 ^ 160 + T) ++ wordBytes 5,
                                  refs := [bal S 10], expect := .revert },
    rt "approve" { call := some ("approve(address,uint256)", [.address (addr T), .int 77]),
                   expect := .success },
    rt "approve-clear" { call := some ("approve(address,uint256)", [.address (addr T), .int 0]),
                         refs := [alw S T 5], expect := .success },
    rt "transferFrom" { call := some (transferFromSig, [.address (addr F), .address (addr T), .int 100]),
                        refs := [alw F S 150, bal F 500], expect := .success },
    rt "transferFrom-insufficient-allowance" { call := some (transferFromSig, [.address (addr F), .address (addr T), .int 100]),
                                               refs := [alw F S 50, bal F 500], expect := .revert },
    rt "transferFrom-insufficient-balance" { call := some (transferFromSig, [.address (addr F), .address (addr T), .int 100]),
                                             refs := [alw F S 150, bal F 50], expect := .revert },
    rt "transferFrom-max-allowance" { call := some (transferFromSig, [.address (addr F), .address (addr T), .int 500]),
                                      refs := [alw F S max256, bal F 500], expect := .success },
    rt "transferFrom-self" { call := some (transferFromSig, [.address (addr S), .address (addr T), .int 100]),
                             refs := [alw S S 100, bal S 100], expect := .success },
    rt "transferFrom-overflow" { call := some (transferFromSig, [.address (addr F), .address (addr T), .int 1]),
                                 refs := [alw F S 1, bal F 1, bal T max256], expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    rt "short-selector" { calldata := ⟨#[0xa9, 0x05]⟩, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([.int 12345], runtime),
      expect := .success },
    { name := "constructor-zero-supply", code := creation, ctorArgs := some ([.int 0], runtime),
      expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([.int 1], runtime),
      value := 1, expect := .revert } ]

def scenario : Scenario :=
  { name := "ERC20", program := _root_.ERC20.SoliditySpec.program, target := _root_.ERC20.SoliditySpec.target,
    cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "ERC20/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned hand-written `erc20Initcode`, which does not emit `Transfer`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "ERC20/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) =>
          let known := if c.expect == .success then some "hand-written initcode does not emit Transfer" else none
          some { c with code := erc20Initcode, ctorArgs := some (args, erc20Bytecode), known := known }
        | none => none }

end Solidity.Test.ERC20
