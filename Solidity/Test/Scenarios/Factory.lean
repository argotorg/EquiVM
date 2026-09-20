import Solidity.Test.Harness
import Solidity.Test.Specs.Factory
import Solidity.Test.Fixtures.FactorySolc

/-! # Differential cases: Factory (contract creation with `new`). -/

namespace Solidity.Test.Factory

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.factoryCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.factoryRuntimeHex
def childCreation : ByteArray := bytesOfHex Fixtures.childCreationHex

def b32 (n : Nat) : ABI.ABIValue := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

def rt (name : String) (c : Case) : Case := { c with name := name, code := runtime }

def cases : List Case :=
  [ rt "make" { call := some ("make(uint256)", [.int 5]), expect := .success },
    rt "make-with-value" { call := some ("make(uint256)", [.int 5]), value := 3, balance := 10, expect := .success },
    rt "make-zero" { call := some ("make(uint256)", [.int 0]), expect := .success },
    rt "make-ctor-reverts" { call := some ("make(uint256)", [.int 7]), expect := .revert },
    rt "make-insufficient-balance" { call := some ("make(uint256)", [.int 5]), value := 3, balance := 1,
                                     expect := .revert },
    rt "make2" { call := some ("make2(uint256,bytes32)", [.int 5, b32 0x1234]), expect := .success },
    rt "make2-zero-salt" { call := some ("make2(uint256,bytes32)", [.int 5, b32 0]), expect := .success },
    rt "make2-ctor-reverts" { call := some ("make2(uint256,bytes32)", [.int 7, b32 0x1234]), expect := .revert },
    rt "make2-nonpayable" { call := some ("make2(uint256,bytes32)", [.int 5, b32 1]), value := 1, expect := .revert },
    rt "makeAndRead" { call := some ("makeAndRead(uint256)", [.int 4]), expect := .success },
    rt "makeAndRead-ctor-reverts" { call := some ("makeAndRead(uint256)", [.int 7]), expect := .revert },
    rt "last" { call := some ("last()", []), expect := .success },
    rt "count" { call := some ("count()", []), refs := [(⟨"count", []⟩, 3)], expect := .success },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "Factory", program := _root_.Factory.SoliditySpec.program, target := "Factory", cases := cases,
    creations := [("Child", childCreation)] }

end Solidity.Test.Factory
