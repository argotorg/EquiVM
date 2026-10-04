import Solidity.Test.Harness
import Solidity.Test.Specs.Consts
import Solidity.Test.Fixtures.ConstsSolc

/-! # Differential cases: typed constants; file-level constants, errors and events. -/

namespace Solidity.Test.Consts

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.constsCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.constsRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := runtime, expect := .success }
def rv (name : String) (c : Case) : Case := { c with name := name, code := runtime, expect := .revert }

def cases : List Case :=
  [ rv "uint8-constant-times-two-overflows" { call := some ("mulSmall()", []) },
    rt "constant-division" { call := some ("divConsts()", []) },
    rt "file-level-uint-constant" { call := some ("wadMul(uint256)", [.int 3]) },
    rt "uint8-constant-add" { call := some ("limitPlus(uint8)", [.int 5]) },
    rv "uint8-constant-add-overflows" { call := some ("limitPlus(uint8)", [.int 6]) },
    rt "bytes16-constant-index" { call := some ("hexDigit(uint8)", [.int 11]) },
    rt "address-constant-equal" { call := some ("isBurn(address)", [.address (addr 0xdEaD)]) },
    rt "address-constant-different" { call := some ("isBurn(address)", [.address (addr 7)]) },
    rt "address-constant-store" { call := some ("setLast()", []) },
    rt "bytes32-constant" { call := some ("uid()", []) },
    rt "bytes4-constant" { call := some ("sel()", []) },
    rt "int256-constant" { call := some ("neg(int256)", [.int 10]) },
    rt "int256-constant-negative-result" { call := some ("neg(int256)", [.int (-3)]) },
    rt "getter-uint8-constant" { call := some ("LIMIT()", []) },
    rt "getter-string-constant" { call := some ("NAME()", []) },
    rt "getter-address-constant" { call := some ("SINK()", []) },
    rv "file-level-error" { call := some ("deny(bool)", [.bool true]) },
    rt "file-level-error-not-taken" { call := some ("deny(bool)", [.bool false]) },
    rv "file-level-error-with-arguments" { call := some ("check(uint256)", [.int 300]) },
    rt "file-level-error-with-arguments-not-taken" { call := some ("check(uint256)", [.int 5]) },
    rt "file-level-event" { call := some ("note(uint256)", [.int 9]) },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def scenario : Scenario :=
  { name := "Consts", program := _root_.Consts.SoliditySpec.program, target := "Consts", cases := cases }

end Solidity.Test.Consts
