import Solidity.Test.Harness
import Solidity.Test.Specs.BaseCall
import Solidity.Test.Fixtures.BaseCallSolc

/-! # Differential cases: explicit base calls. -/

namespace Solidity.Test.BaseCall

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.baseCallCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.baseCallRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := runtime }

def cases : List Case :=
  [ rt "callA" { call := some ("callA()", []), expect := .success },
    rt "callB" { call := some ("callB()", []), expect := .success },
    rt "callSuper" { call := some ("callSuper()", []), expect := .success },
    rt "callOwn" { call := some ("callOwn()", []), expect := .success },
    rt "setViaA" { call := some ("setViaA(uint256)", [.int 7]), expect := .success },
    rt "setViaB" { call := some ("setViaB(uint256)", [.int 7]), expect := .success },
    rt "checkViaA-ok" { call := some ("checkViaA(uint256)", [.int 5]), expect := .success },
    rt "checkViaA-reverts" { call := some ("checkViaA(uint256)", [.int 0]), expect := .revert },
    rt "x" { call := some ("x()", []), expect := .success },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def scenario : Scenario :=
  { name := "BaseCall", program := _root_.BaseCall.SoliditySpec.program, target := "C", cases := cases }

end Solidity.Test.BaseCall
