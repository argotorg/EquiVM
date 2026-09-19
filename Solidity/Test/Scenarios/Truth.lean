import Solidity.Test.Harness
import Solidity.Test.Specs.Truth
import Solm.Examples.Truth.Bytecode
import Solidity.Test.Fixtures.TruthSolc

/-! # Differential cases: Truth. -/

namespace Solidity.Test.Truth

open Solidity.Test


def creation : ByteArray := bytesOfHex Fixtures.truthCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.truthRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := truthBytecode }

def cases : List Case :=
  [ rt "truth" { call := some ("truth()", []), expect := .success },
    rt "truth-extra-calldata" { calldata := selectorOfSig "truth()" ++ ⟨#[1]⟩, expect := .success },
    rt "truth-nonpayable" { call := some ("truth()", []), value := 1, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "Truth", program := _root_.Truth.SoliditySpec.program, target := "Truth", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "Truth/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

end Solidity.Test.Truth
