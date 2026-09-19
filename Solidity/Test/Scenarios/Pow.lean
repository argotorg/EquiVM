import Solidity.Test.Harness
import Solidity.Test.Specs.Pow
import Solm.Examples.Pow.Bytecode
import Solidity.Test.Fixtures.PowSolc

/-! # Differential cases: Pow. -/

namespace Solidity.Test.Pow

open Solidity.Test


def creation : ByteArray := bytesOfHex Fixtures.powCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.powRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := powBytecode }

def cases : List Case :=
  [ rt "pow2-10" { call := some ("pow2(uint256)", [.int 10]), expect := .success },
    rt "pow2-0" { call := some ("pow2(uint256)", [.int 0]), expect := .success },
    rt "pow2-255" { call := some ("pow2(uint256)", [.int 255]), expect := .success },
    rt "pow2-256" { call := some ("pow2(uint256)", [.int 256]), expect := .revert },
    rt "pow2-huge" { call := some ("pow2(uint256)", [.int (2 ^ 256 - 1)]), expect := .revert },
    rt "pow2-nonpayable" { call := some ("pow2(uint256)", [.int 3]), value := 1, expect := .revert },
    rt "pow2-short-calldata" { calldata := selectorOfSig "pow2(uint256)" ++ ⟨#[1, 2]⟩, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "Pow", program := _root_.Pow.SoliditySpec.program, target := "Pow", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "Pow/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `powInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "Pow/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) => some { c with code := powInitcode, ctorArgs := some (args, powBytecode), known := if c.name == "constructor-nonpayable" then some "minimal initcode has no callvalue guard" else none }
        | none => none }

end Solidity.Test.Pow
