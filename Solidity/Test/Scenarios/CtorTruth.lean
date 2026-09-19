import Solidity.Test.Harness
import Solidity.Test.Specs.CtorTruth
import Solm.Examples.CtorTruth.Bytecode
import Solidity.Test.Fixtures.CtorTruthSolc

/-! # Differential cases: CtorTruth. -/

namespace Solidity.Test.CtorTruth

open Solidity.Test


def creation : ByteArray := bytesOfHex Fixtures.ctorTruthCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.ctorTruthRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := ctorTruthRuntimeBytecode }

def cases : List Case :=
  [ rt "truth" { call := some ("truth()", []), expect := .success },
    rt "truth-nonpayable" { call := some ("truth()", []), value := 1, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-payable", code := creation, ctorArgs := some ([], runtime), value := 7,
      balance := 7, expect := .success } ]

def scenario : Scenario :=
  { name := "CtorTruth", program := _root_.CtorTruth.SoliditySpec.program, target := "CtorTruth", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "CtorTruth/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `ctorTruthInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "CtorTruth/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) => some { c with code := ctorTruthInitcode, ctorArgs := some (args, ctorTruthRuntimeBytecode), known := none }
        | none => none }

end Solidity.Test.CtorTruth
