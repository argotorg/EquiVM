import Solidity.Test.Harness
import Solidity.Test.Specs.Reuse
import Solm.Examples.Reuse.Bytecode
import Solidity.Test.Fixtures.ReuseSolc

/-! # Differential cases: Reuse. -/

namespace Solidity.Test.Reuse

open Solidity.Test

def sv (n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"s", []⟩, n)

def creation : ByteArray := bytesOfHex Fixtures.reuseCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.reuseRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := cBytecode }

def cases : List Case :=
  [ rt "f" { call := some ("f(uint256)", [.int 5]), expect := .success },
    rt "f-max-ok" { call := some ("f(uint256)", [.int (2 ^ 255 - 1)]), expect := .success },
    rt "f-overflow" { call := some ("f(uint256)", [.int (2 ^ 255)]), expect := .revert },
    rt "g" { call := some ("g(uint256)", [.int 5]), refs := [sv 1], expect := .success },
    rt "g-overflow" { call := some ("g(uint256)", [.int (2 ^ 255)]), expect := .revert },
    rt "f-nonpayable" { call := some ("f(uint256)", [.int 5]), value := 1, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "Reuse", program := _root_.Reuse.SoliditySpec.program, target := "C", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "Reuse/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `cInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "Reuse/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) => some { c with code := cInitcode, ctorArgs := some (args, cBytecode), known := if c.name == "constructor-nonpayable" then some "minimal initcode has no callvalue guard" else none }
        | none => none }

end Solidity.Test.Reuse
