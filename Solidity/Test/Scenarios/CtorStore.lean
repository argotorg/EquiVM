import Solidity.Test.Harness
import Solidity.Test.Specs.CtorStore
import Solm.Examples.CtorStore.Bytecode
import Solidity.Test.Fixtures.CtorStoreSolc

/-! # Differential cases: CtorStore. -/

namespace Solidity.Test.CtorStore

open Solidity.Test


def creation : ByteArray := bytesOfHex Fixtures.ctorStoreCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.ctorStoreRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := ctorStoreRuntimeBytecode }

def cases : List Case :=
  [ rt "any-call-reverts" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([.int 42], runtime), expect := .success },
    { name := "constructor-zero", code := creation, ctorArgs := some ([.int 0], runtime), expect := .success },
    { name := "constructor-payable", code := creation, ctorArgs := some ([.int 42], runtime), value := 5,
      balance := 5, expect := .success } ]

def scenario : Scenario :=
  { name := "CtorStore", program := _root_.CtorStore.SoliditySpec.program, target := "CtorStore", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "CtorStore/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `ctorStoreInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "CtorStore/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) => some { c with code := ctorStoreInitcode, ctorArgs := some (args, ctorStoreRuntimeBytecode), known := none }
        | none => none }

end Solidity.Test.CtorStore
