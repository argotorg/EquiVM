import Solidity.Test.Harness
import Solidity.Test.Specs.Pausable
import Solm.Examples.OpenZeppelinBench.Pausable.Bytecode
import Solidity.Test.Fixtures.PausableSolc

/-! # Differential cases: Pausable. -/

namespace Solidity.Test.Pausable

open Solidity.Test

def paused : List (Solm.EvaledStorageRef × Nat) := [(⟨"_paused", []⟩, 1)]

def creation : ByteArray := bytesOfHex Fixtures.pausableCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.pausableRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := _root_.OpenZeppelinBench.Pausable.pausableBenchBytecode }

def cases : List Case :=
  [ rt "paused-false" { call := some ("paused()", []), expect := .success },
    rt "paused-true" { call := some ("paused()", []), refs := paused, expect := .success },
    rt "pause" { call := some ("pause()", []), expect := .success },
    rt "pause-already" { call := some ("pause()", []), refs := paused, expect := .revert },
    rt "unpause" { call := some ("unpause()", []), refs := paused, expect := .success },
    rt "unpause-not-paused" { call := some ("unpause()", []), expect := .revert },
    rt "guardedWhenNotPaused" { call := some ("guardedWhenNotPaused()", []), expect := .success },
    rt "guardedWhenNotPaused-paused" { call := some ("guardedWhenNotPaused()", []), refs := paused,
                                       expect := .revert },
    rt "guardedWhenPaused" { call := some ("guardedWhenPaused()", []), refs := paused, expect := .success },
    rt "guardedWhenPaused-not-paused" { call := some ("guardedWhenPaused()", []), expect := .revert },
    rt "pause-nonpayable" { call := some ("pause()", []), value := 1, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "Pausable", program := _root_.OpenZeppelinBench.Pausable.SoliditySpec.program, target := "PausableBench", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "Pausable/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

end Solidity.Test.Pausable
