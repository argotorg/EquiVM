import Solidity.Test.Harness
import Solidity.Test.Specs.Fixes
import Solidity.Test.Fixtures.FixesSolc

/-! # Differential cases: operand order, block scoping, modifier arguments, `super` in modifiers. -/

namespace Solidity.Test.Fixes

open Solidity.Test

def program : Program := _root_.Fixes.SoliditySpec.program

def mk (name target : String) (creation runtime : String) (calls : List (String × List ABI.ABIValue × Expect))
    (extra : List Case := []) : Scenario :=
  let rt := bytesOfHex runtime
  { name := name, program := program, target := target,
    cases := (calls.map fun (sig, args, e) => { name := sig, code := rt, call := some (sig, args), expect := e }) ++
      extra ++ [{ name := "constructor", code := bytesOfHex creation, ctorArgs := some ([], rt), expect := .success }] }

def evalOrder : Scenario :=
  mk "EvalOrder" "EvalOrder" Fixtures.evalOrderCreationHex Fixtures.evalOrderRuntimeHex
    [ ("sub()", [], .success), ("lt()", [], .success), ("addSelf()", [], .success),
      ("shortAnd(bool)", [.bool false], .success), ("shortAnd(bool)", [.bool true], .success),
      ("shortOr(bool)", [.bool false], .success), ("shortOr(bool)", [.bool true], .success) ]

def blockScope : Scenario :=
  mk "BlockScope" "BlockScope" Fixtures.blockScopeCreationHex Fixtures.blockScopeRuntimeHex
    [ ("f()", [], .success), ("g()", [], .success), ("h(uint256)", [.int 4], .success), ("h(uint256)", [.int 0], .success) ]

def modifierArgs : Scenario :=
  mk "ModifierArgs" "ModifierArgs" Fixtures.modifierArgsCreationHex Fixtures.modifierArgsRuntimeHex
    [ ("f()", [], .success), ("g()", [], .success), ("seenLen()", [], .success) ]
    [ { name := "g-guard-passes", code := bytesOfHex Fixtures.modifierArgsRuntimeHex, call := some ("g()", []),
        storage := [(⟨0⟩, ⟨5⟩)], expect := .success } ]

def superMod : Scenario :=
  mk "SuperMod" "SuperMod" Fixtures.superModCreationHex Fixtures.superModRuntimeHex
    [ ("f()", [], .success), ("h()", [], .success), ("g()", [], .success), ("x()", [], .success) ]

end Solidity.Test.Fixes
