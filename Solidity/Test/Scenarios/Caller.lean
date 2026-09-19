import Solidity.Test.Harness
import Solidity.Test.Specs.Caller
import Solm.Examples.Caller.Bytecode
import Solm.Examples.Pow.Bytecode
import Solidity.Test.Fixtures.CallerSolc

/-! # Differential cases: Caller. -/

namespace Solidity.Test.Caller

open Solidity.Test

def P : Nat := 0x9099
def E : Nat := 0xE0A

/-- The callee: `Pow` deployed at `P`. -/
def withPow : List (EVM.Address × Ethereum.Account) := [(addr P, account (code := powBytecode))]
def stored (n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"stored", []⟩, n)

def creation : ByteArray := bytesOfHex Fixtures.callerCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.callerRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := callerBytecode }

def cases : List Case :=
  [ rt "run" { call := some ("run(address,uint256)", [.address (addr P), .int 10]), accounts := withPow,
               expect := .success },
    rt "run-overwrite" { call := some ("run(address,uint256)", [.address (addr P), .int 0]),
                         accounts := withPow, refs := [stored 99], expect := .success },
    rt "run-callee-reverts" { call := some ("run(address,uint256)", [.address (addr P), .int 300]),
                              accounts := withPow, expect := .revert },
    rt "run-eoa-target" { call := some ("run(address,uint256)", [.address (addr E), .int 5]),
                          accounts := withPow, expect := .revert },
    rt "run-missing-target" { call := some ("run(address,uint256)", [.address (addr 0x7777), .int 5]),
                              accounts := withPow, expect := .revert },
    rt "run-self-target" { call := some ("run(address,uint256)", [.address (addr 0xC0FFEE), .int 5]),
                           accounts := withPow, expect := .revert },
    rt "run-nonpayable" { call := some ("run(address,uint256)", [.address (addr P), .int 5]),
                          accounts := withPow, value := 1, expect := .revert },
    rt "run-dirty-address" { calldata := selectorOfSig "run(address,uint256)" ++ wordBytes (2 ^ 160 + P) ++ wordBytes 5,
                             accounts := withPow, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "Caller", program := _root_.Caller.SoliditySpec.program, target := "Caller", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "Caller/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `callerInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "Caller/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) => some { c with code := callerInitcode, ctorArgs := some (args, callerBytecode), known := if c.name == "constructor-nonpayable" then some "minimal initcode has no callvalue guard" else none }
        | none => none }

end Solidity.Test.Caller
