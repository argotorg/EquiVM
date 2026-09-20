import Solidity.Test.Harness
import Solidity.Test.Specs.TryCatch
import Solidity.Test.Fixtures.TryCatchSolc

/-! # Differential cases: try/catch (external calls and `new`). -/

namespace Solidity.Test.TryCatch

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.tryCallerCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.tryCallerRuntimeHex
def calleeRuntime : ByteArray := bytesOfHex Fixtures.tryCalleeRuntimeHex
def childCreation : ByteArray := bytesOfHex Fixtures.tryChildCreationHex

def C : Nat := 0xCA11EE
def E : Nat := 0xE0A

/-- The callee deployed at `C`. -/
def withCallee : List (EVM.Address × Ethereum.Account) := [(addr C, account (code := calleeRuntime))]

def cA : ABI.ABIValue := .address (addr C)

def rt (name : String) (c : Case) : Case := { c with name := name, code := runtime, accounts := withCallee }

def cases : List Case :=
  [ rt "ok" { call := some ("tryOk(address,uint256)", [cA, .int 5]), expect := .success },
    rt "require-caught" { call := some ("tryRequire(address,uint256)", [cA, .int 5]), expect := .success },
    rt "require-passes" { call := some ("tryRequire(address,uint256)", [cA, .int 50]), expect := .success },
    rt "panic-caught" { call := some ("tryPanic(address,uint256)", [cA, .int 1]), expect := .success },
    rt "custom-error-clause-only-bubbles" { call := some ("tryCustomErrorOnly(address,uint256)", [cA, .int 3]),
                                            expect := .revert },
    rt "custom-low-level-caught" { call := some ("tryCustomLow(address,uint256)", [cA, .int 3]), expect := .success },
    rt "plain-generic-clause" { call := some ("tryPlain(address)", [cA]), expect := .success },
    rt "no-return" { call := some ("tryNoReturn(address,uint256)", [cA, .int 9]), expect := .success },
    rt "no-return-eoa" { call := some ("tryNoReturn(address,uint256)", [.address (addr E), .int 9]) },
    rt "bad-return" { call := some ("tryBadReturn(address)", [cA]) },
    rt "ignore-returns" { call := some ("tryIgnoreReturns(address,uint256)", [cA, .int 5]), expect := .success },
    rt "ignore-bad-return" { call := some ("tryIgnoreBad(address)", [cA]) },
    rt "arg-revert-uncaught" { call := some ("tryArgRevert(address)", [cA]), expect := .revert },
    rt "new-ok" { call := some ("tryNew(uint256)", [.int 5]), expect := .success },
    rt "new-caught" { call := some ("tryNew(uint256)", [.int 7]), expect := .success },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def scenario : Scenario :=
  { name := "TryCatch", program := _root_.TryCatch.SoliditySpec.program, target := "TryCaller", cases := cases,
    creations := [("Child", childCreation)] }

end Solidity.Test.TryCatch
