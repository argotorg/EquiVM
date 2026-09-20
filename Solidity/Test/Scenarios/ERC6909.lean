import Solidity.Test.Harness
import Solidity.Test.Specs.ERC6909
import Solm.Examples.OpenZeppelinBench.ERC6909.Bytecode
import Solidity.Test.Fixtures.Erc6909Solc

/-! # Differential cases: ERC6909. -/

namespace Solidity.Test.ERC6909

open Solidity.Test

def S : Nat := 0xA11CE
def Rc : Nat := 0xB0B
def Op : Nat := 0xF00D
def max256 : Nat := 2 ^ 256 - 1

def bal (a id n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"_balances", [.mindex (.address (addr a)), .mindex (.int id)]⟩, n)
def opr (a b : Nat) : Solm.EvaledStorageRef × Nat := (⟨"_operatorApprovals", [.mindex (.address (addr a)), .mindex (.address (addr b))]⟩, 1)
def alw (a b id n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"_allowances", [.mindex (.address (addr a)), .mindex (.address (addr b)), .mindex (.int id)]⟩, n)
def iface (n : Nat) : ABI.ABIValue := .fixedBytes ⟨3, by decide⟩ ((wordBytes (n <<< 224)).toList.take 4)

def transferSig := "transfer(address,uint256,uint256)"
def transferFromSig := "transferFrom(address,address,uint256,uint256)"

def creation : ByteArray := bytesOfHex Fixtures.erc6909CreationHex
def runtime : ByteArray := bytesOfHex Fixtures.erc6909RuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := _root_.OpenZeppelinBench.ERC6909.erc6909BenchBytecode }

def cases : List Case :=
  [ rt "balanceOf" { call := some ("balanceOf(address,uint256)", [.address (addr S), .int 7]),
                     refs := [bal S 7 100], expect := .success },
    rt "allowance" { call := some ("allowance(address,address,uint256)", [.address (addr S), .address (addr Op), .int 7]),
                     refs := [alw S Op 7 60], expect := .success },
    rt "isOperator" { call := some ("isOperator(address,address)", [.address (addr S), .address (addr Op)]),
                      refs := [opr S Op], expect := .success },
    rt "isOperator-false" { call := some ("isOperator(address,address)", [.address (addr S), .address (addr Rc)]),
                            refs := [opr S Op], expect := .success },
    rt "supportsInterface-erc165" { call := some ("supportsInterface(bytes4)", [iface 0x01ffc9a7]),
                                    expect := .success },
    rt "supportsInterface-erc6909" { call := some ("supportsInterface(bytes4)", [iface 0x0f632fb3]),
                                     expect := .success },
    rt "supportsInterface-other" { call := some ("supportsInterface(bytes4)", [iface 0xffffffff]),
                                   expect := .success },
    rt "approve" { call := some ("approve(address,uint256,uint256)", [.address (addr Op), .int 7, .int 100]),
                   expect := .success },
    rt "approve-zero-spender" { call := some ("approve(address,uint256,uint256)", [.address (addr 0), .int 7, .int 100]),
                                expect := .revert },
    rt "setOperator" { call := some ("setOperator(address,bool)", [.address (addr Op), .bool true]),
                       expect := .success },
    rt "setOperator-false" { call := some ("setOperator(address,bool)", [.address (addr Op), .bool false]),
                             refs := [opr S Op], expect := .success },
    rt "setOperator-zero" { call := some ("setOperator(address,bool)", [.address (addr 0), .bool true]),
                            expect := .revert },
    rt "setOperator-dirty-bool" { calldata := selectorOfSig "setOperator(address,bool)" ++ wordBytes Op ++ wordBytes 2,
                                  expect := .revert },
    rt "transfer" { call := some (transferSig, [.address (addr Rc), .int 7, .int 40]), refs := [bal S 7 100],
                    expect := .success },
    rt "transfer-all" { call := some (transferSig, [.address (addr Rc), .int 7, .int 100]),
                        refs := [bal S 7 100], expect := .success },
    rt "transfer-self" { call := some (transferSig, [.address (addr S), .int 7, .int 40]),
                         refs := [bal S 7 100], expect := .success },
    rt "transfer-zero-amount" { call := some (transferSig, [.address (addr Rc), .int 7, .int 0]),
                                expect := .success },
    rt "transfer-insufficient" { call := some (transferSig, [.address (addr Rc), .int 7, .int 101]),
                                 refs := [bal S 7 100], expect := .revert },
    rt "transfer-zero-receiver" { call := some (transferSig, [.address (addr 0), .int 7, .int 1]),
                                  refs := [bal S 7 100], expect := .revert },
    rt "transfer-overflow" { call := some (transferSig, [.address (addr Rc), .int 7, .int 1]),
                             refs := [bal S 7 1, bal Rc 7 max256], expect := .revert },
    rt "transferFrom-allowance" { sender := addr Op,
                                  call := some (transferFromSig, [.address (addr S), .address (addr Rc), .int 7, .int 50]),
                                  refs := [bal S 7 100, alw S Op 7 60], expect := .success },
    rt "transferFrom-max-allowance" { sender := addr Op,
                                      call := some (transferFromSig, [.address (addr S), .address (addr Rc), .int 7, .int 50]),
                                      refs := [bal S 7 100, alw S Op 7 max256], expect := .success },
    rt "transferFrom-insufficient-allowance" { sender := addr Op,
                                               call := some (transferFromSig, [.address (addr S), .address (addr Rc), .int 7, .int 50]),
                                               refs := [bal S 7 100, alw S Op 7 30], expect := .revert },
    rt "transferFrom-operator" { sender := addr Op,
                                 call := some (transferFromSig, [.address (addr S), .address (addr Rc), .int 7, .int 50]),
                                 refs := [bal S 7 100, opr S Op], expect := .success },
    rt "transferFrom-self" { call := some (transferFromSig, [.address (addr S), .address (addr Rc), .int 7, .int 50]),
                             refs := [bal S 7 100], expect := .success },
    rt "transferFrom-insufficient-balance" { sender := addr Op,
                                             call := some (transferFromSig, [.address (addr S), .address (addr Rc), .int 7, .int 50]),
                                             refs := [bal S 7 10, alw S Op 7 60], expect := .revert },
    rt "transferFrom-zero-sender-zero-amount" { sender := addr Op,
                                                call := some (transferFromSig, [.address (addr 0), .address (addr Rc), .int 7, .int 0]),
                                                expect := .revert },
    rt "transferFrom-zero-sender" { sender := addr Op,
                                    call := some (transferFromSig, [.address (addr 0), .address (addr Rc), .int 7, .int 5]),
                                    expect := .revert },
    rt "transfer-nonpayable" { call := some (transferSig, [.address (addr Rc), .int 7, .int 1]),
                               refs := [bal S 7 100], value := 1, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "ERC6909", program := _root_.OpenZeppelinBench.ERC6909.SoliditySpec.program, target := "ERC6909Bench", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "ERC6909/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

end Solidity.Test.ERC6909
