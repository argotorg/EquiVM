import Solidity.Test.Harness
import Solidity.Test.Specs.AccessControl
import Solm.Examples.OpenZeppelinBench.AccessControl.Bytecode
import Solidity.Test.Fixtures.AccessControlSolc

/-! # Differential cases: AccessControl. -/

namespace Solidity.Test.AccessControl

open Solidity.Test

def Adm : Nat := 0xA11CE
def U : Nat := 0xB0B
def R : Nat := 0x1234

def roleKey (r : Nat) : Solm.KeyValue := .fixedBytes ⟨31, by decide⟩ (wordBytes r).toList
def role (r : Nat) : ABI.ABIValue := .fixedBytes ⟨31, by decide⟩ (wordBytes r).toList
def has (r a : Nat) : Solm.EvaledStorageRef × Nat := (⟨"_roles", [.mindex (roleKey r), .field "hasRole", .mindex (.address (addr a))]⟩, 1)
def adminOf (r adm : Nat) : Solm.EvaledStorageRef × Nat := (⟨"_roles", [.mindex (roleKey r), .field "adminRole"]⟩, adm)
def iface (n : Nat) : ABI.ABIValue := .fixedBytes ⟨3, by decide⟩ ((wordBytes (n <<< 224)).toList.take 4)

def admin : List (Solm.EvaledStorageRef × Nat) := [has 0 Adm]

def creation : ByteArray := bytesOfHex Fixtures.accessControlCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.accessControlRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := _root_.OpenZeppelinBench.AccessControl.accessControlBenchBytecode }

def cases : List Case :=
  [ rt "DEFAULT_ADMIN_ROLE" { call := some ("DEFAULT_ADMIN_ROLE()", []), expect := .success },
    rt "hasRole" { call := some ("hasRole(bytes32,address)", [role 0, .address (addr Adm)]), refs := admin,
                   expect := .success },
    rt "hasRole-false" { call := some ("hasRole(bytes32,address)", [role R, .address (addr U)]), refs := admin,
                         expect := .success },
    rt "getRoleAdmin-default" { call := some ("getRoleAdmin(bytes32)", [role R]), expect := .success },
    rt "getRoleAdmin-set" { call := some ("getRoleAdmin(bytes32)", [role R]), refs := [adminOf R 0x99],
                            expect := .success },
    rt "supportsInterface-erc165" { call := some ("supportsInterface(bytes4)", [iface 0x01ffc9a7]),
                                    expect := .success },
    rt "supportsInterface-accesscontrol" { call := some ("supportsInterface(bytes4)", [iface 0x7965db0b]),
                                           expect := .success },
    rt "supportsInterface-other" { call := some ("supportsInterface(bytes4)", [iface 0xffffffff]),
                                   expect := .success },
    rt "supportsInterface-dirty-bytes4" { calldata := selectorOfSig "supportsInterface(bytes4)" ++ wordBytes ((0x01ffc9a7 <<< 224) + 1),
                                          expect := .revert },
    rt "grantRole" { call := some ("grantRole(bytes32,address)", [role R, .address (addr U)]), refs := admin,
                     expect := .success },
    rt "grantRole-already" { call := some ("grantRole(bytes32,address)", [role R, .address (addr U)]),
                             refs := admin ++ [has R U], expect := .success },
    rt "grantRole-unauthorized" { sender := addr U,
                                  call := some ("grantRole(bytes32,address)", [role R, .address (addr U)]),
                                  refs := admin, expect := .revert },
    rt "grantRole-custom-admin" { sender := addr U,
                                  call := some ("grantRole(bytes32,address)", [role R, .address (addr Adm)]),
                                  refs := admin ++ [adminOf R 0x99, has 0x99 U], expect := .success },
    rt "revokeRole" { call := some ("revokeRole(bytes32,address)", [role R, .address (addr U)]),
                      refs := admin ++ [has R U], expect := .success },
    rt "revokeRole-absent" { call := some ("revokeRole(bytes32,address)", [role R, .address (addr U)]),
                             refs := admin, expect := .success },
    rt "revokeRole-unauthorized" { sender := addr U,
                                   call := some ("revokeRole(bytes32,address)", [role 0, .address (addr Adm)]),
                                   refs := admin, expect := .revert },
    rt "renounceRole" { sender := addr U,
                        call := some ("renounceRole(bytes32,address)", [role R, .address (addr U)]),
                        refs := admin ++ [has R U], expect := .success },
    rt "renounceRole-bad-confirmation" { sender := addr U,
                                         call := some ("renounceRole(bytes32,address)", [role R, .address (addr Adm)]),
                                         refs := admin ++ [has R U], expect := .revert },
    rt "hasRole-nonpayable" { call := some ("hasRole(bytes32,address)", [role 0, .address (addr Adm)]),
                              value := 1, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "AccessControl", program := _root_.OpenZeppelinBench.AccessControl.SoliditySpec.program, target := "AccessControlBench", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "AccessControl/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

end Solidity.Test.AccessControl
