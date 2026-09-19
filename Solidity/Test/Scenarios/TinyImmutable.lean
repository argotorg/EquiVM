import Solidity.Test.Harness
import Solidity.Test.Specs.TinyImmutable
import Solm.Examples.TinyImmutable.Bytecode

/-! # Differential cases: TinyImmutable (immutables; the pinned runtime is solc's zero-filled template). -/

namespace Solidity.Test.TinyImmutable

open Solidity.Test

def O : Nat := 0xA11CE
def N : Nat := 0xB0B

/-- solc `immutableReferences` byte offsets in the runtime (`Examples/TinyImmutable/Immutables.lean`). -/
def ownerOffsets : List Nat := [72, 245]
def scaleOffsets : List Nat := [186, 361]

def patch (rt : ByteArray) (offs : List Nat) (v : Nat) : ByteArray :=
  offs.foldl (fun b off => (wordBytes v).copySlice 0 b off 32) rt

/-- The pinned runtime (zero immutables) instantiated with `owner`/`scale`. -/
def runtimeWith (owner scale : Nat) : ByteArray :=
  patch (patch _root_.TinyImmutable.tinyImmutableBytecode ownerOffsets owner) scaleOffsets scale

def u256 (n : Nat) : Value := .uint ⟨256, by decide⟩ n

def creation : ByteArray := _root_.TinyImmutable.tinyImmutableCreationBytecode

/-- Runtime instantiated with `owner = O`, `scale = 7`. -/
def rt (name : String) (c : Case) : Case := { c with name := name, code := runtimeWith O 7 }

def cases : List Case :=
  [ rt "owner" { call := some ("owner()", []), expect := .success },
    rt "scale" { call := some ("scale()", []), expect := .success },
    rt "quote" { call := some ("quote(uint256)", [.int 3]), expect := .success },
    rt "quote-wraps" { call := some ("quote(uint256)", [.int (2 ^ 256 - 1)]), expect := .success },
    rt "quote-not-owner" { sender := addr N, call := some ("quote(uint256)", [.int 3]), expect := .revert },
    rt "quote-nonpayable" { call := some ("quote(uint256)", [.int 3]), value := 1, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([.address (addr O), .int 7, .bool true], runtimeWith O 7),
      expect := .success },
    { name := "constructor-no-scale", code := creation, ctorArgs := some ([.address (addr O), .int 7, .bool false], runtimeWith O 0),
      expect := .success },
    { name := "constructor-zero-owner", code := creation, ctorArgs := some ([.address (addr 0), .int 0, .bool true], runtimeWith 0 0),
      expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([.address (addr O), .int 7, .bool true], runtimeWith O 7),
      value := 1, expect := .revert } ]

def scenario : Scenario :=
  { name := "TinyImmutable", program := _root_.TinyImmutable.SoliditySpec.program,
    target := _root_.TinyImmutable.SoliditySpec.target, cases := cases,
    immutables := [("owner", .address (addr O)), ("scale", u256 7)] }

end Solidity.Test.TinyImmutable
