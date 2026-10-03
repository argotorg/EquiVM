import Solidity.Test.Harness
import Solidity.Test.Specs.Features
import Solidity.Test.Fixtures.FeaturesSolc

/-! # Differential cases: free functions, named arguments, `.selector`, `code.length`, literals,
overloaded events, calldata slices, `bytesN(bytes)`, `bytesN` indexing. -/

namespace Solidity.Test.Features

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.featuresCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.featuresRuntimeHex
def kickerRuntime : ByteArray := bytesOfHex Fixtures.featuresKickerRuntimeHex
def childCreation : ByteArray := bytesOfHex Fixtures.featuresChildCreationHex

def K : Nat := 0x1C1C
def E : Nat := 0xE0A
def U : Nat := 0x05E7

/-- The kicker deployed at `K`. -/
def withKicker : List (EVM.Address × Ethereum.Account) := [(addr K, account (code := kickerRuntime))]

def kA : ABI.ABIValue := .address (addr K)

def rt (name : String) (c : Case) : Case :=
  { c with name := name, code := runtime, accounts := withKicker, expect := .success }

/-- A case expected to revert. -/
def rv (name : String) (c : Case) : Case :=
  { c with name := name, code := runtime, accounts := withKicker, expect := .revert }

def b32 (n : Nat) : ABI.ABIValue := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

/-- `n` distinct bytes `1, 2, …, n`. -/
def bytesN (n : Nat) : ByteArray := ⟨((List.range n).map fun i => UInt8.ofNat (i + 1)).toArray⟩

def cases : List Case :=
  [ rt "sumTo" { call := some ("sumTo(uint256)", [.int 5]) },
    rt "clamped-low" { call := some ("clamped(uint256)", [.int 5]) },
    rt "clamped-mid" { call := some ("clamped(uint256)", [.int 50]) },
    rt "clamped-high" { call := some ("clamped(uint256)", [.int 500]) },
    rt "named-internal" { call := some ("namedInternal(uint256,uint256)", [.int 3, .int 4]) },
    rt "named-external" { call := some ("namedExternal(address,address,uint256)", [kA, .address (addr U), .int 42]) },
    rt "named-new" { call := some ("namedNew(uint256)", [.int 9]) },
    rt "selectors" { call := some ("selectors()", []) },
    rt "code-length-contract" { call := some ("codeLen(address)", [kA]) },
    rt "code-length-eoa" { call := some ("codeLen(address)", [.address (addr E)]) },
    rt "has-code-contract" { call := some ("hasCode(address)", [kA]) },
    rt "has-code-eoa" { call := some ("hasCode(address)", [.address (addr E)]) },
    rt "literals" { call := some ("literals()", []) },
    rt "event-uint" { call := some ("fileUint(bytes32,uint256)", [b32 0x11, .int 7]) },
    rt "event-address" { call := some ("fileAddr(bytes32,address)", [b32 0x11, .address (addr U)]) },
    rt "event-three" { call := some ("fileIlk(bytes32,bytes32,uint256)", [b32 0x22, b32 0x11, .int 9]) },
    rt "event-empty" { call := some ("cage()", []) },
    rt "event-one" { call := some ("cageIlk(bytes32)", [b32 0x22]) },
    rt "slice-head" { call := some ("sliceHead(bytes)", [.bytes (bytesN 8)]) },
    rv "slice-head-short" { call := some ("sliceHead(bytes)", [.bytes (bytesN 2)]) },
    rt "slice-decode" { call := some ("sliceDecode(bytes)", [.bytes (bytesN 4 ++ wordBytes 77 ++ wordBytes U)]) },
    rv "slice-decode-short" { call := some ("sliceDecode(bytes)", [.bytes (bytesN 20)]) },
    rt "slice-mid" { call := some ("sliceMid(bytes,uint256,uint256)", [.bytes (bytesN 10), .int 2, .int 5]) },
    rt "slice-empty" { call := some ("sliceMid(bytes,uint256,uint256)", [.bytes (bytesN 10), .int 3, .int 3]) },
    rv "slice-start-after-end" { call := some ("sliceMid(bytes,uint256,uint256)", [.bytes (bytesN 10), .int 5, .int 2]) },
    rv "slice-end-past-length" { call := some ("sliceMid(bytes,uint256,uint256)", [.bytes (bytesN 10), .int 0, .int 11]) },
    rt "slice-length" { call := some ("sliceLen(bytes,uint256)", [.bytes (bytesN 10), .int 4]) },
    rv "slice-length-bad" { call := some ("sliceLen(bytes,uint256)", [.bytes (bytesN 10), .int 11]) },
    rt "slice-array" { call := some ("sliceArr(uint256[],uint256,uint256)",
                         [.array [.int 1, .int 2, .int 3, .int 4, .int 5], .int 1, .int 4]) },
    rv "slice-array-bad" { call := some ("sliceArr(uint256[],uint256,uint256)",
                             [.array [.int 1, .int 2, .int 3, .int 4, .int 5], .int 4, .int 6]) },
    rt "msg-data-tail" { call := some ("msgTail()", []) },
    rt "bytes-to-bytes4" { call := some ("toB4(bytes)", [.bytes (bytesN 8)]) },
    rt "bytes-to-bytes4-pad" { call := some ("toB4(bytes)", [.bytes (bytesN 2)]) },
    rt "bytes-to-bytes32-pad" { call := some ("toB32(bytes)", [.bytes (bytesN 5)]) },
    rt "bytes-to-bytes32-truncate" { call := some ("toB32(bytes)", [.bytes (bytesN 40)]) },
    rt "bytesN-index-first" { call := some ("byteAt(bytes32,uint256)", [b32 0x0102030405, .int 0]) },
    rt "bytesN-index-last" { call := some ("byteAt(bytes32,uint256)", [b32 0x0102030405, .int 31]) },
    rv "bytesN-index-out-of-range" { call := some ("byteAt(bytes32,uint256)", [b32 0x0102030405, .int 32]) },
    rt "hex-digit" { call := some ("hexDigit(uint8)", [.int 10]) },
    rt "hex-digit-masked" { call := some ("hexDigit(uint8)", [.int 255]) },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def scenario : Scenario :=
  { name := "Features", program := _root_.Features.SoliditySpec.program, target := "Features", cases := cases,
    creations := [("Child", childCreation)] }

end Solidity.Test.Features
