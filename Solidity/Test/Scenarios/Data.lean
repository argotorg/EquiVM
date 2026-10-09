import Solidity.Test.Harness
import Solidity.Test.Specs.Data
import Solidity.Test.Fixtures.DataSolc

/-! # Differential cases: storage layout, arrays, structs, memory references, `delete`, byte arrays.

`Data` holds a few cases per function (the fuzzer mutates these); `Data/boundaries` runs boundary
values and is not fuzzed; `Data/alloc` checks the memory allocation limit. -/

namespace Solidity.Test.Data

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.dataCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.dataRuntimeHex
def allocRuntime : ByteArray := bytesOfHex Fixtures.allocRuntimeHex

def mk (sig : String) (args : List Solm.Value) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args) }

def b4 (n : Nat) : Solm.Value := .fixedBytes ⟨3, by decide⟩ ((wordBytes n).toList.drop 28)
def b1 (n : Nat) : Solm.Value := .fixedBytes ⟨0, by decide⟩ [UInt8.ofNat n]
def bytesN (n : Nat) : ByteArray := ⟨((List.range n).map fun i => UInt8.ofNat (i + 1)).toArray⟩
def str (n : Nat) : Solm.Value := .bytes ⟨((List.range n).map fun i => UInt8.ofNat (97 + i % 26)).toArray⟩
def A : Solm.Value := .address (addr 0xA11CE)

def U8 : List Int := [0, 1, 127, 254, 255]
def U16 : List Int := [0, 1, 65534, 65535]
def I64 : List Int := [-(2 ^ 63), -(2 ^ 63) + 4, -(2 ^ 63) + 5, -1, 0, 5, 2 ^ 63 - 1]
def U128 : List Int := [0, 1, 2 ^ 64, 2 ^ 128 - 6, 2 ^ 128 - 5, 2 ^ 128 - 1]
def U256 : List Int := [0, 1, 2 ^ 128, 2 ^ 256 - 3, 2 ^ 256 - 1]

/-- A few cases per function. -/
def cases : List Case :=
  [ mk "packed(bool,uint8,address,uint16,int64,bytes4)" [.bool true, .int 200, A, .int 65535, .int (-5), b4 0x12345678],
    mk "packedBump(uint8,uint16,int64)" [.int 5, .int 9, .int 0],
    mk "packedClear(uint8,address)" [.int 7, A],
    mk "fixedStore(uint256,uint256)" [.int 2, .int 9],
    mk "fixedMem(uint256,uint256,uint256)" [.int 3, .int 4, .int 2],
    mk "smallOps(uint8,uint8,uint8,uint256)" [.int 1, .int 2, .int 3, .int 1],
    mk "smallMany(uint8)" [.int 40], mk "smallClear(uint8)" [.int 5], mk "popEmpty()" [],
    mk "nestedOps(uint256,uint256,uint256)" [.int 7, .int 1, .int 1],
    mk "ptOps(uint128,uint128,uint256)" [.int 3, .int 4, .int 9], mk "ptPtr(uint256,uint128)" [.int 9, .int 5],
    mk "ptsOps(uint128,uint128,uint256)" [.int 3, .int 4, .int 1],
    mk "recOps(address,uint64,bool,uint256,uint8)" [A, .int 77, .bool true, .int 1000, .int 9],
    mk "recClear(address,uint256,uint8)" [A, .int 1000, .int 9], mk "pointClear(uint256,uint128)" [.int 9, .int 5],
    mk "newArr(uint8)" [.int 5], mk "newBytes(uint8)" [.int 5], mk "memAlias(uint256)" [.int 7],
    mk "memStruct(uint128)" [.int 5], mk "memCopy(uint128)" [.int 5],
    mk "blobOps(bytes,uint256)" [.bytes (bytesN 5), .int 2] "short", mk "blobOps(bytes,uint256)" [.bytes (bytesN 40), .int 35] "long",
    mk "blobClear(bytes)" [.bytes (bytesN 40)],
    mk "blobSet(bytes,uint256,bytes1)" [.bytes (bytesN 5), .int 2, b1 0xfe] "short",
    mk "blobSet(bytes,uint256,bytes1)" [.bytes (bytesN 40), .int 35, b1 0xfe] "long",
    mk "textOps(string)" [str 5] "short", mk "textOps(string)" [str 40] "long",
    mk "fixedArr(uint256)" [.int 2], mk "smallArr(uint256)" [.int 0], mk "pt()" [], mk "points(uint256)" [.int 1],
    mk "pts(uint256)" [.int 0], mk "blob()" [], mk "text()" [], mk "small8()" [], mk "sneg()" [], mk "tag()" [],
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def boundaries : List Case :=
  ([true, false].flatMap fun a => U8.flatMap fun b => U16.flatMap fun d => I64.map fun e =>
    mk "packed(bool,uint8,address,uint16,int64,bytes4)" [.bool a, .int b, A, .int d, .int e, b4 0xffffffff] s!"{a} {b} {d} {e}") ++
  (U8.flatMap fun b => U16.flatMap fun d => I64.map fun e =>
    mk "packedBump(uint8,uint16,int64)" [.int b, .int d, .int e] s!"{b} {d} {e}") ++
  (U8.map fun b => mk "packedClear(uint8,address)" [.int b, A] s!"{b}") ++
  ([(0 : Int), 1, 4, 5, 6, 2 ^ 255].flatMap fun i => U256.map fun v => mk "fixedStore(uint256,uint256)" [.int i, .int v] s!"{i} {v}") ++
  ([(0 : Int), 1, 2, 3, 4].flatMap fun i => U256.map fun a => mk "fixedMem(uint256,uint256,uint256)" [.int a, .int 1, .int i] s!"{a} {i}") ++
  (U8.flatMap fun a => [(0 : Int), 1, 2, 3].map fun i =>
    mk "smallOps(uint8,uint8,uint8,uint256)" [.int a, .int 255, .int 3, .int i] s!"{a} {i}") ++
  ([(0 : Int), 1, 31, 32, 33, 63, 64, 65, 100, 255].map fun n => mk "smallMany(uint8)" [.int n] s!"{n}") ++
  (U8.map fun a => mk "smallClear(uint8)" [.int a] s!"{a}") ++
  ([(0 : Int), 1, 2].flatMap fun r => [(0 : Int), 1, 2].flatMap fun c => [(0 : Int), 2 ^ 256 - 2, 2 ^ 256 - 1].map fun v =>
    mk "nestedOps(uint256,uint256,uint256)" [.int v, .int r, .int c] s!"{v} {r} {c}") ++
  (U128.flatMap fun x => U128.map fun y => mk "ptOps(uint128,uint128,uint256)" [.int x, .int y, .int 9] s!"{x} {y}") ++
  (U128.flatMap fun x => [(0 : Int), 2 ^ 256 - 1].map fun k => mk "ptPtr(uint256,uint128)" [.int k, .int x] s!"{k} {x}") ++
  (U128.flatMap fun x => [(0 : Int), 1, 2].map fun i => mk "ptsOps(uint128,uint128,uint256)" [.int x, .int 4, .int i] s!"{x} {i}") ++
  (U8.flatMap fun t => [true, false].flatMap fun ok => [(0 : Int), 2 ^ 64 - 1].map fun st =>
    mk "recOps(address,uint64,bool,uint256,uint8)" [A, .int st, .bool ok, .int (2 ^ 256 - 1), .int t] s!"{t} {ok} {st}") ++
  (U8.map fun t => mk "recClear(address,uint256,uint8)" [A, .int (2 ^ 256 - 1), .int t] s!"{t}") ++
  (U128.map fun x => mk "pointClear(uint256,uint128)" [.int 9, .int x] s!"{x}") ++
  ([(0 : Int), 1, 2, 10, 255].flatMap fun n => [mk "newArr(uint8)" [.int n] s!"{n}", mk "newBytes(uint8)" [.int n] s!"{n}"]) ++
  (U256.map fun v => mk "memAlias(uint256)" [.int v] s!"{v}") ++
  (U128.flatMap fun x => [mk "memStruct(uint128)" [.int x] s!"{x}", mk "memCopy(uint128)" [.int x] s!"{x}"]) ++
  ([0, 1, 31, 32, 33, 64, 100].flatMap fun n => [(0 : Int), 1, 30, 31, 32, 63, 99, 100].flatMap fun i =>
    [mk "blobOps(bytes,uint256)" [.bytes (bytesN n), .int i] s!"{n} {i}",
     mk "blobSet(bytes,uint256,bytes1)" [.bytes (bytesN n), .int i, b1 0xfe] s!"{n} {i}",
     mk "blobSet(bytes,uint256,bytes1)" [.bytes (bytesN n), .int i, b1 0] s!"{n} {i} zero"]) ++
  ([0, 1, 31, 32, 33, 100].flatMap fun n =>
    [mk "blobClear(bytes)" [.bytes (bytesN n)] s!"{n}", mk "textOps(string)" [str n] s!"{n}"]) ++
  ([(0 : Int), 4, 5, 2 ^ 256 - 1].map fun i => mk "fixedArr(uint256)" [.int i] s!"{i}")

def allocCases : List Case :=
  [(0 : Int), 1, 1000, 2 ^ 64, 2 ^ 255, 2 ^ 256 - 1].flatMap fun n =>
    [ { name := s!"newWords {n}", code := allocRuntime, call := some ("newWords(uint256)", [.int n]) },
      { name := s!"newBytes {n}", code := allocRuntime, call := some ("newBytes(uint256)", [.int n]) } ]

def scenario : Scenario :=
  { name := "Data", program := _root_.Data.SoliditySpec.program, target := "Data", cases := cases }

def scenarioBoundaries : Scenario :=
  { name := "Data/boundaries", program := _root_.Data.SoliditySpec.program, target := "Data", cases := boundaries }

def scenarioAlloc : Scenario :=
  { name := "Data/alloc", program := _root_.Data.SoliditySpec.allocProgram, target := "Alloc", cases := allocCases }

end Solidity.Test.Data
