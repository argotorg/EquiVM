import Solidity.Test.Harness
import Solidity.Test.Specs.Arith
import Solidity.Test.Fixtures.ArithSolc

/-! # Differential cases: arithmetic and types.

`Arith` holds one case per function (the fuzzer mutates these); `Arith/boundaries` runs every
operator on a matrix of boundary values and is not fuzzed. -/

namespace Solidity.Test.Arith

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.arithCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.arithRuntimeHex

def mk (sig : String) (args : List ABI.ABIValue) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args) }

def b4 (n : Nat) : ABI.ABIValue := .fixedBytes ⟨3, by decide⟩ ((wordBytes n).toList.drop 28)
def b32 (n : Nat) : ABI.ABIValue := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

def call1 (sig : String) (xs : List Int) : List Case := xs.map fun a => mk sig [.int a] s!"{a}"
def call2 (sig : String) (xs ys : List Int) : List Case :=
  xs.flatMap fun a => ys.map fun b => mk sig [.int a, .int b] s!"{a} {b}"
def call3 (sig : String) (xs ys zs : List Int) : List Case :=
  xs.flatMap fun a => ys.flatMap fun b => zs.map fun c => mk sig [.int a, .int b, .int c] s!"{a} {b} {c}"

def I8 : List Int := [-128, -127, -2, -1, 0, 1, 2, 126, 127]
def I16 : List Int := [-32768, -1, 0, 1, 255, 32767]
def I256 : List Int := [-(2 ^ 255), -(2 ^ 255) + 1, -2, -1, 0, 1, 2, 2 ^ 255 - 2, 2 ^ 255 - 1]
def U8 : List Int := [0, 1, 2, 15, 16, 127, 128, 254, 255]
def U128 : List Int := [0, 1, 2 ^ 64, 2 ^ 127, 2 ^ 128 - 1]
def U256 : List Int := [0, 1, 2, 3, 255, 256, 2 ^ 128, 2 ^ 255, 2 ^ 256 - 2, 2 ^ 256 - 1]
def SH : List Int := [0, 1, 7, 8, 255, 256, 257, 2 ^ 255]
def SH8 : List Int := [0, 1, 7, 8, 255]
def EXPS : List Int := [0, 1, 2, 3, 8, 255, 256]
def MODS : List Int := [0, 1, 2, 7, 2 ^ 255, 2 ^ 256 - 1]
def B4 : List Nat := [0, 1, 0xff, 0x12345678, 0x80000000, 0xffffffff]

/-- One case per function. -/
def cases : List Case :=
  [ mk "addI8(int8,int8)" [.int 5, .int (-7)], mk "subI8(int8,int8)" [.int 5, .int 7], mk "mulI8(int8,int8)" [.int (-5), .int 7],
    mk "divI8(int8,int8)" [.int (-7), .int 2], mk "modI8(int8,int8)" [.int (-7), .int 2], mk "negI8(int8)" [.int 5],
    mk "cmpI8(int8,int8)" [.int (-1), .int 1],
    mk "addI(int256,int256)" [.int 5, .int (-7)], mk "subI(int256,int256)" [.int 5, .int 7],
    mk "mulI(int256,int256)" [.int (-5), .int 7], mk "divI(int256,int256)" [.int (-7), .int 2],
    mk "modI(int256,int256)" [.int (-7), .int 2], mk "negI(int256)" [.int 5], mk "cmpI(int256,int256)" [.int (-1), .int 1],
    mk "sarI(int256,uint256)" [.int (-16), .int 2], mk "shlI(int256,uint256)" [.int (-3), .int 2],
    mk "sarI8(int8,uint8)" [.int (-16), .int 2],
    mk "addU8(uint8,uint8)" [.int 5, .int 7], mk "subU8(uint8,uint8)" [.int 7, .int 5], mk "mulU8(uint8,uint8)" [.int 5, .int 7],
    mk "divU8(uint8,uint8)" [.int 7, .int 2], mk "modU8(uint8,uint8)" [.int 7, .int 2],
    mk "mulU128(uint128,uint128)" [.int 5, .int 7], mk "mixed(uint8,uint256)" [.int 5, .int 7],
    mk "mixedI(int8,int256)" [.int (-5), .int 7], mk "mulLit(uint8)" [.int 5],
    mk "shlU(uint256,uint256)" [.int 5, .int 3], mk "shrU(uint256,uint256)" [.int 500, .int 3],
    mk "shlU8(uint8,uint8)" [.int 5, .int 3], mk "shlLit(uint8)" [.int 9],
    mk "expU(uint256,uint256)" [.int 3, .int 5], mk "expU8(uint8,uint8)" [.int 3, .int 5],
    mk "expI(int256,uint256)" [.int (-3), .int 5], mk "expLit(uint8)" [.int 9],
    mk "modU(uint256,uint256)" [.int 17, .int 5], mk "divU(uint256,uint256)" [.int 17, .int 5],
    mk "addMod(uint256,uint256,uint256)" [.int 17, .int 5, .int 7], mk "mulMod(uint256,uint256,uint256)" [.int 17, .int 5, .int 7],
    mk "bitsU(uint256,uint256)" [.int 12, .int 10], mk "bitsI16(int16,int16)" [.int (-12), .int 10],
    mk "bitsB4(bytes4,bytes4)" [b4 0x12345678, b4 0x0f0f0f0f], mk "shiftB4(bytes4,uint8)" [b4 0x12345678, .int 4],
    mk "cmpB4(bytes4,bytes4)" [b4 0x12345678, b4 0x0f0f0f0f],
    mk "uAddU8(uint8,uint8)" [.int 250, .int 10], mk "uSubU8(uint8,uint8)" [.int 5, .int 7],
    mk "uMulI8(int8,int8)" [.int 100, .int 3], mk "uSubI8(int8,int8)" [.int (-100), .int 100],
    mk "uNegI(int256)" [.int 5], mk "uDivI(int256,int256)" [.int (-7), .int 2],
    mk "uMulU(uint256,uint256)" [.int (2 ^ 200), .int (2 ^ 100)], mk "uExpU(uint256,uint256)" [.int 3, .int 500],
    mk "compound(uint256,uint256)" [.int 17, .int 5], mk "compoundI(int256,int256)" [.int 17, .int (-5)],
    mk "incs(uint8)" [.int 5], mk "uIncs(uint8)" [.int 255],
    mk "conv(uint256)" [.int 0x1234567890], mk "convI(int256)" [.int (-300)], mk "widen(int8,uint8)" [.int (-5), .int 200],
    mk "signFlip(uint8,int8)" [.int 200, .int (-5)], mk "convB(bytes32)" [b32 (0x12345678 * 2 ^ 224 + 7)],
    mk "convB4(bytes4)" [b4 0x12345678],
    mk "toEnum(uint8)" [.int 2], mk "fromEnum(uint8)" [.int 1], mk "cmpEnum(uint8,uint8)" [.int 1, .int 2],
    mk "limits()" [],
    mk "tern(uint256,uint256)" [.int 5, .int 7], mk "ternMixed(bool,uint8,uint256)" [.bool true, .int 5, .int 7],
    mk "asgNarrow()" [], mk "asgWide(uint8)" [.int 5], mk "asgChain(uint8)" [.int 5], mk "asgStore(uint8)" [.int 5],
    mk "asgStore8(uint256)" [.int 5], mk "asgLit()" [],
    mk "arrFirst(uint8)" [.int 0], mk "arrCommon(uint8)" [.int 1], mk "arrTyped(uint8,uint16,uint8)" [.int 5, .int 7, .int 1],
    mk "arrLitTyped(uint8,uint8)" [.int 5, .int 0],
    mk "condSame(bool,uint8,uint8)" [.bool true, .int 5, .int 7], mk "condArg(bool,uint256,uint256)" [.bool true, .int 5, .int 7],
    mk "condLit(bool,uint256)" [.bool false, .int 5], mk "condExplicit(bool,uint8,uint256)" [.bool true, .int 255, .int 7],
    mk "condPacked(bool,uint8,uint8)" [.bool true, .int 5, .int 7],
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

/-- Every operator on a matrix of boundary values. -/
def boundaries : List Case :=
  (["addI8(int8,int8)", "subI8(int8,int8)", "mulI8(int8,int8)", "divI8(int8,int8)", "modI8(int8,int8)",
    "cmpI8(int8,int8)", "uMulI8(int8,int8)", "uSubI8(int8,int8)"].flatMap fun s => call2 s I8 I8) ++
  call1 "negI8(int8)" I8 ++
  (["addI(int256,int256)", "subI(int256,int256)", "mulI(int256,int256)", "divI(int256,int256)",
    "modI(int256,int256)", "cmpI(int256,int256)", "uDivI(int256,int256)", "compoundI(int256,int256)"].flatMap fun s =>
      call2 s I256 I256) ++
  call1 "negI(int256)" I256 ++ call1 "uNegI(int256)" I256 ++ call1 "convI(int256)" I256 ++
  call2 "sarI(int256,uint256)" I256 SH ++ call2 "shlI(int256,uint256)" I256 SH ++ call2 "sarI8(int8,uint8)" I8 SH8 ++
  (["addU8(uint8,uint8)", "subU8(uint8,uint8)", "mulU8(uint8,uint8)", "divU8(uint8,uint8)", "modU8(uint8,uint8)",
    "uAddU8(uint8,uint8)", "uSubU8(uint8,uint8)", "expU8(uint8,uint8)", "shlU8(uint8,uint8)"].flatMap fun s =>
      call2 s U8 U8) ++
  call2 "mulU128(uint128,uint128)" U128 U128 ++ call2 "mixed(uint8,uint256)" U8 U256 ++
  call2 "mixedI(int8,int256)" I8 I256 ++ call1 "mulLit(uint8)" U8 ++ call1 "shlLit(uint8)" U8 ++
  call1 "expLit(uint8)" U8 ++ call1 "incs(uint8)" U8 ++ call1 "uIncs(uint8)" U8 ++
  call2 "shlU(uint256,uint256)" U256 SH ++ call2 "shrU(uint256,uint256)" U256 SH ++
  call2 "expU(uint256,uint256)" U256 EXPS ++ call2 "uExpU(uint256,uint256)" U256 EXPS ++
  call2 "expI(int256,uint256)" I256 EXPS ++
  (["modU(uint256,uint256)", "divU(uint256,uint256)", "bitsU(uint256,uint256)", "uMulU(uint256,uint256)",
    "compound(uint256,uint256)", "tern(uint256,uint256)"].flatMap fun s => call2 s U256 U256) ++
  call3 "addMod(uint256,uint256,uint256)" U256 U256 MODS ++ call3 "mulMod(uint256,uint256,uint256)" U256 U256 MODS ++
  call2 "bitsI16(int16,int16)" I16 I16 ++
  (B4.flatMap fun a => B4.map fun b => mk "bitsB4(bytes4,bytes4)" [b4 a, b4 b] s!"{a} {b}") ++
  (B4.flatMap fun a => B4.map fun b => mk "cmpB4(bytes4,bytes4)" [b4 a, b4 b] s!"{a} {b}") ++
  (B4.flatMap fun a => [0, 1, 4, 8, 31, 32, 33, 255].map fun s => mk "shiftB4(bytes4,uint8)" [b4 a, .int s] s!"{a} {s}") ++
  (B4.map fun a => mk "convB4(bytes4)" [b4 a] s!"{a}") ++
  ([0, 1, 2 ^ 255, 2 ^ 256 - 1, 0x12345678 * 2 ^ 224 + 7].map fun a => mk "convB(bytes32)" [b32 a] s!"{a}") ++
  call1 "conv(uint256)" (U256 ++ [127, 128, 2 ^ 160 - 1, 2 ^ 160, 65535, 65536]) ++
  call2 "widen(int8,uint8)" I8 U8 ++ call2 "signFlip(uint8,int8)" U8 I8 ++
  call1 "toEnum(uint8)" [0, 1, 2, 3, 4, 255] ++ call1 "fromEnum(uint8)" [0, 1, 2, 3] ++
  call2 "cmpEnum(uint8,uint8)" [0, 1, 2, 3] [0, 1, 2] ++
  ([true, false].flatMap fun c => U8.flatMap fun a => [(0 : Int), 255, 2 ^ 256 - 1].flatMap fun b =>
    [mk "ternMixed(bool,uint8,uint256)" [.bool c, .int a, .int b] s!"{c} {a} {b}",
     mk "condExplicit(bool,uint8,uint256)" [.bool c, .int a, .int b] s!"{c} {a} {b}"]) ++
  ([true, false].flatMap fun c => U8.flatMap fun a => U8.flatMap fun b =>
    [mk "condSame(bool,uint8,uint8)" [.bool c, .int a, .int b] s!"{c} {a} {b}",
     mk "condPacked(bool,uint8,uint8)" [.bool c, .int a, .int b] s!"{c} {a} {b}"]) ++
  ([true, false].flatMap fun c => U256.flatMap fun a =>
    [mk "condLit(bool,uint256)" [.bool c, .int a] s!"{c} {a}",
     mk "condArg(bool,uint256,uint256)" [.bool c, .int a, .int 3] s!"{c} {a}"]) ++
  call1 "asgWide(uint8)" U8 ++ call1 "asgChain(uint8)" U8 ++ call1 "asgStore(uint8)" U8 ++
  call1 "asgStore8(uint256)" U256 ++ [mk "asgNarrow()" [], mk "asgLit()" []] ++
  call1 "arrFirst(uint8)" [0, 1, 2, 3] ++ call1 "arrCommon(uint8)" [0, 1, 2] ++
  call3 "arrTyped(uint8,uint16,uint8)" U8 [0, 1, 218, 219, 300, 65535] [0, 1, 2] ++
  call2 "arrLitTyped(uint8,uint8)" U8 [0, 1, 2]

def scenario : Scenario :=
  { name := "Arith", program := _root_.Arith.SoliditySpec.program, target := "Arith", cases := cases }

def scenarioBoundaries : Scenario :=
  { name := "Arith/boundaries", program := _root_.Arith.SoliditySpec.program, target := "Arith", cases := boundaries }

/-! ## The documented deviation: conditionals with differently typed branches

solc gives `c ? a : b` the common type of both branches; the spec language has no static types and
uses the type of the branch taken.  The spec must state the conversion (`c ? uint256(a) : b`). -/

def condRuntime : ByteArray := bytesOfHex Fixtures.condRuntimeHex

def mkCond (sig : String) (args : List ABI.ABIValue) (tag : String) (known : Bool) : Case :=
  { name := s!"{sig} {tag}", code := condRuntime, call := some (sig, args),
    known := if known then some "conditional typed by the branch taken, not the common type" else none }

def condCases : List Case :=
  ([true, false].flatMap fun c => [(0 : Int), 5, 255].flatMap fun a => [(0 : Int), 7, 2 ^ 256 - 1].map fun b =>
    mkCond "ternArith(bool,uint8,uint256)" [.bool c, .int a, .int b] s!"{c} {a} {b}" (c && a == 255)) ++
  [true, false].map fun c => mkCond "condTwoLits(bool)" [.bool c] s!"{c}" c

def scenarioCond : Scenario :=
  { name := "Conditional/deviation", program := _root_.Arith.SoliditySpec.condProgram, target := "Cond", cases := condCases }

end Solidity.Test.Arith
