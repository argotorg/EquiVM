import Solidity.Test.Harness
import Solidity.Test.Specs.Libs
import Solidity.Test.Fixtures.LibsSolc

/-! # Differential cases: libraries.

`Libs` holds a few cases per function (the fuzzer mutates these); `Libs/boundaries` runs boundary
values and is not fuzzed. -/

namespace Solidity.Test.Libs

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.libsCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.libsRuntimeHex

def MAX : Int := 2 ^ 256 - 1
def WAD : Int := 10 ^ 18

def mk (sig : String) (args : List Solm.Value) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args) }

def arr (xs : List Int) : Solm.Value := .array (xs.map (.int ·))

def call1 (sig : String) (xs : List Int) : List Case := xs.map fun a => mk sig [.int a] s!"{a}"
def call2 (sig : String) (xs ys : List Int) : List Case :=
  xs.flatMap fun a => ys.map fun b => mk sig [.int a, .int b] s!"{a} {b}"

def cases : List Case :=
  [ mk "wmul(uint256,uint256)" [.int (3 * WAD), .int (2 * WAD)], mk "wmulU(uint256,uint256)" [.int (3 * WAD), .int 5],
    mk "clampU(uint256)" [.int 7], mk "clampU(uint256)" [.int 101] "too big",
    mk "accOps(uint256,uint256)" [.int 10, .int 4], mk "markIt(uint256)" [.int 9],
    mk "sumMem(uint256[])" [arr [3, 4, 5]], mk "sumMem(uint256[])" [arr []] "empty",
    mk "firstOf(uint256)" [.int 8], mk "firstEmpty()" [], mk "constShadow(uint256)" [.int 10],
    mk "chain(uint256)" [.int 7], mk "chain(uint256)" [.int 40] "too big",
    mk "sqs(uint256,uint256)" [.int 6, .int 7], mk "accMem(uint256)" [.int 9],
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def boundaries : List Case :=
  call2 "wmul(uint256,uint256)" [0, 1, WAD, 2 ^ 128, MAX] [0, 1, WAD, 2 ^ 128, MAX] ++
  call2 "wmulU(uint256,uint256)" [0, WAD, MAX] [0, WAD, MAX] ++
  call1 "clampU(uint256)" [0, 99, 100, 101, MAX] ++
  call2 "accOps(uint256,uint256)" [0, 1, 2 ^ 255, MAX] [0, 1, 2 ^ 255, MAX] ++
  call1 "markIt(uint256)" [0, 1, MAX] ++
  ([[], [0], [MAX], [1, 2, 3], [MAX, 1], [2 ^ 255, 2 ^ 255]].map fun xs => mk "sumMem(uint256[])" [arr xs] s!"{xs}") ++
  call1 "firstOf(uint256)" [0, 1, 2 ^ 256 - 2, MAX] ++
  call1 "chain(uint256)" [0, 1, 31, 32, 2 ^ 128, MAX] ++
  call2 "sqs(uint256,uint256)" [0, 1, 2 ^ 128 - 1, 2 ^ 128, MAX] [0, 1, 2, MAX] ++
  call1 "accMem(uint256)" [0, 1, 9, MAX] ++ call1 "constShadow(uint256)" [0, 3, MAX - 6, MAX - 5, MAX]

/-- The qualified forms `L.CONST` and `L.Struct(...)`. -/
def qualCases : List Case :=
  { name := "wad()", code := bytesOfHex Fixtures.libsQualRuntimeHex, call := some ("wad()", []), expect := .success } ::
  [(0 : Int), 1, 9, MAX].map fun a =>
    { name := s!"accLit(uint256) {a}", code := bytesOfHex Fixtures.libsQualRuntimeHex,
      call := some ("accLit(uint256)", [.int a]), expect := .success }

def scenario : Scenario :=
  { name := "Libs", program := _root_.Libs.SoliditySpec.program, target := "Libs", cases := cases }

def scenarioBoundaries : Scenario :=
  { name := "Libs/boundaries", program := _root_.Libs.SoliditySpec.program, target := "Libs", cases := boundaries }

def scenarioQual : Scenario :=
  { name := "Libs/qualified", program := _root_.Libs.SoliditySpec.qualProgram, target := "LibsQual", cases := qualCases }

end Solidity.Test.Libs
