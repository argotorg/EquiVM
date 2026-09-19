import Solidity.Test.Harness
import Solidity.Test.Specs.StringStoreLite
import Solm.Examples.StringStoreLite.Bytecode
import Solidity.Test.Fixtures.StringStoreLiteSolc

/-! # Differential cases: StringStoreLite. -/

namespace Solidity.Test.StringStoreLite

open Solidity.Test

def str (s : String) : Solm.Value := .bytes s.toUTF8
def long40 : String := "0123456789012345678901234567890123456789"
def s31 : String := "0123456789012345678901234567890"
def s32 : String := "01234567890123456789012345678901"

/-- Short-form slot word: data left-aligned, `2·len` in the low byte. -/
def shortSlot (s : String) : Ethereum.UInt256 :=
  word ((natOfBytes s.toUTF8) <<< (8 * (32 - s.length)) + 2 * s.length)
/-- Long form: `2·len + 1` in slot 0, data at `keccak(0)`. -/
def dataBase : Nat := natOfBytes (ffi.KEC (wordBytes 0))
def longSlots (s : String) : List (Ethereum.UInt256 × Ethereum.UInt256) :=
  (word 0, word (2 * s.length + 1)) ::
    ((List.range ((s.length + 31) / 32)).map fun i =>
      let chunk := s.toUTF8.extract (32 * i) (32 * i + 32)
      (word (dataBase + i), word (natOfBytes chunk <<< (8 * (32 - chunk.size)))))
def short (s : String) : List (Ethereum.UInt256 × Ethereum.UInt256) := [(word 0, shortSlot s)]

def creation : ByteArray := bytesOfHex Fixtures.stringStoreLiteCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.stringStoreLiteRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := stringStoreLiteBytecode }

def cases : List Case :=
  [ rt "set-short" { call := some ("set(string)", [str "hello"]), expect := .success },
    rt "set-31" { call := some ("set(string)", [str s31]), expect := .success },
    rt "set-32" { call := some ("set(string)", [str s32]), expect := .success },
    rt "set-long" { call := some ("set(string)", [str long40]), expect := .success },
    rt "set-empty" { call := some ("set(string)", [str ""]), expect := .success },
    rt "set-short-over-long" { call := some ("set(string)", [str "hi"]), storage := longSlots long40,
                               expect := .success },
    rt "set-long-over-short" { call := some ("set(string)", [str long40]), storage := short "hello",
                               expect := .success },
    rt "set-empty-over-long" { call := some ("set(string)", [str ""]), storage := longSlots long40,
                               expect := .success },
    rt "set-long-over-longer" { call := some ("set(string)", [str s32]), storage := longSlots long40,
                                expect := .success },
    rt "clear-short" { call := some ("clearCurrent()", []), storage := short "hello", expect := .success },
    rt "clear-long" { call := some ("clearCurrent()", []), storage := longSlots long40, expect := .success },
    rt "clear-empty" { call := some ("clearCurrent()", []), expect := .success },
    rt "length-short" { call := some ("currentLength()", []), storage := short "hello", expect := .success },
    rt "length-long" { call := some ("currentLength()", []), storage := longSlots long40, expect := .success },
    rt "length-empty" { call := some ("currentLength()", []), expect := .success },
    rt "set-nonpayable" { call := some ("set(string)", [str "hello"]), value := 1, expect := .revert },
    rt "set-bad-offset" { calldata := selectorOfSig "set(string)" ++ wordBytes 0x1000 ++ wordBytes 0,
                          expect := .revert },
    rt "set-length-past-end" { calldata := selectorOfSig "set(string)" ++ wordBytes 0x20 ++ wordBytes 100 ++ wordBytes 0,
                               expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([], runtime), value := 1,
      expect := .revert } ]

def scenario : Scenario :=
  { name := "StringStoreLite", program := _root_.StringStoreLite.SoliditySpec.program, target := "StringStoreLite", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "StringStoreLite/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `stringStoreLiteInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "StringStoreLite/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) => some { c with code := stringStoreLiteInitcode, ctorArgs := some (args, stringStoreLiteBytecode), known := if c.name == "constructor-nonpayable" then some "minimal initcode has no callvalue guard" else none }
        | none => none }

end Solidity.Test.StringStoreLite
