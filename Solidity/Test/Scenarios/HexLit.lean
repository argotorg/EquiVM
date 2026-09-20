import Solidity.Test.Harness
import Solidity.Test.Specs.HexLit
import Solidity.Test.Fixtures.HexLitSolc

/-! # Differential cases: HexLit (number literals converting to `bytesN`). -/

namespace Solidity.Test.HexLit

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.hexLitCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.hexLitRuntimeHex

def b2 (hi lo : UInt8) : ABI.ABIValue := .fixedBytes ⟨1, by decide⟩ [hi, lo]

def rt (name : String) (c : Case) : Case := { c with name := name, code := runtime }

def cases : List Case :=
  [ rt "set" { call := some ("set()", []), expect := .success },
    rt "cmp-eq" { call := some ("cmp(bytes2)", [b2 0x12 0x34]), expect := .success },
    rt "cmp-ne" { call := some ("cmp(bytes2)", [b2 0x12 0x35]), expect := .success },
    rt "conv" { call := some ("conv()", []), expect := .success },
    rt "pass" { call := some ("pass()", []), expect := .success },
    rt "zero" { call := some ("zero()", []), expect := .success },
    rt "a" { call := some ("a()", []), expect := .success },
    rt "b" { call := some ("b()", []), expect := .success },
    rt "c" { call := some ("c()", []), expect := .success },
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def scenario : Scenario :=
  { name := "HexLit", program := _root_.HexLit.SoliditySpec.program, target := "HexLit", cases := cases }

end Solidity.Test.HexLit
