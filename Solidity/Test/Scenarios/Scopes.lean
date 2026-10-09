import Solidity.Test.Harness
import Solidity.Test.Specs.Scopes
import Solidity.Test.Fixtures.ScopesSolc

/-! # Differential cases: name scopes.

`Scopes`: one name at file level, in two libraries and in the contract; calls between functions of
one library; qualified names; three enums with one name (ranges, encoding, `using for`, overloads);
`using for` and a modifier inside a library.
`PTop`: a private variable name used in a base and a derived contract, initializers and base
constructor arguments in the scope of their contract.  `STop`: structs, enums, constants, errors,
events and functions named through a base, an interface and an unrelated contract. -/

namespace Solidity.Test.Scopes

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.scopesCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.scopesRuntimeHex
def topCreation : ByteArray := bytesOfHex Fixtures.pTopCreationHex
def topRuntime : ByteArray := bytesOfHex Fixtures.pTopRuntimeHex

def MAX : Int := 2 ^ 256 - 1

def mk (sig : String) (args : List Solm.Value) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args) }

def call1 (sig : String) (xs : List Int) : List Case := xs.map fun a => mk sig [.int a] s!"{a}"

def cases : List Case :=
  [ { mk "consts()" [] with expect := .success }, { mk "runs(uint256)" [.int 5] with expect := .success },
    { mk "viaUsing(uint256)" [.int 5] with expect := .success },
    { mk "mods(uint256)" [.int 50] "50" with expect := .success }, { mk "mods(uint256)" [.int 150] "150" with expect := .revert },
    { mk "mods(uint256)" [.int 1000] "1000" with expect := .revert },
    { mk "infoOps(uint128)" [.int 9] with expect := .success },
    { mk "fails(uint8)" [.int 0] with expect := .revert }, { mk "fails(uint8)" [.int 1] with expect := .revert },
    { mk "fails(uint8)" [.int 2] with expect := .revert }, { mk "fails(uint8)" [.int 3] with expect := .success },
    { mk "notes(uint256)" [.int 7] with expect := .success },
    { mk "modes(uint8)" [.int 0] with expect := .success }, { mk "modes(uint8)" [.int 1] with expect := .success },
    { mk "modes(uint8)" [.int 2] with expect := .revert }, mk "ia()" [], mk "ib()" [],
    { mk "enumPick()" [] with expect := .success },
    { mk "enumConv(uint8,uint8)" [.int 0, .int 1] "0 1" with expect := .success },
    { mk "enumConv(uint8,uint8)" [.int 0, .int 2] "0 2" with expect := .revert },
    { mk "enumConv(uint8,uint8)" [.int 1, .int 2] "1 2" with expect := .success },
    { mk "enumConv(uint8,uint8)" [.int 1, .int 3] "1 3" with expect := .revert },
    { mk "enumConv(uint8,uint8)" [.int 2, .int 3] "2 3" with expect := .success },
    { mk "enumConv(uint8,uint8)" [.int 2, .int 4] "2 4" with expect := .revert },
    { mk "enumEnc(uint8)" [.int 0] "0" with expect := .success }, { mk "enumEnc(uint8)" [.int 1] "1" with expect := .success },
    { mk "enumEnc(uint8)" [.int 2] "2" with expect := .revert },
    { mk "enumUsing(uint8)" [.int 0] "0" with expect := .success }, { mk "enumUsing(uint8)" [.int 5] "5" with expect := .success },
    mk "mb()" [],
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def boundaries : List Case :=
  call1 "runs(uint256)" [0, 1, MAX / 5 - 1000, MAX / 5 - 999, MAX / 3 - 100, MAX / 3 - 99, MAX - 1000, MAX - 7, MAX - 6, MAX - 3, MAX - 2, MAX] ++
  call1 "infoOps(uint128)" [0, 1, 2 ^ 128 - 2, 2 ^ 128 - 1] ++
  call1 "fails(uint8)" [0, 1, 2, 3, 255] ++ call1 "notes(uint256)" [0, MAX - 1, MAX] ++
  call1 "modes(uint8)" [0, 1, 2, 255] ++
  ([(0 : Int), 1, 2].flatMap fun k => [(0 : Int), 1, 2, 3, 4, 255].map fun m =>
    mk "enumConv(uint8,uint8)" [.int k, .int m] s!"{k} {m}") ++
  call1 "enumEnc(uint8)" [0, 1, 2, 255] ++ call1 "enumUsing(uint8)" [0, 1, 2, 3, 4, 5, 254, 255] ++
  call1 "viaUsing(uint256)" [0, 1, MAX / 3 - 100, MAX / 3 - 99, MAX / 4 - 325, MAX / 4 - 324, MAX - 1000, MAX] ++
  call1 "mods(uint256)" [0, 1, 99, 100, 101, 999, 1000, MAX]

/-- Storage of `PTop` as its constructor leaves it for `(a, mid) = (3, 9)`: `PBase.x`, `shared`,
    `PMid.x`, `mid`, `top`, `derivedInit`. -/
def topRefs : List (Solm.EvaledStorageRef × Nat) :=
  [(⟨"PBase.x", []⟩, 9), (⟨"shared", []⟩, 10), (⟨"PMid.x", []⟩, 6), (⟨"mid", []⟩, 15), (⟨"top", []⟩, 9),
   (⟨"derivedInit", []⟩, 16)]

def mkT (sig : String) : Case := { name := sig, code := topRuntime, call := some (sig, []), refs := topRefs }

def ctor (a mid : Int) (value : Nat := 0) : Case :=
  { name := s!"constructor {a} {mid} value {value}", code := topCreation,
    ctorArgs := some ([.int a, .int mid], topRuntime), value := value, balance := value }

def topCases : List Case :=
  [ { mkT "both()" with expect := .success }, mkT "baseF()", mkT "midF()", mkT "mid()", mkT "top()", mkT "derivedInit()",
    { ctor 3 9 with expect := .success }, ctor 0 0, ctor (MAX - 1) 1, ctor MAX 1, ctor (MAX / 2) 5, ctor (MAX / 2 + 1) 5,
    ctor 3 9 (value := 1) ]

/-- The state variable initializers run before base constructor arguments are evaluated (`got = 6`). -/
def orderCases : List Case :=
  [ { name := "constructor", code := bytesOfHex Fixtures.qTopCreationHex,
      ctorArgs := some ([], bytesOfHex Fixtures.qTopRuntimeHex), expect := .success } ]

/-- Base constructor arguments are all evaluated before any constructor body runs. -/
def nestCases : List Case :=
  [(0 : Int), 5, MAX].map fun k =>
    { name := s!"constructor {k}", code := bytesOfHex Fixtures.rTopCreationHex,
      ctorArgs := some ([.int k], bytesOfHex Fixtures.rTopRuntimeHex) }

def qualRuntime : ByteArray := bytesOfHex Fixtures.sTopRuntimeHex

def mkQ (sig : String) (args : List Solm.Value) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := qualRuntime, call := some (sig, args), refs := [(⟨"bx", []⟩, 4)] }

def qualCases : List Case :=
  [ { mkQ "items(uint128,uint8)" [.int 9, .int 0] "9 0" with expect := .success },
    { mkQ "items(uint128,uint8)" [.int 9, .int 2] "9 2" with expect := .success },
    { mkQ "items(uint128,uint8)" [.int 9, .int 3] "9 3" with expect := .revert },
    { mkQ "calls(uint256)" [.int 5] with expect := .success },
    { mkQ "errs(uint8)" [.int 0] "0" with expect := .revert }, { mkQ "errs(uint8)" [.int 1] "1" with expect := .revert },
    { mkQ "errs(uint8)" [.int 2] "2" with expect := .revert }, { mkQ "errs(uint8)" [.int 3] "3" with expect := .revert },
    { mkQ "errs(uint8)" [.int 4] "4" with expect := .success },
    mkQ "bx()" [], mkQ "stored()" [], mkQ "kind()" [], mkQ "ikind()" [],
    { name := "constructor", code := bytesOfHex Fixtures.sTopCreationHex, ctorArgs := some ([], qualRuntime),
      expect := .success } ]

def qualBoundaries : List Case :=
  ([(0 : Int), 1, 2, 3, 2 ^ 128 - 1].flatMap fun v => [(0 : Int), 1, 2, 3, 255].map fun m =>
    mkQ "items(uint128,uint8)" [.int v, .int m] s!"{v} {m}") ++
  ([(0 : Int), 1, MAX / 3, MAX / 3 + 1, MAX / 2, MAX / 2 + 1, MAX].map fun v => mkQ "calls(uint256)" [.int v] s!"{v}") ++
  ([(0 : Int), 1, 2, 3, 4, 5, 253, 254, 255].map fun k => mkQ "errs(uint8)" [.int k] s!"{k}")

def scenario : Scenario :=
  { name := "Scopes", program := _root_.Scopes.SoliditySpec.program, target := "Scopes", cases := cases }

def scenarioBoundaries : Scenario :=
  { name := "Scopes/boundaries", program := _root_.Scopes.SoliditySpec.program, target := "Scopes", cases := boundaries }

def scenarioTop : Scenario :=
  { name := "PTop", program := _root_.Scopes.SoliditySpec.inheritProgram, target := "PTop", cases := topCases }

def scenarioOrder : Scenario :=
  { name := "QTop", program := _root_.Scopes.SoliditySpec.orderProgram, target := "QTop", cases := orderCases }

def scenarioNest : Scenario :=
  { name := "RTop", program := _root_.Scopes.SoliditySpec.nestProgram, target := "RTop", cases := nestCases }

def scenarioQual : Scenario :=
  { name := "STop", program := _root_.Scopes.SoliditySpec.qualProgram, target := "STop", cases := qualCases }

def scenarioQualBoundaries : Scenario :=
  { name := "STop/boundaries", program := _root_.Scopes.SoliditySpec.qualProgram, target := "STop",
    cases := qualBoundaries }

end Solidity.Test.Scopes
