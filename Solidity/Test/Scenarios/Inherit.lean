import Solidity.Test.Harness
import Solidity.Test.Specs.Inherit
import Solidity.Test.Fixtures.InheritSolc

/-! # Differential cases: inheritance (the diamond `Diamond is Left, Right, IShape`).

`Inherit` holds the runtime cases (fuzzed) and the constructor; `Inherit/boundaries` runs the
functions and the constructor on boundary values. -/

namespace Solidity.Test.Inherit

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.diamondCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.diamondRuntimeHex

def MAX : Int := 2 ^ 256 - 1

/-- Storage as the constructor leaves it for `(x, y) = (3, 4)`, with `log` replaced by `lg`. -/
def st (lg : Nat) (a := 5) (l := 14) (r := 10) (d := 4) : List (Solm.EvaledStorageRef × Nat) :=
  [(⟨"a", []⟩, a), (⟨"log", []⟩, lg), (⟨"l", []⟩, l), (⟨"r", []⟩, r), (⟨"sides", []⟩, 4), (⟨"d", []⟩, d)]

def mk (sig : String) (args : List ABI.ABIValue) (tag : String := "") (lg : Nat := 0) : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args), refs := st lg }

def ctor (x y : Int) (value : Nat := 0) : Case :=
  { name := s!"constructor {x} {y} value {value}", code := creation, ctorArgs := some ([.int x, .int y], runtime),
    value := value, balance := value }

def cases : List Case :=
  [ mk "v()" [], mk "v()" [] "log 5" 5, mk "viaHook()" [], mk "tagged()" [] "" 3, mk "abs(uint256)" [.int 7],
    mk "area()" [], mk "sides()" [], mk "pick(uint256)" [.int 7], mk "pick(uint256,uint256)" [.int 7, .int 8],
    mk "pick(address)" [.address (addr 0xBEEF)], mk "picks(uint256)" [.int 7], mk "leftV()" [] "" 2,
    mk "state()" [] "" 1234, mk "a()" [], mk "l()" [], mk "r()" [], mk "d()" [], mk "log()" [] "" 9,
    { ctor 3 4 with expect := .success }, { ctor 0 0 with expect := .success } ]

def boundaries : List Case :=
  ([0, 1, 9, 10 ^ 70, (2 ^ 256 - 1) / 10 - 100, (2 ^ 256 - 1) / 10, (2 ^ 256 - 1) / 10 + 1, 2 ^ 256 - 1].flatMap fun lg =>
    [ mk "v()" [] s!"log {lg}" lg, mk "tagged()" [] s!"log {lg}" lg, mk "leftV()" [] s!"log {lg}" lg ]) ++
  ([(0 : Int), 1, 2 ^ 255, MAX].flatMap fun x =>
    [ mk "abs(uint256)" [.int x] s!"{x}", mk "pick(uint256)" [.int x] s!"{x}", mk "picks(uint256)" [.int x] s!"{x}",
      mk "pick(uint256,uint256)" [.int x, .int 1] s!"{x}" ]) ++
  ([0, 1, 2 ^ 128 - 1, 2 ^ 128, 2 ^ 256 - 1].map fun d =>
    { mk "area()" [] s!"d {d}" with refs := st 0 (d := d) }) ++
  ([(0 : Int), 1, 3, 2 ^ 256 - 14, 2 ^ 256 - 13, 2 ^ 256 - 3, 2 ^ 256 - 2, MAX].flatMap fun x =>
    [(0 : Int), 4, MAX].map fun y => ctor x y) ++
  [ctor 3 4 (value := 1)]

def scenario : Scenario :=
  { name := "Inherit", program := _root_.Inherit.SoliditySpec.program, target := "Diamond", cases := cases }

def scenarioBoundaries : Scenario :=
  { name := "Inherit/boundaries", program := _root_.Inherit.SoliditySpec.program, target := "Diamond", cases := boundaries }

end Solidity.Test.Inherit
