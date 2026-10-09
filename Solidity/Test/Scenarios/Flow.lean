import Solidity.Test.Harness
import Solidity.Test.Specs.Flow
import Solidity.Test.Fixtures.FlowSolc

/-! # Differential cases: control flow.

`Flow` holds a few cases per function (the fuzzer mutates these); `Flow/boundaries` runs every
function on a matrix of boundary values and is not fuzzed. -/

namespace Solidity.Test.Flow

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.flowCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.flowRuntimeHex

def mk (sig : String) (args : List Solm.Value) (tag : String := "") : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args) }

/-- A case that starts with `counter = n`. -/
def mkC (n : Nat) (sig : String) (args : List Solm.Value) (tag : String := "") : Case :=
  { mk sig args tag with refs := [(⟨"counter", []⟩, n)] }

def arr (xs : List Int) : Solm.Value := .array (xs.map (.int ·))

def call1 (sig : String) (xs : List Int) : List Case := xs.map fun a => mk sig [.int a] s!"{a}"
def call2 (sig : String) (xs ys : List Int) : List Case :=
  xs.flatMap fun a => ys.map fun b => mk sig [.int a, .int b] s!"{a} {b}"
def callB2 (sig : String) : List Case :=
  [true, false].flatMap fun a => [true, false].map fun b => mk sig [.bool a, .bool b] s!"{a} {b}"

def MAX : Int := 2 ^ 256 - 1
def N8 : List Int := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 17, 31, 32, 33, 63, 64, 100, 254, 255]
def S8 : List Int := [0, 1, 2, 3, 4, 5, 9, 10, 255]
def ARRS : List (List Int) :=
  [[], [0], [1], [1, 0], [0, 1], [3, 9, 2, 9], [5, 6, 0, 7], [1, 2, 3], [MAX, 0], [7, MAX, 7]]

/-- A few cases per function. -/
def cases : List Case :=
  [ mk "ifChain(uint256)" [.int 5], mk "ifChain(uint256)" [.int 50], mk "ifChain(uint256)" [.int 100],
    mk "ifChain(uint256)" [.int 101],
    mk "ifNoElse(uint256,uint256)" [.int 7, .int 3], mk "ifNoElse(uint256,uint256)" [.int 3, .int 3],
    mk "ifNoElse(uint256,uint256)" [.int 3, .int 7],
    mk "ifDangling(bool,bool)" [.bool true, .bool true], mk "ifDangling(bool,bool)" [.bool true, .bool false],
    mk "ifDangling(bool,bool)" [.bool false, .bool true],
    mk "ifEffect(uint256,uint256)" [.int 0, .int 0], mk "ifEffect(uint256,uint256)" [.int 0, .int 5],
    mkC 3 "ifEffect(uint256,uint256)" [.int 5, .int 0],
    mk "shortCircuit(bool,bool)" [.bool true, .bool false], mkC 7 "shortCircuit(bool,bool)" [.bool false, .bool true],
    mk "ternNested(uint256)" [.int 5], mk "ternNested(uint256)" [.int 15], mk "ternNested(uint256)" [.int 25],
    mk "ternSide(bool)" [.bool true], mkC 4 "ternSide(bool)" [.bool false],
    mk "whileSum(uint8)" [.int 10], mk "whileBreak(uint8,uint8)" [.int 10, .int 4],
    mk "whileBreak(uint8,uint8)" [.int 4, .int 10], mk "whileContinue(uint8)" [.int 10],
    mk "whileCond(uint8)" [.int 5], mk "gcd(uint256,uint256)" [.int 48, .int 18], mk "collatz(uint16)" [.int 27],
    mk "scan(uint256[])" [arr [5, 6, 0, 7]], mk "scan(uint256[])" [arr [1, 2]],
    mk "doOnce(uint8)" [.int 0], mk "doOnce(uint8)" [.int 5], mk "doContinue(uint8)" [.int 7],
    mk "doBreak(uint8)" [.int 10], mk "doBreak(uint8)" [.int 2],
    mk "forSum(uint8)" [.int 10], mk "forContinue(uint8)" [.int 9], mk "forNoInit(uint8)" [.int 7],
    mk "forNoCond(uint8)" [.int 100], mk "forEmpty(uint8)" [.int 6], mk "forNested(uint8,uint8)" [.int 5, .int 6],
    mk "forReturn(uint8,uint8)" [.int 10, .int 4], mk "forReturn(uint8,uint8)" [.int 4, .int 10],
    mk "forTwoVars(uint8)" [.int 9], mk "loopRevert(uint8,uint8)" [.int 6, .int 9],
    mk "loopRevert(uint8,uint8)" [.int 6, .int 3], mk "emitLoop(uint8)" [.int 15], mk "forScope(uint8)" [.int 4],
    mk "maxOf(uint256[])" [arr [3, 9, 2, 9]], mk "findIn(uint256[],uint256)" [arr [4, 5, 6], .int 5],
    mk "findIn(uint256[],uint256)" [arr [4, 5, 6], .int 9],
    mk "uncheckedLoop(uint8)" [.int 20], mk "uncheckedWrap(uint8)" [.int 3], mk "uncheckedWrap(uint8)" [.int 1],
    mk "uncheckedBreak(uint8)" [.int 30], mk "uncheckedBreak(uint8)" [.int 200],
    mk "namedRet(uint256)" [.int 3], mk "namedRet(uint256)" [.int 9], mk "earlyRet(uint256)" [.int 0],
    mk "earlyRet(uint256)" [.int 1], mk "earlyRet(uint256)" [.int 2], mk "retVoid(uint256)" [.int 0],
    mk "retVoid(uint256)" [.int 1], mk "noRet(uint256)" [.int 3], mk "noRet(uint256)" [.int 9],
    mk "retTuple(uint256)" [.int 4], mk "retTuple(uint256)" [.int MAX],
    mk "req(uint256)" [.int 0], mk "req(uint256)" [.int 5], mk "req(uint256)" [.int 50], mk "req(uint256)" [.int 51],
    mk "req(uint256)" [.int 52], mk "req(uint256)" [.int 53], mk "req(uint256)" [.int 100],
    mk "factorial(uint8)" [.int 5], mk "factorial(uint8)" [.int 57], mk "factorial(uint8)" [.int 58],
    mk "fib(uint8)" [.int 15], mk "isEven(uint8)" [.int 7], mk "isEven(uint8)" [.int 8],
    mk "rep(uint8)" [.int 0], mk "rep(uint8)" [.int 1], mkC 5 "rep(uint8)" [.int 3],
    mk "withAfter(uint256)" [.int 0], mkC 5 "withAfter(uint256)" [.int 1],
    mk "withPost(uint256)" [.int 3], mk "withPost(uint256)" [.int 4], mkC 2 "withPost(uint256)" [.int 6],
    mk "skipped(bool)" [.bool true], mk "skipped(bool)" [.bool false],
    mk "decLoop(uint8)" [.int 5], mk "preDec(uint8)" [.int 5], mk "countdown(uint8)" [.int 3],
    mk "countdown(uint8)" [.int 200],
    mk "uncheckedRet(uint8)" [.int 100], mk "uncheckedLeak(uint8)" [.int 100], mk "uncheckedLeak(uint8)" [.int 10],
    mk "scanSafe(uint256[])" [arr [5, 6, 0, 7]], mk "scanSafe(uint256[])" [arr [1, 2]],
    mk "findPair(uint8)" [.int 12], mk "findPair(uint8)" [.int 7],
    mk "shadowFor(uint8)" [.int 4], mk "shadowAssign()" [], mk "shadowNested(uint256)" [.int 7],
    mk "shadowRet(uint256)" [.int 3], mk "shadowRet(uint256)" [.int 9], mk "shadowBreak(uint8)" [.int 6],
    mk "shadowParam(uint256)" [.int 5], mkC 2 "viaShadowMod(uint256)" [.int 30],
    { mk "stale()" [] with refs := [(⟨"total", []⟩, 3)] },
    mkC 9 "counter()" [], mk "total()" [], mk "hits(uint256)" [.int 1],
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def boundaries : List Case :=
  call1 "ifChain(uint256)" [0, 9, 10, 99, 100, 101, MAX] ++
  call2 "ifNoElse(uint256,uint256)" [0, 1, MAX] [0, 1, MAX] ++
  callB2 "ifDangling(bool,bool)" ++
  ([0, 1, 5, 2 ^ 256 - 2, 2 ^ 256 - 1].flatMap fun c => [(0 : Int), 1, 2, 3, 6, MAX].flatMap fun x =>
    [(0 : Int), 1, 2, 3, 7, MAX].map fun y => mkC c "ifEffect(uint256,uint256)" [.int x, .int y] s!"{c} {x} {y}") ++
  ([0, 1, 2 ^ 256 - 1].flatMap fun c => [true, false].flatMap fun a => [true, false].map fun b =>
    mkC c "shortCircuit(bool,bool)" [.bool a, .bool b] s!"{c} {a} {b}") ++
  call1 "ternNested(uint256)" [0, 9, 10, 19, 20, MAX] ++
  ([0, 1, 2 ^ 256 - 2, 2 ^ 256 - 1].flatMap fun c => [true, false].map fun b =>
    mkC c "ternSide(bool)" [.bool b] s!"{c} {b}") ++
  (["whileSum(uint8)", "whileContinue(uint8)", "whileCond(uint8)", "doOnce(uint8)", "doContinue(uint8)",
    "doBreak(uint8)", "forSum(uint8)", "forContinue(uint8)", "forNoInit(uint8)", "forNoCond(uint8)",
    "forEmpty(uint8)", "forTwoVars(uint8)", "forScope(uint8)", "emitLoop(uint8)", "uncheckedLoop(uint8)",
    "uncheckedWrap(uint8)", "uncheckedBreak(uint8)", "factorial(uint8)", "fib(uint8)", "isEven(uint8)",
    "decLoop(uint8)", "preDec(uint8)", "countdown(uint8)", "uncheckedRet(uint8)", "uncheckedLeak(uint8)",
    "findPair(uint8)"].flatMap fun sig => call1 sig N8) ++
  call1 "uncheckedLeak(uint8)" [55, 56, 155, 156, 211, 212] ++
  call2 "whileBreak(uint8,uint8)" S8 S8 ++
  call2 "forReturn(uint8,uint8)" S8 S8 ++
  call2 "forNested(uint8,uint8)" [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 255] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 255] ++
  call2 "loopRevert(uint8,uint8)" [0, 1, 5, 6, 255] [0, 1, 4, 5, 6, 254, 255] ++
  call2 "gcd(uint256,uint256)" [0, 1, 12, 18, 89, 144, 2 ^ 255, MAX] [0, 1, 12, 18, 89, 144, 2 ^ 255, MAX] ++
  call1 "collatz(uint16)" [0, 1, 2, 3, 6, 7, 27, 97, 871, 65535] ++
  (ARRS.flatMap fun xs =>
    [mk "scan(uint256[])" [arr xs] s!"{xs}", mk "scanSafe(uint256[])" [arr xs] s!"{xs}",
     mk "maxOf(uint256[])" [arr xs] s!"{xs}"] ++
    [(0 : Int), 1, 2, 9, MAX].map fun v => mk "findIn(uint256[],uint256)" [arr xs, .int v] s!"{xs} {v}") ++
  call1 "namedRet(uint256)" [0, 5, 6, MAX] ++
  call1 "earlyRet(uint256)" [0, 1, 2, 3, MAX] ++
  call1 "retVoid(uint256)" [0, 1] ++
  call1 "noRet(uint256)" [0, 5, 6, MAX] ++
  call1 "retTuple(uint256)" [0, 1, 2, 2 ^ 256 - 4, 2 ^ 256 - 3, 2 ^ 256 - 2, MAX] ++
  call1 "req(uint256)" [0, 1, 49, 50, 51, 52, 53, 54, 99, 100, MAX] ++
  ([0, 1, 5, 2 ^ 256 - 3, 2 ^ 256 - 1].flatMap fun c => [(0 : Int), 1, 2, 3, 4, 7, 255].map fun n =>
    mkC c "rep(uint8)" [.int n] s!"{c} {n}") ++
  ([0, 1, 2 ^ 256 - 101, 2 ^ 256 - 100, 2 ^ 256 - 1].flatMap fun c => [(0 : Int), 1, 2].map fun x =>
    mkC c "withAfter(uint256)" [.int x] s!"{c} {x}") ++
  ([0, 1, 2 ^ 256 - 3].flatMap fun c => [(0 : Int), 1, 3, 4, 5, MAX].map fun x =>
    mkC c "withPost(uint256)" [.int x] s!"{c} {x}") ++
  ([0, 7].flatMap fun c => [true, false].map fun b => mkC c "skipped(bool)" [.bool b] s!"{c} {b}") ++
  call1 "shadowFor(uint8)" N8 ++ call1 "shadowBreak(uint8)" N8 ++
  call1 "shadowNested(uint256)" [0, 1, MAX] ++
  call1 "shadowRet(uint256)" [0, 5, 6, 254, 255, 256, 511, MAX] ++
  call1 "shadowParam(uint256)" [0, 5, 2 ^ 256 - 2, MAX] ++
  ([0, 2, 2 ^ 256 - 6, 2 ^ 256 - 5].flatMap fun c => [(0 : Int), 30, MAX].map fun v =>
    mkC c "viaShadowMod(uint256)" [.int v] s!"{c} {v}") ++
  ([0, 3, 8, 2 ^ 256 - 1].map fun t => { mk "stale()" [] s!"{t}" with refs := [(⟨"total", []⟩, t)] })

def scenario : Scenario :=
  { name := "Flow", program := _root_.Flow.SoliditySpec.program, target := "Flow", cases := cases }

def scenarioBoundaries : Scenario :=
  { name := "Flow/boundaries", program := _root_.Flow.SoliditySpec.program, target := "Flow", cases := boundaries }

end Solidity.Test.Flow
