import Solidity.Test.Harness
import Solidity.Test.Specs.Recv
import Solidity.Test.Fixtures.RecvSolc

/-! # Differential cases: `receive` and `fallback`.

One scenario per contract, all with the same raw calldata shapes: empty, shorter than a selector,
an unknown selector, a known selector with and without its argument; each with and without value. -/

namespace Solidity.Test.Recv

open Solidity.Test

def hex (s : String) : ByteArray := bytesOfHex s

/-- Calldata shapes (`f(uint256)` is `b3de648b`, `f()` is `26121ff0`, `g(uint256)` is `e420264a`). -/
def shapes : List (String × ByteArray) :=
  [ ("empty", .empty), ("1 byte", hex "00"), ("3 bytes", hex "b3de64"), ("unknown", hex "deadbeef"),
    ("unknown+word", hex "deadbeef" ++ wordBytes 7),
    ("f(uint256) no arg", hex "b3de648b"), ("f(uint256) 5", hex "b3de648b" ++ wordBytes 5),
    ("f(uint256) short arg", hex "b3de648b" ++ hex "0001"),
    ("f()", hex "26121ff0"), ("f() extra", hex "26121ff0" ++ wordBytes 9),
    ("g(uint256) no arg", hex "e420264a"), ("g(uint256) 5", hex "e420264a" ++ wordBytes 5),
    ("long", hex "01" ++ wordBytes 1 ++ wordBytes 2 ++ wordBytes 3) ]

def rawCases (code : ByteArray) : List Case :=
  shapes.flatMap fun (n, cd) => [0, 1, 7].map fun v =>
    { name := s!"{n} value {v}", code := code, calldata := cd, value := v, balance := v }

def getter (code : ByteArray) (sig : String) : Case := { name := sig, code := code, call := some (sig, []) }

def recvFbCreation : ByteArray := hex Fixtures.recvFbCreationHex
def recvFbRuntime : ByteArray := hex Fixtures.recvFbRuntimeHex
def fbOnlyRuntime : ByteArray := hex Fixtures.fbOnlyRuntimeHex
def fbDataRuntime : ByteArray := hex Fixtures.fbDataRuntimeHex
def recvOnlyRuntime : ByteArray := hex Fixtures.recvOnlyRuntimeHex
def noFbRuntime : ByteArray := hex Fixtures.noFbRuntimeHex

open _root_.Recv.SoliditySpec in
def scenarios : List Scenario :=
  [ { name := "RecvFb", program := programRecvFb, target := "RecvFb",
      cases := rawCases recvFbRuntime ++ [getter recvFbRuntime "got()", getter recvFbRuntime "fb()", getter recvFbRuntime "data()",
        { name := "constructor", code := recvFbCreation, ctorArgs := some ([], recvFbRuntime), expect := .success }] },
    { name := "FbOnly", program := programFbOnly, target := "FbOnly",
      cases := rawCases fbOnlyRuntime ++ [getter fbOnlyRuntime "fb()"] },
    { name := "FbData", program := programFbData, target := "FbData",
      cases := rawCases fbDataRuntime ++ [getter fbDataRuntime "n()",
        { name := "n at 255", code := fbDataRuntime, calldata := hex "aabb", refs := [(⟨"n", []⟩, 255)] },
        { name := "n at max", code := fbDataRuntime, calldata := hex "aabb", refs := [(⟨"n", []⟩, 2 ^ 256 - 1)] }] },
    { name := "RecvOnly", program := programRecvOnly, target := "RecvOnly",
      cases := rawCases recvOnlyRuntime ++ [getter recvOnlyRuntime "got()"] },
    { name := "NoFb", program := programNoFb, target := "NoFb", cases := rawCases noFbRuntime } ]

end Solidity.Test.Recv
