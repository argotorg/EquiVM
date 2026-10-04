import Solidity.Test.Harness
import Solidity.Test.Specs.Calls
import Solidity.Test.Fixtures.CallsSolc

/-! # Differential cases: external calls, low-level calls, ether transfers.

`Calls` holds a few cases per function (the fuzzer mutates these); `Calls/boundaries` runs every
call form against every kind of receiver and is not fuzzed. -/

namespace Solidity.Test.Calls

open Solidity.Test

def creation : ByteArray := bytesOfHex Fixtures.callsCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.callsRuntimeHex

/-- Receivers: `T` the full callee, `S` accepts ether, `G` needs more than the stipend to accept it,
    `N` has no `receive`, `R` rejects ether with a message, `E` has no code. -/
def T : Nat := 0x7A26E7
def S : Nat := 0x51C4
def G : Nat := 0x62EED
def N : Nat := 0x402EC
def R : Nat := 0x2E1EC7
def E : Nat := 0xE0A

def others : List (EVM.Address × Ethereum.Account) :=
  [ (addr T, account (balance := 2) (code := bytesOfHex Fixtures.callsTargetRuntimeHex) (storage := [(⟨0⟩, ⟨5⟩)])),
    (addr S, account (code := bytesOfHex Fixtures.callsSinkRuntimeHex)),
    (addr G, account (code := bytesOfHex Fixtures.callsGreedyRuntimeHex)),
    (addr N, account (code := bytesOfHex Fixtures.callsNoRecvRuntimeHex)),
    (addr R, account (code := bytesOfHex Fixtures.callsRejecterRuntimeHex)) ]

def a (n : Nat) : ABI.ABIValue := .address (addr n)
def MAX : Int := 2 ^ 256 - 1

/-- A call with `value` wei on a contract that already held `funds` wei (the harness starts at the
    code, so the balance includes the value). -/
def mk (sig : String) (args : List ABI.ABIValue) (tag : String := "") (value : Nat := 0) (funds : Nat := 0) : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args), accounts := others, value := value,
    balance := funds + value }

def ok (c : Case) : Case := { c with expect := .success }
def rv (c : Case) : Case := { c with expect := .revert }

/-- A case that starts with `last = l` and `pokes = p`. -/
def mkS (l p : Nat) (c : Case) : Case := { c with refs := [(⟨"last", []⟩, l), (⟨"pokes", []⟩, p)] }

def receivers : List (String × Nat) := [("T", T), ("S", S), ("G", G), ("N", N), ("R", R), ("E", E)]

/-- A few cases per function. -/
def cases : List Case :=
  [ ok (mk "callSet(address,uint256)" [a T, .int 9]), rv (mk "callSet(address,uint256)" [a E, .int 9] "eoa"),
    ok (mk "callPay(address,uint256)" [a T, .int 5] "ok" (value := 10)),
    rv (mk "callPay(address,uint256)" [a T, .int 50] "insufficient" (value := 10)),
    rv (mk "callPay(address,uint256)" [a S, .int 1] "no such function" (value := 10)),
    ok (mk "callGas(address,uint256)" [a T, .int 100000]), rv (mk "callGas(address,uint256)" [a T, .int 100] "too little"),
    mk "callMulti(address,uint256)" [a T, .int 4], mk "callMultiPick(address,uint256)" [a T, .int 4],
    mk "callMultiPick(address,uint256)" [a T, .int 5], mk "callStr(address,uint256)" [a T, .int 5],
    mk "callStr(address,uint256)" [a T, .int 40], mk "callArr(address,uint256)" [a T, .int 5],
    mk "callArr(address,uint256)" [a T, .int 8], mk "callPoint(address,uint128)" [a T, .int 9],
    mk "callSumPoint(address,uint128,uint128)" [a T, .int 3, .int 4],
    rv (mk "callFail(address,uint8)" [a T, .int 0]), rv (mk "callFail(address,uint8)" [a T, .int 1]),
    rv (mk "callFail(address,uint8)" [a T, .int 2]), rv (mk "callFail(address,uint8)" [a T, .int 3]),
    rv (mk "callFail(address,uint8)" [a T, .int 4]), rv (mk "callFail(address,uint8)" [a T, .int 5]),
    ok (mk "callFail(address,uint8)" [a T, .int 6]),
    ok (mk "callPing(address)" [a T]), rv (mk "callPing(address)" [a E] "eoa"),
    ok (mk "callBack(address,uint256)" [a T, .int 5]), rv (mk "callBack(address,uint256)" [a T, .int MAX] "overflow"),
    mk "who(address)" [a T], mkS 7 3 (mk "selfPoke(uint256)" [.int 3]), mkS 7 3 (mk "selfView()" []),
    mk "poke(uint256)" [.int 4],
    ok (mk "lowCall(address,uint256)" [a T, .int 9]), ok (mk "lowCall(address,uint256)" [a E, .int 9] "eoa"),
    ok (mk "lowCallDecode(address,uint256)" [a T, .int 9]), rv (mk "lowCallDecode(address,uint256)" [a E, .int 9] "eoa"),
    mk "lowValue(address,uint256)" [a S, .int 3] "sink" (value := 5),
    ok (mk "lowValue(address,uint256)" [a G, .int 3] "greedy" (value := 5)),
    ok (mk "lowValue(address,uint256)" [a N, .int 3] "no receive" (value := 5)),
    mk "lowValue(address,uint256)" [a R, .int 3] "rejecter" (value := 5),
    mk "lowValue(address,uint256)" [a E, .int 3] "eoa" (value := 5),
    mk "lowValue(address,uint256)" [a S, .int 50] "insufficient" (value := 5),
    mk "lowFail(address)" [a T], mk "lowStatic(address)" [a T], mk "lowStaticWrite(address)" [a T],
    mkS 1 0 (mk "lowDelegate(address,uint256)" [a T, .int 77]), mk "lowUnknown(address)" [a T],
    rv (mk "lowBubble(address)" [a T]),
    ok (mk "doTransfer(address,uint256)" [a S, .int 3] "sink" (value := 5)),
    rv (mk "doTransfer(address,uint256)" [a G, .int 3] "greedy" (value := 5)),
    rv (mk "doTransfer(address,uint256)" [a N, .int 3] "no receive" (value := 5)),
    rv (mk "doTransfer(address,uint256)" [a R, .int 3] "rejecter" (value := 5)),
    ok (mk "doTransfer(address,uint256)" [a E, .int 3] "eoa" (value := 5)),
    ok (mk "doTransfer(address,uint256)" [a S, .int 0] "zero"),
    rv (mk "doTransfer(address,uint256)" [a S, .int 50] "insufficient" (value := 5)),
    mk "doSend(address,uint256)" [a S, .int 3] "sink" (value := 5),
    ok (mk "doSend(address,uint256)" [a G, .int 3] "greedy" (value := 5)),
    mk "doSend(address,uint256)" [a N, .int 3] "no receive" (value := 5),
    mk "doSend(address,uint256)" [a R, .int 3] "rejecter" (value := 5),
    mk "doSend(address,uint256)" [a E, .int 3] "eoa" (value := 5),
    ok (mk "doSend(address,uint256)" [a S, .int 50] "insufficient" (value := 5)),
    mk "balances(address)" [a T] "" (funds := 9),
    { name := "receive", code := runtime, accounts := others, value := 3, balance := 3, expect := .success },
    { name := "receive-no-value", code := runtime, accounts := others },
    mkS 7 3 (mk "last()" []), mkS 7 3 (mk "pokes()" []),
    { name := "constructor", code := creation, ctorArgs := some ([], runtime), expect := .success } ]

def boundaries : List Case :=
  (receivers.flatMap fun (rn, r) => [(0 : Int), 1, 5, 6].flatMap fun v => [0, 1].flatMap fun bal =>
    [ mk "doTransfer(address,uint256)" [a r, .int v] s!"{rn} {v} {bal}" (value := 5) (funds := bal),
      mk "doSend(address,uint256)" [a r, .int v] s!"{rn} {v} {bal}" (value := 5) (funds := bal),
      mk "lowValue(address,uint256)" [a r, .int v] s!"{rn} {v} {bal}" (value := 5) (funds := bal),
      mk "callPay(address,uint256)" [a r, .int v] s!"{rn} {v} {bal}" (value := 5) (funds := bal) ]) ++
  (receivers.flatMap fun (rn, r) =>
    ([(0 : Int), 1, 2, 3, 4, 5, 6, 255].map fun k => mk "callFail(address,uint8)" [a r, .int k] s!"{rn} {k}") ++
    [ mk "callSet(address,uint256)" [a r, .int 9] rn, mk "callMulti(address,uint256)" [a r, .int 4] rn,
      mk "callStr(address,uint256)" [a r, .int 5] rn, mk "callArr(address,uint256)" [a r, .int 5] rn,
      mk "callPoint(address,uint128)" [a r, .int 9] rn, mk "callPing(address)" [a r] rn,
      mk "callBack(address,uint256)" [a r, .int 5] rn, mk "who(address)" [a r] rn,
      mk "lowCall(address,uint256)" [a r, .int 9] rn, mk "lowCallDecode(address,uint256)" [a r, .int 9] rn,
      mk "lowFail(address)" [a r] rn, mk "lowStatic(address)" [a r] rn, mk "lowStaticWrite(address)" [a r] rn,
      mk "lowDelegate(address,uint256)" [a r, .int 77] rn, mk "lowUnknown(address)" [a r] rn,
      mk "lowBubble(address)" [a r] rn, mk "balances(address)" [a r] rn (funds := 4) ]) ++
  ([(0 : Int), 1, 100, 2300, 5000, 21000, 22000, 23000, 25000, 30000, 100000, 2 ^ 64, MAX].map fun g =>
    mk "callGas(address,uint256)" [a T, .int g] s!"{g}") ++
  ([(0 : Int), 1, 31, 32, 33, 63, 64, 65, 69, 70, MAX].map fun n => mk "callStr(address,uint256)" [a T, .int n] s!"{n}") ++
  ([(0 : Int), 1, 2, 7, 8, 9, MAX].map fun n => mk "callArr(address,uint256)" [a T, .int n] s!"{n}") ++
  ([(0 : Int), 1, 2, 2 ^ 256 - 2, MAX].flatMap fun v =>
    [ mk "callMulti(address,uint256)" [a T, .int v] s!"{v}", mk "callMultiPick(address,uint256)" [a T, .int v] s!"{v}",
      mk "callSet(address,uint256)" [a T, .int v] s!"{v}", mk "lowCallDecode(address,uint256)" [a T, .int v] s!"{v}",
      mk "lowDelegate(address,uint256)" [a T, .int v] s!"{v}" ]) ++
  ([(0 : Int), 1, 2 ^ 128 - 1].flatMap fun x => [(0 : Int), 1, 2 ^ 128 - 1].flatMap fun y =>
    [ mk "callPoint(address,uint128)" [a T, .int x] s!"{x}",
      mk "callSumPoint(address,uint128,uint128)" [a T, .int x, .int y] s!"{x} {y}" ]) ++
  ([0, 1, 5].flatMap fun p => [(0 : Int), 1, 5, 2 ^ 256 - 4, 2 ^ 256 - 3, 2 ^ 256 - 2, MAX].flatMap fun v =>
    [ mkS 0 p (mk "callBack(address,uint256)" [a T, .int v] s!"{p} {v}"),
      mkS 0 p (mk "selfPoke(uint256)" [.int v] s!"{p} {v}"), mkS 0 p (mk "poke(uint256)" [.int v] s!"{p} {v}") ]) ++
  ([0, 7, 2 ^ 256 - 1].map fun l => mkS l 0 (mk "selfView()" [] s!"{l}")) ++
  ([0, 1, 2 ^ 256 - 1].flatMap fun l => [0, 1, 5].map fun v =>
    mkS l 0 { name := s!"receive {l} {v}", code := runtime, accounts := others, value := v, balance := v })

def scenario : Scenario :=
  { name := "Calls", program := _root_.Calls.SoliditySpec.program, target := "Calls", cases := cases }

def scenarioBoundaries : Scenario :=
  { name := "Calls/boundaries", program := _root_.Calls.SoliditySpec.program, target := "Calls", cases := boundaries }

end Solidity.Test.Calls
