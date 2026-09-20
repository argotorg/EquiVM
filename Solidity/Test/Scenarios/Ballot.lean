import Solidity.Test.Harness
import Solidity.Test.Specs.Ballot
import Solm.Examples.Ballot.Bytecode
import Solidity.Test.Fixtures.BallotSolc

/-! # Differential cases: Ballot (optimizer ON; structs, storage pointers, dynamic arrays, loops). -/

namespace Solidity.Test.Ballot

open Solidity.Test

def C : Nat := 0xC4A1
def V1 : Nat := 0xA11CE
def V2 : Nat := 0xB0B
def V3 : Nat := 0xF00D

def voter (a : Nat) (f : String) (n : Nat) : Solm.EvaledStorageRef × Nat :=
  (⟨"voters", [.mindex (.address (addr a)), .field f]⟩, n)
def weight (a n : Nat) := voter a "weight" n
def voted (a : Nat) := voter a "voted" 1
def delegateTo (a b : Nat) := voter a "delegate" b
def voteOf (a n : Nat) := voter a "vote" n
def chair (a : Nat) : Solm.EvaledStorageRef × Nat := (⟨"chairperson", []⟩, a)
def len (n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"proposals", [.length]⟩, n)
def pname (i c : Nat) : Solm.EvaledStorageRef × Nat := (⟨"proposals", [.aindex (.int i), .field "name"]⟩, c <<< 248)
def votes (i n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"proposals", [.aindex (.int i), .field "voteCount"]⟩, n)

def b32 (c : Nat) : ABI.ABIValue := .fixedBytes ⟨31, by decide⟩ (wordBytes (c <<< 248)).toList

def creation : ByteArray := bytesOfHex Fixtures.ballotCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.ballotRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := ballotBytecode }

def cases : List Case :=
  [ rt "chairperson" { call := some ("chairperson()", []), refs := [chair C], expect := .success },
    rt "voters-getter" { call := some ("voters(address)", [.address (addr V1)]),
                         refs := [weight V1 1, voted V1, delegateTo V1 V2, voteOf V1 3], expect := .success },
    rt "voters-getter-unset" { call := some ("voters(address)", [.address (addr V3)]), expect := .success },
    rt "proposals-getter" { call := some ("proposals(uint256)", [.int 1]),
                            refs := [len 2, pname 0 0x41, pname 1 0x42, votes 1 9], expect := .success },
    rt "proposals-getter-out-of-range" { call := some ("proposals(uint256)", [.int 5]), refs := [len 2],
                                         expect := .revert },
    rt "giveRightToVote" { sender := addr C, call := some ("giveRightToVote(address)", [.address (addr V2)]),
                           refs := [chair C], expect := .success },
    rt "giveRightToVote-not-chair" { call := some ("giveRightToVote(address)", [.address (addr V2)]),
                                     refs := [chair C], expect := .revert },
    rt "giveRightToVote-already-voted" { sender := addr C,
                                         call := some ("giveRightToVote(address)", [.address (addr V2)]),
                                         refs := [chair C, voted V2], expect := .revert },
    rt "giveRightToVote-has-weight" { sender := addr C,
                                      call := some ("giveRightToVote(address)", [.address (addr V2)]),
                                      refs := [chair C, weight V2 1], expect := .revert },
    rt "vote" { call := some ("vote(uint256)", [.int 1]), refs := [weight V1 2, len 2, votes 1 5],
                expect := .success },
    rt "vote-no-weight" { call := some ("vote(uint256)", [.int 1]), refs := [len 2], expect := .revert },
    rt "vote-already-voted" { call := some ("vote(uint256)", [.int 1]), refs := [weight V1 1, voted V1, len 2],
                              expect := .revert },
    rt "vote-out-of-range" { call := some ("vote(uint256)", [.int 7]), refs := [weight V1 1, len 2],
                             expect := .revert },
    rt "vote-nonpayable" { call := some ("vote(uint256)", [.int 1]), refs := [weight V1 1, len 2], value := 1,
                           expect := .revert },
    rt "delegate" { call := some ("delegate(address)", [.address (addr V2)]),
                    refs := [weight V1 1, weight V2 1], expect := .success },
    rt "delegate-to-voted" { call := some ("delegate(address)", [.address (addr V2)]),
                             refs := [weight V1 3, weight V2 1, voted V2, voteOf V2 0, len 1, votes 0 4],
                             expect := .success },
    rt "delegate-chain" { call := some ("delegate(address)", [.address (addr V2)]),
                          refs := [weight V1 1, weight V2 1, voted V2, delegateTo V2 V3, weight V3 1],
                          expect := .success },
    rt "delegate-loop" { call := some ("delegate(address)", [.address (addr V2)]),
                         refs := [weight V1 1, weight V2 1, voted V2, delegateTo V2 V1], expect := .revert },
    rt "delegate-self" { call := some ("delegate(address)", [.address (addr V1)]), refs := [weight V1 1],
                         expect := .revert },
    rt "delegate-no-weight" { call := some ("delegate(address)", [.address (addr V2)]), refs := [weight V2 1],
                              expect := .revert },
    rt "delegate-already-voted" { call := some ("delegate(address)", [.address (addr V2)]),
                                  refs := [weight V1 1, voted V1, weight V2 1], expect := .revert },
    rt "delegate-to-nonvoter" { call := some ("delegate(address)", [.address (addr V2)]),
                                refs := [weight V1 1], expect := .revert },
    rt "winningProposal" { call := some ("winningProposal()", []),
                           refs := [len 3, votes 0 3, votes 1 7, votes 2 5], expect := .success },
    rt "winningProposal-tie" { call := some ("winningProposal()", []), refs := [len 2, votes 0 7, votes 1 7],
                               expect := .success },
    rt "winningProposal-empty" { call := some ("winningProposal()", []), expect := .success },
    rt "winnerName" { call := some ("winnerName()", []),
                      refs := [len 2, pname 0 0x41, pname 1 0x42, votes 1 2], expect := .success },
    rt "winnerName-empty" { call := some ("winnerName()", []), expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, expect := .revert },
    rt "empty-calldata" { expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([.array [b32 0x41, b32 0x42, b32 0x43]], runtime),
      expect := .success },
    { name := "constructor-empty", code := creation, ctorArgs := some ([.array []], runtime),
      expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([.array [b32 0x41]], runtime),
      value := 1, expect := .revert } ]

def scenario : Scenario :=
  { name := "Ballot", program := _root_.Ballot.SoliditySpec.program, target := _root_.Ballot.SoliditySpec.target,
    cases := cases }

def scenarioSolc : Scenario :=
  { scenario with
      name := "Ballot/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

end Solidity.Test.Ballot
