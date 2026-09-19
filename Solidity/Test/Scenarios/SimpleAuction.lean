import Solidity.Test.Harness
import Solidity.Test.Specs.SimpleAuction
import Solm.Examples.SimpleAuction.Bytecode
import Solidity.Test.Fixtures.SimpleAuctionSolc

/-! # Differential cases: SimpleAuction (payable, custom errors, events, `.call{value}` to EOAs). -/

namespace Solidity.Test.SimpleAuction

open Solidity.Test

def B : Nat := 0xBE
def V1 : Nat := 0xA11CE
def V2 : Nat := 0xB0B

def max256 : Nat := 2 ^ 256 - 1

def bene (a : Nat) : Solm.EvaledStorageRef × Nat := (⟨"beneficiary", []⟩, a)
def endTime (t : Nat) : Solm.EvaledStorageRef × Nat := (⟨"auctionEndTime", []⟩, t)
def bidder (a : Nat) : Solm.EvaledStorageRef × Nat := (⟨"highestBidder", []⟩, a)
def bid (n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"highestBid", []⟩, n)
def pend (a n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"pendingReturns", [.mindex (.address (addr a))]⟩, n)
def ended : Solm.EvaledStorageRef × Nat := (⟨"ended", []⟩, 1)

def stamp (t : Nat) : Ethereum.BlockHeader := { (default : Ethereum.BlockHeader) with timestamp := t }

def creation : ByteArray := bytesOfHex Fixtures.simpleAuctionCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.simpleAuctionRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := simpleAuctionBytecode }

def cases : List Case :=
  [ rt "beneficiary" { call := some ("beneficiary()", []), refs := [bene B, endTime 1000], expect := .success },
    rt "auctionEndTime" { call := some ("auctionEndTime()", []), refs := [bene B, endTime 1000],
                          expect := .success },
    rt "highestBidder" { call := some ("highestBidder()", []), refs := [bidder V2, bid 100],
                         expect := .success },
    rt "highestBid" { call := some ("highestBid()", []), refs := [bidder V2, bid 100], expect := .success },
    rt "bid-first" { call := some ("bid()", []), refs := [bene B, endTime 1000], value := 100,
                     header := stamp 500, expect := .success },
    rt "bid-higher" { call := some ("bid()", []), refs := [bene B, endTime 1000, bidder V2, bid 100],
                      value := 150, header := stamp 500, balance := 100, expect := .success },
    rt "bid-higher-again" { call := some ("bid()", []),
                            refs := [bene B, endTime 1000, bidder V2, bid 100, pend V2 30], value := 150,
                            header := stamp 500, balance := 130, expect := .success },
    rt "bid-not-high-enough" { call := some ("bid()", []), refs := [bene B, endTime 1000, bidder V2, bid 100],
                               value := 50, header := stamp 500, balance := 100, expect := .revert },
    rt "bid-equal" { call := some ("bid()", []), refs := [bene B, endTime 1000, bidder V2, bid 100],
                     value := 100, header := stamp 500, balance := 100, expect := .revert },
    rt "bid-ended" { call := some ("bid()", []), refs := [bene B, endTime 1000], value := 100,
                     header := stamp 1001, expect := .revert },
    rt "bid-at-end" { call := some ("bid()", []), refs := [bene B, endTime 1000], value := 100,
                      header := stamp 1000, expect := .success },
    rt "bid-zero" { call := some ("bid()", []), refs := [bene B, endTime 1000], value := 0, header := stamp 500,
                    expect := .revert },
    rt "withdraw" { call := some ("withdraw()", []), refs := [bene B, endTime 1000, pend V1 100],
                    balance := 100, expect := .success },
    rt "withdraw-nothing" { call := some ("withdraw()", []), refs := [bene B, endTime 1000],
                            expect := .success },
    rt "withdraw-unfunded" { call := some ("withdraw()", []), refs := [bene B, endTime 1000, pend V1 100],
                             balance := 0, expect := .success },
    rt "withdraw-nonpayable" { call := some ("withdraw()", []), refs := [bene B, endTime 1000, pend V1 100],
                               balance := 100, value := 1, expect := .revert },
    rt "auctionEnd" { call := some ("auctionEnd()", []), refs := [bene B, endTime 1000, bidder V2, bid 100],
                      balance := 100, header := stamp 1000, expect := .success },
    rt "auctionEnd-not-yet" { call := some ("auctionEnd()", []),
                              refs := [bene B, endTime 1000, bidder V2, bid 100], balance := 100,
                              header := stamp 999, expect := .revert },
    rt "auctionEnd-already" { call := some ("auctionEnd()", []),
                              refs := [bene B, endTime 1000, bidder V2, bid 100, ended], balance := 100,
                              header := stamp 2000, expect := .revert },
    rt "auctionEnd-unfunded" { call := some ("auctionEnd()", []),
                               refs := [bene B, endTime 1000, bidder V2, bid 100], balance := 0,
                               header := stamp 2000, expect := .revert },
    rt "auctionEnd-zero-bid" { call := some ("auctionEnd()", []), refs := [bene B, endTime 1000],
                               header := stamp 2000, expect := .success },
    rt "empty-calldata" { refs := [bene B, endTime 1000], expect := .revert },
    rt "empty-calldata-value" { refs := [bene B, endTime 1000], value := 5, expect := .revert },
    rt "unknown-selector" { calldata := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, refs := [bene B, endTime 1000],
                            expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([.int 600, .address (addr B)], runtime),
      header := stamp 400, expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([.int 600, .address (addr B)], runtime),
      header := stamp 400, value := 1, expect := .revert },
    { name := "constructor-overflow", code := creation, ctorArgs := some ([.int max256, .address (addr B)], runtime),
      header := stamp 400, expect := .revert } ]

def scenario : Scenario :=
  { name := "SimpleAuction", program := _root_.SimpleAuction.SoliditySpec.program,
    target := _root_.SimpleAuction.SoliditySpec.target, cases := cases }

def scenarioSolc : Scenario :=
  { scenario with
      name := "SimpleAuction/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `simpleAuctionInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "SimpleAuction/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) =>
          let known := if c.name == "constructor-overflow" then some "hand-written initcode reverts without Panic(0x11) data" else none
          some { c with code := simpleAuctionInitcode, ctorArgs := some (args, simpleAuctionBytecode), known := known }
        | none => none }

end Solidity.Test.SimpleAuction
