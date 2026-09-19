import Solidity.Test.Harness
import Solidity.Test.Specs.BlindAuction
import Solm.Examples.BlindAuction.Bytecode
import Solidity.Test.Fixtures.BlindAuctionSolc

/-! # Differential cases: BlindAuction. -/

namespace Solidity.Test.BlindAuction

open Solidity.Test

def B : Nat := 0xBE
def S : Nat := 0xA11CE
def V2 : Nat := 0xB0B

def max256 : Nat := 2 ^ 256 - 1
def stamp (t : Nat) : Ethereum.BlockHeader := { (default : Ethereum.BlockHeader) with timestamp := t }

def sv (n : String) (v : Nat) : Solm.EvaledStorageRef × Nat := (⟨n, []⟩, v)
def pend (a n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"pendingReturns", [.mindex (.address (addr a))]⟩, n)
def bidsLen (a n : Nat) : Solm.EvaledStorageRef × Nat := (⟨"bids", [.mindex (.address (addr a)), .length]⟩, n)
def bidField (a i : Nat) (f : String) (v : Nat) : Solm.EvaledStorageRef × Nat :=
  (⟨"bids", [.mindex (.address (addr a)), .aindex (.int i), .field f]⟩, v)

/-- `keccak256(abi.encodePacked(value, fake, secret))` as a word. -/
def blinded (value : Nat) (fake : Bool) (secret : Nat) : Nat :=
  natOfBytes (ffi.KEC (wordBytes value ++ ⟨#[if fake then 1 else 0]⟩ ++ wordBytes secret))

def b32 (n : Nat) : Solm.Value := .fixedBytes ⟨31, by decide⟩ (wordBytes n).toList

/-- One placed bid of `S`: `bids[S] = [(blinded(value, fake, secret), deposit)]`. -/
def oneBid (value : Nat) (fake : Bool) (secret deposit : Nat) : List (Solm.EvaledStorageRef × Nat) :=
  [bidsLen S 1, bidField S 0 "blindedBid" (blinded value fake secret), bidField S 0 "deposit" deposit]

def times : List (Solm.EvaledStorageRef × Nat) := [sv "beneficiary" B, sv "biddingEnd" 1000, sv "revealEnd" 2000]

def revealSig := "reveal(uint256[],bool[],bytes32[])"
def revealArgs (vs : List Nat) (fs : List Bool) (ss : List Nat) : Option (String × List Solm.Value) :=
  some (revealSig, [.array (vs.map (.int ·)), .array (fs.map (.bool ·)), .array (ss.map b32)])

/-- Hand-encoded `reveal` calldata with raw `bool` words (dirty values are validated on access). -/
def revealRaw (vs fakeWords ss : List Nat) : ByteArray :=
  let arr (ws : List Nat) : ByteArray := ws.foldl (fun b w => b ++ wordBytes w) (wordBytes ws.length)
  let o1 := 0x60
  let o2 := o1 + 32 * (vs.length + 1)
  let o3 := o2 + 32 * (fakeWords.length + 1)
  selectorOfSig revealSig ++ wordBytes o1 ++ wordBytes o2 ++ wordBytes o3 ++ arr vs ++ arr fakeWords ++ arr ss

def creation : ByteArray := bytesOfHex Fixtures.blindAuctionCreationHex
def runtime : ByteArray := bytesOfHex Fixtures.blindAuctionRuntimeHex

def rt (name : String) (c : Case) : Case := { c with name := name, code := blindAuctionBytecode }

def cases : List Case :=
  [ rt "beneficiary" { call := some ("beneficiary()", []), refs := times, expect := .success },
    rt "biddingEnd" { call := some ("biddingEnd()", []), refs := times, expect := .success },
    rt "revealEnd" { call := some ("revealEnd()", []), refs := times, expect := .success },
    rt "ended" { call := some ("ended()", []), refs := times ++ [sv "ended" 1], expect := .success },
    rt "highestBidder" { call := some ("highestBidder()", []),
                         refs := [sv "highestBidder" V2, sv "highestBid" 5], expect := .success },
    rt "highestBid" { call := some ("highestBid()", []), refs := [sv "highestBidder" V2, sv "highestBid" 5],
                      expect := .success },
    rt "bids-getter" { call := some ("bids(address,uint256)", [.address (addr S), .int 0]),
                       refs := times ++ oneBid 5 false 11 5, expect := .success },
    rt "bids-getter-out-of-range" { call := some ("bids(address,uint256)", [.address (addr S), .int 1]),
                                    refs := times ++ oneBid 5 false 11 5, expect := .revert },
    rt "bids-getter-empty" { call := some ("bids(address,uint256)", [.address (addr V2), .int 0]),
                             refs := times, expect := .revert },
    rt "bid" { call := some ("bid(bytes32)", [b32 (blinded 5 false 11)]), refs := times, value := 5,
               header := stamp 500, expect := .success },
    rt "bid-second" { call := some ("bid(bytes32)", [b32 (blinded 7 true 12)]),
                      refs := times ++ oneBid 5 false 11 5, value := 9, balance := 5, header := stamp 500,
                      expect := .success },
    rt "bid-too-late" { call := some ("bid(bytes32)", [b32 (blinded 5 false 11)]), refs := times, value := 5,
                        header := stamp 1000, expect := .revert },
    rt "bid-zero-value" { call := some ("bid(bytes32)", [b32 0]), refs := times, header := stamp 500,
                          expect := .success },
    rt "reveal-valid" { call := revealArgs [5] [false] [11], refs := times ++ oneBid 5 false 11 5,
                        balance := 5, header := stamp 1500, expect := .success },
    rt "reveal-fake" { call := revealArgs [5] [true] [11], refs := times ++ oneBid 5 true 11 5, balance := 5,
                       header := stamp 1500, expect := .success },
    rt "reveal-wrong-secret" { call := revealArgs [5] [false] [12], refs := times ++ oneBid 5 false 11 5,
                               balance := 5, header := stamp 1500, expect := .success },
    rt "reveal-underfunded-bid" { call := revealArgs [9] [false] [11], refs := times ++ oneBid 9 false 11 5,
                                  balance := 5, header := stamp 1500, expect := .success },
    rt "reveal-not-highest" { call := revealArgs [5] [false] [11],
                              refs := times ++ oneBid 5 false 11 5 ++ [sv "highestBidder" V2, sv "highestBid" 8],
                              balance := 13, header := stamp 1500, expect := .success },
    rt "reveal-overbid" { call := revealArgs [5] [false] [11],
                          refs := times ++ oneBid 5 false 11 5 ++ [sv "highestBidder" V2, sv "highestBid" 3],
                          balance := 8, header := stamp 1500, expect := .success },
    rt "reveal-two-bids" { call := revealArgs [5, 7] [false, false] [11, 12],
                           refs := times ++ [bidsLen S 2, bidField S 0 "blindedBid" (blinded 5 false 11), bidField S 0 "deposit" 5, bidField S 1 "blindedBid" (blinded 7 false 12), bidField S 1 "deposit" 7],
                           balance := 12, header := stamp 1500, expect := .success },
    rt "reveal-too-early" { call := revealArgs [5] [false] [11], refs := times ++ oneBid 5 false 11 5,
                            balance := 5, header := stamp 1000, expect := .revert },
    rt "reveal-too-late" { call := revealArgs [5] [false] [11], refs := times ++ oneBid 5 false 11 5,
                           balance := 5, header := stamp 2000, expect := .revert },
    rt "reveal-length-mismatch" { call := revealArgs [5, 6] [false] [11], refs := times ++ oneBid 5 false 11 5,
                                  balance := 5, header := stamp 1500, expect := .revert },
    rt "reveal-no-bids" { call := revealArgs [] [] [], refs := times, header := stamp 1500, expect := .success },
    rt "reveal-dirty-bool-unused" { calldata := revealRaw [] [] [], refs := times, header := stamp 1500,
                                    expect := .success },
    rt "reveal-dirty-bool-read" { calldata := revealRaw [5] [2] [11], refs := times ++ oneBid 5 false 11 5,
                                  balance := 5, header := stamp 1500, expect := .revert },
    rt "reveal-unfunded-refund" { call := revealArgs [5] [true] [11], refs := times ++ oneBid 5 true 11 5,
                                  balance := 0, header := stamp 1500, expect := .revert },
    rt "withdraw" { call := some ("withdraw()", []), refs := times ++ [pend S 7], balance := 7,
                    expect := .success },
    rt "withdraw-nothing" { call := some ("withdraw()", []), refs := times, expect := .success },
    rt "withdraw-unfunded" { call := some ("withdraw()", []), refs := times ++ [pend S 7], balance := 0,
                             expect := .revert },
    rt "auctionEnd" { call := some ("auctionEnd()", []),
                      refs := times ++ [sv "highestBidder" V2, sv "highestBid" 5], balance := 5,
                      header := stamp 2001, expect := .success },
    rt "auctionEnd-too-early" { call := some ("auctionEnd()", []), refs := times, header := stamp 2000,
                                expect := .revert },
    rt "auctionEnd-already" { call := some ("auctionEnd()", []), refs := times ++ [sv "ended" 1],
                              header := stamp 2001, expect := .revert },
    rt "auctionEnd-unfunded" { call := some ("auctionEnd()", []), refs := times ++ [sv "highestBid" 5],
                               balance := 0, header := stamp 2001, expect := .revert },
    rt "withdraw-nonpayable" { call := some ("withdraw()", []), refs := times, value := 1, expect := .revert },
    rt "empty-calldata" { refs := times, expect := .revert },
    { name := "constructor", code := creation, ctorArgs := some ([.int 600, .int 1000, .address (addr B)], runtime),
      header := stamp 400, expect := .success },
    { name := "constructor-nonpayable", code := creation, ctorArgs := some ([.int 600, .int 1000, .address (addr B)], runtime),
      header := stamp 400, value := 1, expect := .revert },
    { name := "constructor-overflow-bidding", code := creation, ctorArgs := some ([.int max256, .int 1, .address (addr B)], runtime),
      header := stamp 400, expect := .revert },
    { name := "constructor-overflow-reveal", code := creation, ctorArgs := some ([.int 600, .int max256, .address (addr B)], runtime),
      header := stamp 400, expect := .revert } ]

def scenario : Scenario :=
  { name := "BlindAuction", program := _root_.BlindAuction.SoliditySpec.program, target := "BlindAuction", cases := cases }

/-- The same runtime cases on the local solc's runtime code. -/
def scenarioSolc : Scenario :=
  { scenario with
      name := "BlindAuction/solc-0.8.35",
      cases := cases.filterMap fun c => if c.ctorArgs.isSome then none else some { c with code := runtime } }

/-- Deployment through the pinned `blindAuctionInitcode`. -/
def scenarioPinnedCtor : Scenario :=
  { scenario with
      name := "BlindAuction/pinned-initcode",
      cases := cases.filterMap fun c => match c.ctorArgs with
        | some (args, _) => some { c with code := blindAuctionInitcode, ctorArgs := some (args, blindAuctionBytecode), known := if c.name.startsWith "constructor-overflow" then some "hand-written initcode reverts without Panic(0x11) data" else none }
        | none => none }

end Solidity.Test.BlindAuction
