import Solm.Semantics
import Solm.SolidityLayout

/-!
# SimpleAuction — Solm specification for `SimpleAuction.sol`

A faithful (events-aside) Solm spec of the classic Solidity `SimpleAuction` example.

Notable Solm features exercised:

* the value/time environment — `msg.value` (`env .callvalue`), `msg.sender` (`env .caller`),
  `block.timestamp` (`env .timestamp`);
* a `mapping(address => uint)` (`pendingReturns`) with a read-modify-write (`+=`);
* the low-level value send `payable(addr).call{value: v}("")` modelled as `lowLevelCall` (raw call,
  binds a `success : bool`, callee revert does **not** propagate), in both the "refund and possibly
  roll back" (`withdraw`) and "pay-or-revert" (`auctionEnd`) shapes;
* `if (cond) revert E();` modelled as `require (¬cond)` — the custom-error payload is dropped, since
  the spec tracks storage and return values only;
* the four solc-generated public getters (`beneficiary`, `auctionEndTime`, `highestBidder`,
  `highestBid`).

The storage layout and the (empty) external-call ABI are taken from the generic Solidity helpers;
they are a sketch to be pinned when proving runtime equivalence against the deployed bytecode.
-/

open Solm ABI

namespace SimpleAuction

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)
def addr    : ABIType := .elem .address
def boolTy  : ABIType := .elem .bool

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt    : StorageType := .elem .address
def boolSt    : StorageType := .elem .bool

/-! ## Expression / ref helpers -/

def sender : Expr := .env .caller
def now : Expr := .env .timestamp
/-- Pin a value into the `uint256` range (models solc's *checked* arithmetic: reverts on overflow). -/
def u256 (e : Expr) : Expr := .inRange uint256Int e

def beneficiaryRef    : StorageRef := { base := "beneficiary" }
def auctionEndTimeRef : StorageRef := { base := "auctionEndTime" }
def highestBidderRef  : StorageRef := { base := "highestBidder" }
def highestBidRef     : StorageRef := { base := "highestBid" }
def endedRef          : StorageRef := { base := "ended" }
/-- `pendingReturns[a]`. -/
def pendingReturnsRef (a : Expr) : StorageRef := { base := "pendingReturns", steps := [.mindex a] }

/-! ## Storage -/

def storageDecls : List StorageDecl :=
  [ { name := "beneficiary", ty := addrSt },
    { name := "auctionEndTime", ty := uint256St },
    { name := "highestBidder", ty := addrSt },
    { name := "highestBid", ty := uint256St },
    { name := "pendingReturns", ty := .mapping .address uint256St },
    { name := "ended", ty := boolSt } ]

/-! ## Constructor

`constructor(uint biddingTime, address payable beneficiaryAddress)`.
-/
def constructorDecl : ConstructorDecl :=
  { params :=
      [ { name := "biddingTime", ty := uint256 },
        { name := "beneficiaryAddress", ty := addr } ]
    body :=
      [ .assign .storage beneficiaryRef (.var "beneficiaryAddress"),
        .assign .storage auctionEndTimeRef (u256 (.binary .add now (.var "biddingTime"))) ] }

/-! ## Transitions -/

/-- `bid() external payable` — record a new high bid, queueing the prior bid for refund. -/
def bidTransition : TransitionDecl :=
  { name := "bid"
    params := []
    returnType := none
    body :=
      -- `if (block.timestamp > auctionEndTime) revert AuctionAlreadyEnded();`
      [ .require (.binary .le now (.storage auctionEndTimeRef)),
        -- `if (msg.value <= highestBid) revert BidNotHighEnough(highestBid);`
        .require (.binary .gt (.env .callvalue) (.storage highestBidRef)),
        -- `if (highestBid != 0) pendingReturns[highestBidder] += highestBid;`
        .ite (.binary .ne (.storage highestBidRef) (.intLit 0))
          [ .assign .storage (pendingReturnsRef (.storage highestBidderRef))
              (u256 (.binary .add
                (.storage (pendingReturnsRef (.storage highestBidderRef)))
                (.storage highestBidRef))) ]
          [],
        .assign .storage highestBidderRef sender,
        .assign .storage highestBidRef (.env .callvalue) ] }

/-- `withdraw() external returns (bool)` — refund a previously overbid amount; on a failed send,
    restore the credit and return `false`. -/
def withdrawTransition : TransitionDecl :=
  { name := "withdraw"
    params := []
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "amount" (some uint256) (.storage (pendingReturnsRef sender)),
        .ite (.binary .gt (.var "amount") (.intLit 0))
          [ .assign .storage (pendingReturnsRef sender) (.intLit 0),
            -- `(bool success, ) = payable(msg.sender).call{value: amount}("");`
            .lowLevelCall sender (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
            .ite (.unary .not (.var "success"))
              [ .assign .storage (pendingReturnsRef sender) (.var "amount"),
                .return (.boolLit false) ]
              [] ]
          [],
        .return (.boolLit true) ] }

/-- `auctionEnd() external` — once the auction is over, mark it ended and pay the beneficiary. -/
def auctionEndTransition : TransitionDecl :=
  { name := "auctionEnd"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        -- `if (block.timestamp < auctionEndTime) revert AuctionNotYetEnded();`
        .require (.binary .ge now (.storage auctionEndTimeRef)),
        -- `if (ended) revert AuctionEndAlreadyCalled();`
        .require (.unary .not (.storage endedRef)),
        .assign .storage endedRef (.boolLit true),
        -- `(bool success, ) = beneficiary.call{value: highestBid}("");  require(success);`
        .lowLevelCall (.storage beneficiaryRef) (.storage highestBidRef)
          (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ] }

/-! ## Transitions — auto-generated public getters -/

def beneficiaryGetter : TransitionDecl :=
  { name := "beneficiary", params := [], returnType := some addr
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage beneficiaryRef) ] }

def auctionEndTimeGetter : TransitionDecl :=
  { name := "auctionEndTime", params := [], returnType := some uint256
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage auctionEndTimeRef) ] }

def highestBidderGetter : TransitionDecl :=
  { name := "highestBidder", params := [], returnType := some addr
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage highestBidderRef) ] }

def highestBidGetter : TransitionDecl :=
  { name := "highestBid", params := [], returnType := some uint256
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage highestBidRef) ] }

/-! ## Contract + config -/

def simpleAuctionContract : ContractDecl :=
  { name := "SimpleAuction"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ bidTransition, withdrawTransition, auctionEndTransition,
        beneficiaryGetter, auctionEndTimeGetter, highestBidderGetter, highestBidGetter ] }

/-- Storage layout (sketch — refine the slot details when proving). -/
def simpleAuctionStorageLayout : StorageLayout where
  layout :=
    match genSolidityLayout [] storageDecls with
    | some layout => layout
    | none => fun _ _ => none

end SimpleAuction

def simpleAuctionConfig : Config :=
  { storage := SimpleAuction.simpleAuctionStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment SimpleAuction.simpleAuctionContract.ctor.params }
