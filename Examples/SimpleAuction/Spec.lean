import Solm.Semantics
import Solm.SolidityLayout
import Solm.MetaSolidityLayout

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

The generated storage layout matches the deployed solc bytecode: scalar slots 0..3,
`pendingReturns` uses mapping base slot 4, and `ended` occupies slot 5, byte offset 0.
The external-call ABI uses the generic empty-call helper.
-/

open Solm ABI Ethereum

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
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage beneficiaryRef (.var "beneficiaryAddress"),
        .assign .storage auctionEndTimeRef (u256 (.binary .add now (.var "biddingTime"))) ] }

/-! ## Transitions -/

/-- `bid() external payable` — record a new high bid, queueing the prior bid for refund. -/
def bidTransition : TransitionDecl :=
  { name := "bid"
    params := []
    returnType := []
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
    returnType := [boolTy]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "amount" (some uint256) (.storage (pendingReturnsRef sender)),
        .ite (.binary .gt (.var "amount") (.intLit 0))
          [ .assign .storage (pendingReturnsRef sender) (.intLit 0),
            -- `(bool success, ) = payable(msg.sender).call{value: amount}("");`
            .lowLevelCall sender (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
            .ite (.unary .not (.var "success"))
              [ .assign .storage (pendingReturnsRef sender) (.var "amount"),
                .return [(.boolLit false)] ]
              [] ]
          [],
        .return [(.boolLit true)] ] }

/-- `auctionEnd() external` — once the auction is over, mark it ended and pay the beneficiary. -/
def auctionEndTransition : TransitionDecl :=
  { name := "auctionEnd"
    params := []
    returnType := []
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
  { name := "beneficiary", params := [], returnType := [addr]
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return [(.storage beneficiaryRef)] ] }

def auctionEndTimeGetter : TransitionDecl :=
  { name := "auctionEndTime", params := [], returnType := [uint256]
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return [(.storage auctionEndTimeRef)] ] }

def highestBidderGetter : TransitionDecl :=
  { name := "highestBidder", params := [], returnType := [addr]
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return [(.storage highestBidderRef)] ] }

def highestBidGetter : TransitionDecl :=
  { name := "highestBid", params := [], returnType := [uint256]
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return [(.storage highestBidRef)] ] }

/-! ## Contract + config -/

def simpleAuctionContract : ContractDecl :=
  { name := "SimpleAuction"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ bidTransition, withdrawTransition, auctionEndTransition,
        beneficiaryGetter, auctionEndTimeGetter, highestBidderGetter, highestBidGetter ] }

/-! ## Generated storage layout -/

def simpleAuctionUint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def simpleAuctionAddrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def simpleAuctionBoolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def simpleAuctionMappingSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (KEC (key.toByteArray ++ baseSlot.toByteArray))

def pendingReturnsSlot (owner : KeyValue) : Ethereum.UInt256 :=
  simpleAuctionMappingSlot (keyValueToWord owner) ⟨4⟩

def simpleAuctionStorageLayout : StorageLayout :=
  solidityLayout! [([] : List StructDecl)] [storageDecls]

end SimpleAuction

def simpleAuctionConfig : Config :=
  { storageBackend := solidityStorageBackend SimpleAuction.simpleAuctionStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment SimpleAuction.simpleAuctionContract.ctor.params }

@[simp] theorem simpleAuctionConfig_storage_beneficiary :
    simpleAuctionConfig.storageBackend.locate? { base := "beneficiary", steps := [] } =
      some (.leaf (SimpleAuction.simpleAuctionAddrLoc ⟨0⟩)) :=
  rfl

@[simp] theorem simpleAuctionConfig_storage_auctionEndTime :
    simpleAuctionConfig.storageBackend.locate? { base := "auctionEndTime", steps := [] } =
      some (.leaf (SimpleAuction.simpleAuctionUint256Loc ⟨1⟩)) :=
  rfl

@[simp] theorem simpleAuctionConfig_storage_highestBidder :
    simpleAuctionConfig.storageBackend.locate? { base := "highestBidder", steps := [] } =
      some (.leaf (SimpleAuction.simpleAuctionAddrLoc ⟨2⟩)) :=
  rfl

@[simp] theorem simpleAuctionConfig_storage_highestBid :
    simpleAuctionConfig.storageBackend.locate? { base := "highestBid", steps := [] } =
      some (.leaf (SimpleAuction.simpleAuctionUint256Loc ⟨3⟩)) :=
  rfl

@[simp] theorem simpleAuctionConfig_storage_pendingReturns (owner : KeyValue) :
    simpleAuctionConfig.storageBackend.locate? { base := "pendingReturns", steps := [.mindex owner] } =
      some (.leaf (SimpleAuction.simpleAuctionUint256Loc (SimpleAuction.pendingReturnsSlot owner))) :=
  rfl

@[simp] theorem simpleAuctionConfig_storage_ended :
    simpleAuctionConfig.storageBackend.locate? { base := "ended", steps := [] } =
      some (.leaf (SimpleAuction.simpleAuctionBoolLoc ⟨5⟩)) :=
  rfl
