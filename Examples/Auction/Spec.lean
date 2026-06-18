import Solm.Semantics
import Solm.SolidityLayout

/-!
# Auction — Solm specification for Nouns' `NounsAuctionHouse.sol`

A faithful (events-aside) Solm spec of the Nouns auction house.  Inherited machinery is **flattened**:
`Ownable`→`_owner`, `Pausable`→`_paused`, `ReentrancyGuard`→`_locked`; modifiers are inlined as
`require`/`assign`; `initialize` is modelled as the constructor.

Notable Solm features exercised: `block.timestamp` (`env .timestamp`), `if`/`ite`, the typed
try/catch (`checkedCall`) around `nouns.mint()`, the low-level value send (`lowLevelCall`) with the
WETH fallback, and the `Error(string)`-selector discrimination via `bytesSlice` + `bytes` equality.

The external-call ABI (`auctionExternalABI`) and storage layout are sketched for the spec; their
exact `encode?`/slot details are to be pinned when proving.
-/

open Solm ABI

namespace Auction

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)
def uint8 : ABIType := .elem (.int uint8Int)
def addr : ABIType := .elem .address

def uint256St : StorageType := .elem (.int uint256Int)
def uint8St : StorageType := .elem (.int uint8Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool

/-! ## Expression / ref helpers -/

def sender : Expr := .env .caller
def now : Expr := .env .timestamp
/-- `address(0)`. -/
def zeroAddr : Expr := .cast (.intLit 0) addrSt
/-- Pin a value into the `uint256` range (models non-wrapping solc arithmetic; reverts on overflow). -/
def u256 (e : Expr) : Expr := .inRange uint256Int e
/-- `keccak256("Error(string)")[:4]`. -/
def errorStringSelector : ByteArray := ⟨#[0x08, 0xc3, 0x79, 0xa0]⟩

def ownerRef : StorageRef := { base := "_owner" }
def pausedRef : StorageRef := { base := "_paused" }
def lockedRef : StorageRef := { base := "_locked" }
def nounsRef : StorageRef := { base := "nouns" }
def wethRef : StorageRef := { base := "weth" }
def timeBufferRef : StorageRef := { base := "timeBuffer" }
def reservePriceRef : StorageRef := { base := "reservePrice" }
def minBidIncRef : StorageRef := { base := "minBidIncrementPercentage" }
def durationRef : StorageRef := { base := "duration" }
/-- A field of the single `auction` storage struct. -/
def aField (f : Ident) : StorageRef := { base := "auction", steps := [.field f] }

/-! ## Storage -/

def auctionStructTy : StorageType :=
  .struct "Auction"
    [ ("nounId", uint256St), ("amount", uint256St), ("startTime", uint256St),
      ("endTime", uint256St), ("bidder", addrSt), ("settled", boolSt) ]

def auctionStructDecl : StructDecl :=
  { name := "Auction"
    fields :=
      [ { name := "nounId", ty := uint256St }, { name := "amount", ty := uint256St },
        { name := "startTime", ty := uint256St }, { name := "endTime", ty := uint256St },
        { name := "bidder", ty := addrSt }, { name := "settled", ty := boolSt } ] }

def storageDecls : List StorageDecl :=
  [ { name := "nouns", ty := addrSt },
    { name := "weth", ty := addrSt },
    { name := "timeBuffer", ty := uint256St },
    { name := "reservePrice", ty := uint256St },
    { name := "minBidIncrementPercentage", ty := uint8St },
    { name := "duration", ty := uint256St },
    { name := "auction", ty := auctionStructTy },
    { name := "_owner", ty := addrSt },
    { name := "_paused", ty := boolSt },
    { name := "_locked", ty := boolSt } ]

/-! ## Internal helpers -/

/-- `_safeTransferETHWithFallback(to, amount)`: raw value send; on failure wrap to WETH and transfer. -/
def safeTransferETHWithFallback : FunctionDecl :=
  { name := "_safeTransferETHWithFallback"
    params := [{ name := "to", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := none
    body :=
      [ .lowLevelCall (.var "to") (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
        .ite (.unary .not (.var "success"))
          [ .externalCall (.storage wethRef) "deposit" (.var "amount") [] "_dep",
            .externalCall (.storage wethRef) "transfer" (.intLit 0)
              [.var "to", .var "amount"] "_xfer" ]
          [] ] }

/-- `_settleAuction()`: require started/unsettled/expired, mark settled, transfer or burn the noun,
    and pay the owner if there was a bid. -/
def settleAuctionFn : FunctionDecl :=
  { name := "_settleAuction"
    params := []
    returnType := none
    body :=
      [ .require (.binary .ne (.storage (aField "startTime")) (.intLit 0)),
        .require (.unary .not (.storage (aField "settled"))),
        .require (.binary .ge now (.storage (aField "endTime"))),
        .assign (aField "settled") (.boolLit true),
        .ite (.binary .eq (.storage (aField "bidder")) zeroAddr)
          [ .externalCall (.storage nounsRef) "burn" (.intLit 0)
              [.storage (aField "nounId")] "_burn" ]
          [ .externalCall (.storage nounsRef) "transferFrom" (.intLit 0)
              [.env .this, .storage (aField "bidder"), .storage (aField "nounId")] "_tf" ],
        .ite (.binary .gt (.storage (aField "amount")) (.intLit 0))
          [ .internalCall "_safeTransferETHWithFallback"
              [.storage ownerRef, .storage (aField "amount")] "_pay" ]
          [] ] }

/-- `_createAuction()`: `try nouns.mint()`; on success start a fresh auction, on a string-revert
    pause (catch `Error(string)`), on any other revert re-revert. -/
def createAuctionFn : FunctionDecl :=
  { name := "_createAuction"
    params := []
    returnType := none
    body :=
      [ .checkedCall (.storage nounsRef) "mint" (.intLit 0) [] "nounId"
          -- onSuccess (nounId in scope): build the new auction
          [ .assign (aField "nounId") (.var "nounId"),
            .assign (aField "amount") (.intLit 0),
            .assign (aField "startTime") now,
            .assign (aField "endTime") (u256 (.binary .add now (.storage durationRef))),
            .assign (aField "bidder") zeroAddr,
            .assign (aField "settled") (.boolLit false) ]
          -- onFail (err : bytes in scope): catch Error(string) ⇒ pause, else re-revert
          "err"
          [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
                              (.bytesLit errorStringSelector))
              [ .assign pausedRef (.boolLit true) ]
              [ .require (.boolLit false) ] ] ] }

/-! ## Transitions -/

/-- `createBid(uint256 nounId)` — payable, nonReentrant. -/
def createBidTransition : TransitionDecl :=
  { name := "createBid"
    params := [{ name := "nounId", ty := uint256 }]
    returnType := none
    body :=
      [ -- nonReentrant (enter)
        .require (.unary .not (.storage lockedRef)),
        .assign lockedRef (.boolLit true),
        -- validations
        .require (.binary .eq (.storage (aField "nounId")) (.var "nounId")),
        .require (.binary .lt now (.storage (aField "endTime"))),
        .require (.binary .ge (.env .callvalue) (.storage reservePriceRef)),
        .require (.binary .ge (.env .callvalue)
          (.binary .add (.storage (aField "amount"))
            (.binary .div (.binary .mul (.storage (aField "amount")) (.storage minBidIncRef))
              (.intLit 100)))),
        -- refund prior bidder, if any
        .ite (.binary .ne (.storage (aField "bidder")) zeroAddr)
          [ .internalCall "_safeTransferETHWithFallback"
              [.storage (aField "bidder"), .storage (aField "amount")] "_refund" ]
          [],
        -- record the new high bid
        .assign (aField "amount") (.env .callvalue),
        .assign (aField "bidder") sender,
        -- anti-snipe extension
        .ite (.binary .lt (.binary .sub (.storage (aField "endTime")) now) (.storage timeBufferRef))
          [ .assign (aField "endTime") (u256 (.binary .add now (.storage timeBufferRef))) ]
          [],
        -- nonReentrant (leave)
        .assign lockedRef (.boolLit false) ] }

/-- `settleCurrentAndCreateNewAuction()` — nonReentrant, whenNotPaused. -/
def settleAndCreateTransition : TransitionDecl :=
  { name := "settleCurrentAndCreateNewAuction"
    params := []
    returnType := none
    body :=
      [ .require (.unary .not (.storage lockedRef)),
        .assign lockedRef (.boolLit true),
        .require (.unary .not (.storage pausedRef)),
        .internalCall "_settleAuction" [] "_s",
        .internalCall "_createAuction" [] "_c",
        .assign lockedRef (.boolLit false) ] }

/-- `settleAuction()` — whenPaused, nonReentrant. -/
def settleAuctionTransition : TransitionDecl :=
  { name := "settleAuction"
    params := []
    returnType := none
    body :=
      [ .require (.unary .not (.storage lockedRef)),
        .assign lockedRef (.boolLit true),
        .require (.storage pausedRef),
        .internalCall "_settleAuction" [] "_s",
        .assign lockedRef (.boolLit false) ] }

/-- `pause()` — onlyOwner. -/
def pauseTransition : TransitionDecl :=
  { name := "pause"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq sender (.storage ownerRef)),
        .assign pausedRef (.boolLit true) ] }

/-- `unpause()` — onlyOwner; start a fresh auction if none is live. -/
def unpauseTransition : TransitionDecl :=
  { name := "unpause"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq sender (.storage ownerRef)),
        .assign pausedRef (.boolLit false),
        .ite (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
                          (.storage (aField "settled")))
          [ .internalCall "_createAuction" [] "_c" ]
          [] ] }

/-- `setTimeBuffer(uint256)` — onlyOwner. -/
def setTimeBufferTransition : TransitionDecl :=
  { name := "setTimeBuffer"
    params := [{ name := "_timeBuffer", ty := uint256 }]
    returnType := none
    body :=
      [ .require (.binary .eq sender (.storage ownerRef)),
        .assign timeBufferRef (.var "_timeBuffer") ] }

/-- `setReservePrice(uint256)` — onlyOwner. -/
def setReservePriceTransition : TransitionDecl :=
  { name := "setReservePrice"
    params := [{ name := "_reservePrice", ty := uint256 }]
    returnType := none
    body :=
      [ .require (.binary .eq sender (.storage ownerRef)),
        .assign reservePriceRef (.var "_reservePrice") ] }

/-- `setMinBidIncrementPercentage(uint8)` — onlyOwner. -/
def setMinBidIncTransition : TransitionDecl :=
  { name := "setMinBidIncrementPercentage"
    params := [{ name := "_minBidIncrementPercentage", ty := uint8 }]
    returnType := none
    body :=
      [ .require (.binary .eq sender (.storage ownerRef)),
        .assign minBidIncRef (.var "_minBidIncrementPercentage") ] }

/-- `initialize(...)` — modelled as the constructor (sets config, owner = msg.sender, paused). -/
def constructorDecl : ConstructorDecl :=
  { params :=
      [ { name := "_nouns", ty := addr }, { name := "_weth", ty := addr },
        { name := "_timeBuffer", ty := uint256 }, { name := "_reservePrice", ty := uint256 },
        { name := "_minBidIncrementPercentage", ty := uint8 }, { name := "_duration", ty := uint256 } ]
    body :=
      [ .assign ownerRef sender,
        .assign nounsRef (.var "_nouns"),
        .assign wethRef (.var "_weth"),
        .assign timeBufferRef (.var "_timeBuffer"),
        .assign reservePriceRef (.var "_reservePrice"),
        .assign minBidIncRef (.var "_minBidIncrementPercentage"),
        .assign durationRef (.var "_duration"),
        .assign pausedRef (.boolLit true) ] }

def auctionContract : ContractDecl :=
  { name := "NounsAuctionHouse"
    storage := storageDecls
    ctor := constructorDecl
    structs := [auctionStructDecl]
    functions := [safeTransferETHWithFallback, settleAuctionFn, createAuctionFn]
    transitions :=
      [ createBidTransition, settleAndCreateTransition, settleAuctionTransition,
        pauseTransition, unpauseTransition, setTimeBufferTransition,
        setReservePriceTransition, setMinBidIncTransition ] }

/-! ## Config (sketch — refine `encode?` and the layout when proving) -/

def auctionStorageLayout : StorageLayout where
  layout :=
    match genSolidityLayout [] storageDecls with
    | some layout => layout
    | none => fun _ => none

/-- External-call ABI: `mint` returns a `uint256`; the other callees (`burn`/`transferFrom`/
    `deposit`/`transfer`) are treated as void here (return `unit`), so `externalCall` succeeds with a
    dummy bound value.  `encode?` is a placeholder pending the per-callee selector encodings. -/
def auctionExternalABI : ExternalCallABI where
  encode? := fun _ _ => some ByteArray.empty
  decode? := fun name out => if name = "mint" then defaultDecodeReturn? name out else some .unit

end Auction

def auctionConfig : Config :=
  { storage := Auction.auctionStorageLayout
    externalABI := Auction.auctionExternalABI }
