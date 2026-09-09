import ABI.Encode
import Solm.Semantics
import Solm.SolidityLayout

/-!
# Auction — Solm specification for Nouns' `NounsAuctionHouse.sol`

A faithful, events-aside Solm spec of the Nouns auction house.  The OpenZeppelin
upgradeable bases are flattened into the storage cells and modifier code that
the compiled runtime observes: `Initializable`, `PausableUpgradeable`,
`ReentrancyGuardUpgradeable`, and `OwnableUpgradeable`.

The remaining intentional abstraction is Solm's low-level call form, which does
not currently expose the ETH-transfer gas stipend.  The call itself, value, data,
success/failure branch, and WETH fallback calldata are modeled explicitly.
-/

open Solm ABI

namespace Auction

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)
def uint8 : ABIType := .elem (.int uint8Int)
def boolTy : ABIType := .elem .bool
def addr : ABIType := .elem .address

def uint256St : StorageType := .elem (.int uint256Int)
def uint8St : StorageType := .elem (.int uint8Int)
def addrSt : StorageType := .elem .address
def boolSt : StorageType := .elem .bool
def gap49St : StorageType := .array uint256St 49
def gap50St : StorageType := .array uint256St 50

/-! ## Expression / ref helpers -/

def sender : Expr := .env .caller
def now : Expr := .env .timestamp
/-- `address(0)`. -/
def zeroAddr : Expr := .cast (.intLit 0) addrSt
/-- Pin a value into the `uint256` range (models non-wrapping solc arithmetic). -/
def u256 (e : Expr) : Expr := .inRange uint256Int e
/-- `keccak256("Error(string)")[:4]`. -/
def errorStringSelector : ByteArray := ⟨#[0x08, 0xc3, 0x79, 0xa0]⟩

def nonpayable : Stmt := .require (.binary .eq (.env .callvalue) (.intLit 0))

def localBytesLength (name : Ident) : Expr :=
  .arrayLength .localVar { base := name }

def errorStringPayload (name : Ident) : Expr :=
  .bytesSlice (.var name) (.intLit 4) (localBytesLength name)

def errorStringReturndataLongEnough (name : Ident) : Expr :=
  .binary .ge (localBytesLength name) (.intLit 68)

def solcMaxU64Expr : Expr :=
  .intLit (Int.ofNat ABI.solcMaxU64)

def errorStringOffsetDecode (name : Ident) : Expr :=
  .abiDecode uint256 (errorStringPayload name)

def errorStringOffsetInBounds (name offsetName : Ident) : Expr :=
  .binary .le (.binary .add (.var offsetName) (.intLit 36)) (localBytesLength name)

def errorStringLengthWord (name offsetName : Ident) : Expr :=
  .bytesSlice (errorStringPayload name) (.var offsetName)
    (.binary .add (.var offsetName) (.intLit 32))

def errorStringLengthDecode (name offsetName : Ident) : Expr :=
  .abiDecode uint256 (errorStringLengthWord name offsetName)

def errorStringPayloadInBounds (name offsetName lengthName : Ident) : Expr :=
  .binary .le
    (.binary .add (.binary .add (.var offsetName) (.var lengthName)) (.intLit 36))
    (localBytesLength name)

def solcWordAlignMaskExpr : Expr :=
  .intLit (Int.ofNat (Ethereum.UInt256.size - 32))

def errorStringRoundedAllocSize (offset length : Expr) : Expr :=
  .binary .bitAnd solcWordAlignMaskExpr
    (.binary .add (.binary .add (.binary .add offset length) (.intLit 32)) (.intLit 31))

def errorStringNewFreePtr (offsetName lengthName : Ident)
    (freePtr : Expr := .intLit 128) : Expr :=
  .binary .add freePtr
    (errorStringRoundedAllocSize (.var offsetName) (.var lengthName))

def errorStringAllocationWithinU64 (offsetName lengthName : Ident)
    (freePtr : Expr := .intLit 128) : Expr :=
  .binary .le (errorStringNewFreePtr offsetName lengthName freePtr) solcMaxU64Expr

def errorStringAllocationNoWrap (offsetName lengthName : Ident)
    (freePtr : Expr := .intLit 128) : Expr :=
  .binary .ge (errorStringNewFreePtr offsetName lengthName freePtr) freePtr

def initializedRef : StorageRef := { base := "_initialized" }
def initializingRef : StorageRef := { base := "_initializing" }
def pausedRef : StorageRef := { base := "_paused" }
def statusRef : StorageRef := { base := "_status" }
def ownerRef : StorageRef := { base := "_owner" }

def nounsRef : StorageRef := { base := "nouns" }
def wethRef : StorageRef := { base := "weth" }
def timeBufferRef : StorageRef := { base := "timeBuffer" }
def reservePriceRef : StorageRef := { base := "reservePrice" }
def minBidIncRef : StorageRef := { base := "minBidIncrementPercentage" }
def durationRef : StorageRef := { base := "duration" }
def auctionRef : StorageRef := { base := "auction" }
/-- A field of the single `auction` storage struct. -/
def aField (f : Ident) : StorageRef := { base := "auction", steps := [.field f] }

def auctionMemField (f : Ident) : Expr := .field (.var "_auction") f

def notEntered : Expr := .intLit 1
def entered : Expr := .intLit 2

def checkedExternalCallStmts (receiver : Expr) (name : Ident) (eth : Expr)
    (args : List Expr) (retVar : Ident) (perm : Bool := true) : List Stmt :=
  [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
    .externalCall receiver name eth args retVar (perm := perm) ]

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
  [ -- InitializableUpgradeable in the 0.8.6-era OZ layout.
    { name := "_initialized", ty := boolSt },
    { name := "_initializing", ty := boolSt },
    -- ContextUpgradeable.
    { name := "__contextGap", ty := gap50St },
    -- PausableUpgradeable.
    { name := "_paused", ty := boolSt },
    { name := "__pausableGap", ty := gap49St },
    -- ReentrancyGuardUpgradeable.
    { name := "_status", ty := uint256St },
    { name := "__reentrancyGuardGap", ty := gap49St },
    -- OwnableUpgradeable.
    { name := "_owner", ty := addrSt },
    { name := "__ownableGap", ty := gap49St },
    -- NounsAuctionHouse.
    { name := "nouns", ty := addrSt },
    { name := "weth", ty := addrSt },
    { name := "timeBuffer", ty := uint256St },
    { name := "reservePrice", ty := uint256St },
    { name := "minBidIncrementPercentage", ty := uint8St },
    { name := "duration", ty := uint256St },
    { name := "auction", ty := auctionStructTy } ]

/-! ## Internal helpers -/

def safeTransferETHWithFallbackBody (onETHSuccess transfer : List Stmt) : List Stmt :=
      [ .lowLevelCall (.var "to") (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
        .ite (.unary .not (.var "success"))
          (checkedExternalCallStmts (.storage wethRef) "deposit" (.var "amount") [] "_dep" ++
            transfer)
          onETHSuccess ]

/-- `_safeTransferETHWithFallback(to, amount)`: raw value send; on failure wrap to WETH and transfer. -/
def safeTransferETHWithFallback : FunctionDecl :=
  { name := "_safeTransferETHWithFallback"
    params := [{ name := "to", ty := addr }, { name := "amount", ty := uint256 }]
    returnType := []
    body := safeTransferETHWithFallbackBody []
      [ .externalCall (.storage wethRef) "transfer" (.intLit 0)
          [.var "to", .var "amount"] "_xfer" ] }

def settleAuctionBody (payout : List Stmt) : List Stmt :=
      [ .letDecl "_auction" none (.storage auctionRef),
        .require (.binary .ne (auctionMemField "startTime") (.intLit 0)),
        .require (.unary .not (auctionMemField "settled")),
        .require (.binary .ge now (auctionMemField "endTime")),
        .assign .storage (aField "settled") (.boolLit true),
        .ite (.binary .eq (auctionMemField "bidder") zeroAddr)
          (checkedExternalCallStmts (.storage nounsRef) "burn" (.intLit 0)
            [auctionMemField "nounId"] "_burn")
          (checkedExternalCallStmts (.storage nounsRef) "transferFrom" (.intLit 0)
            [.env .this, auctionMemField "bidder", auctionMemField "nounId"] "_tf"),
        .ite (.binary .gt (auctionMemField "amount") (.intLit 0))
          payout [] ]

/-- `_settleAuction()`: snapshot the auction, settle it, burn/transfer the noun, and pay the owner. -/
def settleAuctionFn : FunctionDecl :=
  { name := "_settleAuction"
    params := []
    returnType := []
    body := settleAuctionBody
      [ .internalCall "_safeTransferETHWithFallback"
          [.storage ownerRef, auctionMemField "amount"] "_pay" ] }

def createAuctionBody (freePtr : Expr) : List Stmt :=
      [ .checkedCall (.storage nounsRef) "mint" (.intLit 0) [] "nounId"
          [ .letDecl "startTime" (some uint256) now,
            .letDecl "endTime" (some uint256)
              (u256 (.binary .add (.var "startTime") (.storage durationRef))),
            .assign .storage (aField "nounId") (.var "nounId"),
            .assign .storage (aField "amount") (.intLit 0),
            .assign .storage (aField "startTime") (.var "startTime"),
            .assign .storage (aField "endTime") (.var "endTime"),
            .assign .storage (aField "bidder") zeroAddr,
            .assign .storage (aField "settled") (.boolLit false) ]
          "err"
          [ .ite (.binary .eq (.bytesSlice (.var "err") (.intLit 0) (.intLit 4))
                              (.bytesLit errorStringSelector))
              [ .require (errorStringReturndataLongEnough "err"),
                .letDecl "_errOffset" (some uint256) (errorStringOffsetDecode "err"),
                .require (.binary .le (.var "_errOffset") solcMaxU64Expr),
                .require (errorStringOffsetInBounds "err" "_errOffset"),
                .letDecl "_errLength" (some uint256) (errorStringLengthDecode "err" "_errOffset"),
                .require (.binary .le (.var "_errLength") solcMaxU64Expr),
                .require (errorStringPayloadInBounds "err" "_errOffset" "_errLength"),
                .require (errorStringAllocationWithinU64 "_errOffset" "_errLength" freePtr),
                .require (errorStringAllocationNoWrap "_errOffset" "_errLength" freePtr),
                .letDecl "_errString" (some .string) (.abiDecode .string (errorStringPayload "err")),
                .require (.unary .not (.storage pausedRef)),
                .assign .storage pausedRef (.boolLit true) ]
              [ .require (.boolLit false) ] ] ]

/-- `_createAuction()`: `try nouns.mint()`; on `Error(string)` pause, on any other revert re-revert. -/
def createAuctionFn : FunctionDecl :=
  { name := "_createAuction"
    params := []
    returnType := []
    body := createAuctionBody (.intLit 128) }

-- The settlement-and-creation path must carry the compiler's free-memory pointer:
-- its auction snapshot reserves 192 bytes beyond the initial pointer of 128.
-- The empty payout buffer reserves another word, and returned bytes can advance
-- the pointer further. These internal results are bookkeeping only; the public
-- entry point still takes no arguments and returns no values.
def roundedMemoryAllocation (size : Expr) : Expr :=
  .binary .bitAnd solcWordAlignMaskExpr (.binary .add size (.intLit 31))

def payoutFreePtrAfterETH : Expr :=
  .ite (.binary .eq (localBytesLength "_data") (.intLit 0))
    (.intLit 352)
    (.binary .add (.intLit 352)
      (roundedMemoryAllocation (.binary .add (localBytesLength "_data") (.intLit 32))))

def safeTransferETHWithMemory : FunctionDecl :=
  { name := "_safeTransferETHWithMemory"
    params := safeTransferETHWithFallback.params
    returnType := [uint256]
    body := safeTransferETHWithFallbackBody
      [ .return [payoutFreePtrAfterETH] ]
      [ .lowLevelCall (.storage wethRef) (.intLit 0)
          (.abiEncodeCall "transfer" [.var "to", .var "amount"])
          "_xferSuccess" "_xferData",
        .require (.var "_xferSuccess"),
        .letDecl "_xfer" (some boolTy) (.abiDecode boolTy (.var "_xferData")),
        .return [.binary .add payoutFreePtrAfterETH
          (roundedMemoryAllocation (localBytesLength "_xferData"))] ] }

def settleAuctionWithMemoryFn : FunctionDecl :=
  { name := "_settleAuctionWithMemory"
    params := []
    returnType := [uint256]
    body := settleAuctionBody
      [ .internalCall "_safeTransferETHWithMemory"
          [.storage ownerRef, auctionMemField "amount"] "_pay",
        .return [.var "_pay"] ] ++
      [ .return [.intLit 320] ] }

def createAuctionWithMemoryFn : FunctionDecl :=
  { name := "_createAuctionWithMemory"
    params := [{ name := "_freePtr", ty := uint256 }]
    returnType := []
    body := createAuctionBody (.var "_freePtr") }

/-! ## Transitions -/

/-- `initialize(...)` — external initializer, not a constructor. -/
def initializeTransition : TransitionDecl :=
  { name := "initialize"
    params :=
      [ { name := "_nouns", ty := addr }, { name := "_weth", ty := addr },
        { name := "_timeBuffer", ty := uint256 }, { name := "_reservePrice", ty := uint256 },
        { name := "_minBidIncrementPercentage", ty := uint8 }, { name := "_duration", ty := uint256 } ]
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .or (.storage initializingRef)
          (.unary .not (.storage initializedRef))),
        .letDecl "isTopLevelCall" (some boolTy) (.unary .not (.storage initializingRef)),
        .ite (.var "isTopLevelCall")
          [ .assign .storage initializingRef (.boolLit true),
            .assign .storage initializedRef (.boolLit true) ]
          [],
        .assign .storage pausedRef (.boolLit false),
        .assign .storage statusRef notEntered,
        .assign .storage ownerRef sender,
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true),
        .assign .storage nounsRef (.var "_nouns"),
        .assign .storage wethRef (.var "_weth"),
        .assign .storage timeBufferRef (.var "_timeBuffer"),
        .assign .storage reservePriceRef (.var "_reservePrice"),
        .assign .storage minBidIncRef (.var "_minBidIncrementPercentage"),
        .assign .storage durationRef (.var "_duration"),
        .ite (.var "isTopLevelCall")
          [ .assign .storage initializingRef (.boolLit false) ]
          [] ] }

/-- `createBid(uint256 nounId)` — payable, nonReentrant. -/
def createBidTransition : TransitionDecl :=
  { name := "createBid"
    params := [{ name := "nounId", ty := uint256 }]
    returnType := []
    body :=
      [ .require (.binary .ne (.storage statusRef) entered),
        .assign .storage statusRef entered,
        .letDecl "_auction" none (.storage auctionRef),
        .require (.binary .eq (auctionMemField "nounId") (.var "nounId")),
        .require (.binary .lt now (auctionMemField "endTime")),
        .require (.binary .ge (.env .callvalue) (.storage reservePriceRef)),
        .require (.binary .ge (.env .callvalue)
          (u256 (.binary .add (auctionMemField "amount")
            (.binary .div (u256 (.binary .mul (auctionMemField "amount")
              (.storage minBidIncRef))) (.intLit 100))))),
        .letDecl "lastBidder" (some addr) (auctionMemField "bidder"),
        .ite (.binary .ne (.var "lastBidder") zeroAddr)
          [ .internalCall "_safeTransferETHWithFallback"
              [.var "lastBidder", auctionMemField "amount"] "_refund" ]
          [],
        .assign .storage (aField "amount") (.env .callvalue),
        .assign .storage (aField "bidder") sender,
        .letDecl "extended" (some boolTy)
          (.binary .lt (.binary .sub (auctionMemField "endTime") now) (.storage timeBufferRef)),
        .ite (.var "extended")
          [ .assign .storage (aField "endTime") (u256 (.binary .add now (.storage timeBufferRef))) ]
          [],
        .assign .storage statusRef notEntered ] }

/-- `settleCurrentAndCreateNewAuction()` — nonReentrant, whenNotPaused. -/
def settleAndCreateTransition : TransitionDecl :=
  { name := "settleCurrentAndCreateNewAuction"
    params := []
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .ne (.storage statusRef) entered),
        .assign .storage statusRef entered,
        .require (.unary .not (.storage pausedRef)),
        .internalCall "_settleAuctionWithMemory" [] "_s",
        .internalCall "_createAuctionWithMemory" [.var "_s"] "_c",
        .assign .storage statusRef notEntered ] }

/-- `settleAuction()` — whenPaused, nonReentrant. -/
def settleAuctionTransition : TransitionDecl :=
  { name := "settleAuction"
    params := []
    returnType := []
    body :=
      [ nonpayable,
        .require (.storage pausedRef),
        .require (.binary .ne (.storage statusRef) entered),
        .assign .storage statusRef entered,
        .internalCall "_settleAuction" [] "_s",
        .assign .storage statusRef notEntered ] }

/-- `pause()` — onlyOwner; `_pause()` includes `whenNotPaused`. -/
def pauseTransition : TransitionDecl :=
  { name := "pause"
    params := []
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .eq sender (.storage ownerRef)),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ] }

/-- `unpause()` — onlyOwner; `_unpause()` includes `whenPaused`. -/
def unpauseTransition : TransitionDecl :=
  { name := "unpause"
    params := []
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .eq sender (.storage ownerRef)),
        .require (.storage pausedRef),
        .assign .storage pausedRef (.boolLit false),
        .ite (.binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
                          (.storage (aField "settled")))
          [ .internalCall "_createAuction" [] "_c" ]
          [] ] }

/-- `setTimeBuffer(uint256)` — onlyOwner. -/
def setTimeBufferTransition : TransitionDecl :=
  { name := "setTimeBuffer"
    params := [{ name := "_timeBuffer", ty := uint256 }]
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .eq sender (.storage ownerRef)),
        .assign .storage timeBufferRef (.var "_timeBuffer") ] }

/-- `setReservePrice(uint256)` — onlyOwner. -/
def setReservePriceTransition : TransitionDecl :=
  { name := "setReservePrice"
    params := [{ name := "_reservePrice", ty := uint256 }]
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .eq sender (.storage ownerRef)),
        .assign .storage reservePriceRef (.var "_reservePrice") ] }

/-- `setMinBidIncrementPercentage(uint8)` — onlyOwner. -/
def setMinBidIncTransition : TransitionDecl :=
  { name := "setMinBidIncrementPercentage"
    params := [{ name := "_minBidIncrementPercentage", ty := uint8 }]
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .eq sender (.storage ownerRef)),
        .assign .storage minBidIncRef (.var "_minBidIncrementPercentage") ] }

/-- `transferOwnership(address newOwner)` — onlyOwner; reverts on the zero address. -/
def transferOwnershipTransition : TransitionDecl :=
  { name := "transferOwnership"
    params := [{ name := "newOwner", ty := addr }]
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .eq sender (.storage ownerRef)),
        .require (.binary .ne (.var "newOwner") zeroAddr),
        .assign .storage ownerRef (.var "newOwner") ] }

/-- `renounceOwnership()` — onlyOwner; sets the owner to `address(0)`. -/
def renounceOwnershipTransition : TransitionDecl :=
  { name := "renounceOwnership"
    params := []
    returnType := []
    body :=
      [ nonpayable,
        .require (.binary .eq sender (.storage ownerRef)),
        .assign .storage ownerRef zeroAddr ] }

/-! ## Public getters -/

def ownerGetter : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := [addr]
    body := [ nonpayable, .return [(.storage ownerRef)] ] }

def pausedGetter : TransitionDecl :=
  { name := "paused"
    params := []
    returnType := [boolTy]
    body := [ nonpayable, .return [(.storage pausedRef)] ] }

def nounsGetter : TransitionDecl :=
  { name := "nouns"
    params := []
    returnType := [addr]
    body := [ nonpayable, .return [(.storage nounsRef)] ] }

def wethGetter : TransitionDecl :=
  { name := "weth"
    params := []
    returnType := [addr]
    body := [ nonpayable, .return [(.storage wethRef)] ] }

def timeBufferGetter : TransitionDecl :=
  { name := "timeBuffer"
    params := []
    returnType := [uint256]
    body := [ nonpayable, .return [(.storage timeBufferRef)] ] }

def reservePriceGetter : TransitionDecl :=
  { name := "reservePrice"
    params := []
    returnType := [uint256]
    body := [ nonpayable, .return [(.storage reservePriceRef)] ] }

def minBidIncGetter : TransitionDecl :=
  { name := "minBidIncrementPercentage"
    params := []
    returnType := [uint8]
    body := [ nonpayable, .return [(.storage minBidIncRef)] ] }

def durationGetter : TransitionDecl :=
  { name := "duration"
    params := []
    returnType := [uint256]
    body := [ nonpayable, .return [(.storage durationRef)] ] }

def auctionGetter : TransitionDecl :=
  { name := "auction"
    params := []
    returnType := [uint256, uint256, uint256, uint256, addr, boolTy]
    body :=
      [ nonpayable,
        .return
          [ .storage (aField "nounId"),
            .storage (aField "amount"),
            .storage (aField "startTime"),
            .storage (aField "endTime"),
            .storage (aField "bidder"),
            .storage (aField "settled") ] ] }

/-! ## Contract and runtime ABI -/

def constructorDecl : ConstructorDecl :=
  { params := []
    body := [nonpayable] }

def auctionContract : ContractDecl :=
  { name := "NounsAuctionHouse"
    storage := storageDecls
    ctor := constructorDecl
    structs := [auctionStructDecl]
    functions := [safeTransferETHWithFallback, settleAuctionFn, createAuctionFn,
      safeTransferETHWithMemory, settleAuctionWithMemoryFn, createAuctionWithMemoryFn]
    transitions :=
      [ initializeTransition,
        createBidTransition, settleAndCreateTransition, settleAuctionTransition,
        pauseTransition, unpauseTransition, setTimeBufferTransition,
        setReservePriceTransition, setMinBidIncTransition,
        transferOwnershipTransition, renounceOwnershipTransition,
        ownerGetter, pausedGetter, nounsGetter, wethGetter, timeBufferGetter,
        reservePriceGetter, minBidIncGetter, durationGetter, auctionGetter ] }

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩

def mintSelector : ByteArray := selectorBytes 0x12 0x49 0xc5 0x8b
def burnSelector : ByteArray := selectorBytes 0x42 0x96 0x6c 0x68
def transferFromSelector : ByteArray := selectorBytes 0x23 0xb8 0x72 0xdd
def depositSelector : ByteArray := selectorBytes 0xd0 0xe3 0x0d 0xb0
def transferSelector : ByteArray := selectorBytes 0xa9 0x05 0x9c 0xbb

def encodeCallWithSelector? (sel : ByteArray) (tys : List ABIType) (args : List Value) :
    Option EVM.Bytes := do
  let payload <- ABI.encodeABIValues? tys args
  some (sel ++ payload.toByteArray)

def isVoidExternal (name : Ident) : Bool :=
  if name = "burn" then true
  else if name = "transferFrom" then true
  else if name = "deposit" then true
  else false

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValue? ty out).map (fun v => [v])

def decodeVoid? (_out : EVM.Bytes) : Option (List Value) :=
  some []

/-! ## Hand-written storage layout

The Auction runtime is compiled against upgradeable OpenZeppelin bases.  Their
reserved gaps are bytecode-visible because they push the child fields far down
in storage:

* `InitializableUpgradeable`: `_initialized`/`_initializing` packed in slot 0.
* `ContextUpgradeable`: 50-word gap at slots 1..50.
* `PausableUpgradeable`: `_paused` at slot 51, then a 49-word gap.
* `ReentrancyGuardUpgradeable`: `_status` at slot 101, then a 49-word gap.
* `OwnableUpgradeable`: `_owner` at slot 151, then a 49-word gap.
* `NounsAuctionHouse`: child fields start at slot 201.
-/

def auctionUint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def auctionUint8LocAt (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int uint8Int }

def auctionAddrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def auctionBoolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def auctionBoolLocAt (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .bool }

def auctionStorageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_initialized", [] => some (auctionBoolLoc ⟨0⟩)
    | "_initializing", [] => some (auctionBoolLocAt ⟨0⟩ 1)
    | "_paused", [] => some (auctionBoolLoc ⟨51⟩)
    | "_status", [] => some (auctionUint256Loc ⟨101⟩)
    | "_owner", [] => some (auctionAddrLoc ⟨151⟩)
    | "nouns", [] => some (auctionAddrLoc ⟨201⟩)
    | "weth", [] => some (auctionAddrLoc ⟨202⟩)
    | "timeBuffer", [] => some (auctionUint256Loc ⟨203⟩)
    | "reservePrice", [] => some (auctionUint256Loc ⟨204⟩)
    | "minBidIncrementPercentage", [] => some (auctionUint8LocAt ⟨205⟩ 0)
    | "duration", [] => some (auctionUint256Loc ⟨206⟩)
    | "auction", [.field "nounId"] => some (auctionUint256Loc ⟨207⟩)
    | "auction", [.field "amount"] => some (auctionUint256Loc ⟨208⟩)
    | "auction", [.field "startTime"] => some (auctionUint256Loc ⟨209⟩)
    | "auction", [.field "endTime"] => some (auctionUint256Loc ⟨210⟩)
    | "auction", [.field "bidder"] => some (auctionAddrLoc ⟨211⟩)
    | "auction", [.field "settled"] => some (auctionBoolLocAt ⟨211⟩ 20)
    | _, _ => none

/-- External-call ABI for the token/WETH calls made by the runtime. -/
def auctionExternalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "mint" then
      match args with
      | [] => some mintSelector
      | _ => none
    else if name = "burn" then
      encodeCallWithSelector? burnSelector [uint256] args
    else if name = "transferFrom" then
      encodeCallWithSelector? transferFromSelector [addr, addr, uint256] args
    else if name = "deposit" then
      match args with
      | [] => some depositSelector
      | _ => none
    else if name = "transfer" then
      encodeCallWithSelector? transferSelector [addr, uint256] args
    else
      none
  decode? := fun name out =>
    if name = "mint" then decodeReturn? uint256 out
    else if name = "transfer" then decodeReturn? boolTy out
    else if isVoidExternal name then decodeVoid? out
    else none

end Auction

def auctionConfig : Config :=
  { storage := Auction.auctionStorageLayout
    externalABI := Auction.auctionExternalABI
    selfDeployment := genSolidityConstructorDeployment Auction.auctionContract.ctor.params }
