import Solm.Semantics
import Solm.SolidityLayout

/-!
# BlindAuction — Solm specification for `BlindAuction.sol`

A faithful (events-aside) Solm spec of the Solidity `BlindAuction` example.

Notable Solm features exercised:

* a **`mapping(address => Bid[])`** (`bids`) — a mapping whose values are *dynamic arrays of
  structs* — grown with `push` of a struct literal (`bid`);
* the `Bid { bytes32 blindedBid; uint deposit; }` struct, and a storage alias into one array
  element (`Bid storage bidToCheck = bids[msg.sender][i]`) via `letStorage`;
* the low-level value send `payable(addr).call{value: v}("")` (`lowLevelCall`) in `withdraw`,
  `reveal`, and the pay-or-revert `auctionEnd`;
* the modifiers `onlyBefore`/`onlyAfter` inlined as `require`, and `if (cond) revert E();` as
  `require (¬cond)` (the custom-error payloads are dropped — the spec tracks storage and return
  values only);
* an **internal** helper `placeBid` (`FunctionDecl`, returns `bool`);
* the solc-generated public getters, including the two-key `bids(address,uint256)` array getter;
* the `reveal` hash check `bidToCheck.blindedBid != keccak256(abi.encodePacked(value, fake, secret))`,
  using the **`keccak256`** and **`abiEncodePacked`** `Expr` nodes (`Solm/Syntax.lean`).  The spec
  `keccak256` evaluates to the same `ffi.KEC` the EVM's `KECCAK256` opcode uses, so runtime-equivalence
  reduces to equality of the hashed bytes — i.e. that our packed encoding matches what solc lays out
  in memory before hashing.

The storage layout is **hand-written** to match the deployed bytecode (the nested
`mapping → Bid[] → struct` defeats `genSolidityLayout`); the (empty) external ABI is the generic
default.
-/

open Solm ABI

namespace BlindAuction

/-! ## Types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)
def addr    : ABIType := .elem .address
def boolTy  : ABIType := .elem .bool
/-- `bytes32` is the ABI fixed-bytes of width 32 (`ElemType.bytes` stores `n` with width `n+1`). -/
def bytes32 : ABIType := .elem (.bytes ⟨31, by decide⟩)

def uint256St : StorageType := .elem (.int uint256Int)
def addrSt    : StorageType := .elem .address
def boolSt    : StorageType := .elem .bool
def bytes32St : StorageType := .elem (.bytes ⟨31, by decide⟩)

/-! ## Expression / ref helpers -/

def sender : Expr := .env .caller
def now : Expr := .env .timestamp
/-- `address(0)`. -/
def zeroAddr : Expr := .cast (.intLit 0) addrSt
/-- Pin a value into the `uint256` range (models solc's *checked* arithmetic: reverts on overflow). -/
def u256 (e : Expr) : Expr := .inRange uint256Int e

def beneficiaryRef   : StorageRef := { base := "beneficiary" }
def biddingEndRef    : StorageRef := { base := "biddingEnd" }
def revealEndRef     : StorageRef := { base := "revealEnd" }
def endedRef         : StorageRef := { base := "ended" }
def highestBidderRef : StorageRef := { base := "highestBidder" }
def highestBidRef    : StorageRef := { base := "highestBid" }
/-- `pendingReturns[a]`. -/
def pendingReturnsRef (a : Expr) : StorageRef := { base := "pendingReturns", steps := [.mindex a] }
/-- `bids[a]` — the dynamic array of `Bid`s for `a`. -/
def bidsRef (a : Expr) : StorageRef := { base := "bids", steps := [.mindex a] }
/-- A field of `bids[a][i]`. -/
def bidF (a i : Expr) (f : Ident) : StorageRef :=
  { base := "bids", steps := [.mindex a, .aindex i, .field f] }
/-- A field of the storage alias `name` (e.g. `bidToCheck.blindedBid`). -/
def aliasF (name : Ident) (f : Ident) : StorageRef := { base := name, steps := [.field f] }

/-! ## Storage declarations + struct schema -/

def bidStructTy : StorageType :=
  .struct "Bid" [ ("blindedBid", bytes32St), ("deposit", uint256St) ]

def bidStructDecl : StructDecl :=
  { name := "Bid"
    fields := [ { name := "blindedBid", ty := bytes32St }, { name := "deposit", ty := uint256St } ] }

def storageDecls : List StorageDecl :=
  [ { name := "beneficiary", ty := addrSt },
    { name := "biddingEnd", ty := uint256St },
    { name := "revealEnd", ty := uint256St },
    { name := "ended", ty := boolSt },
    { name := "bids", ty := .mapping .address (.dynamicArray bidStructTy) },
    { name := "highestBidder", ty := addrSt },
    { name := "highestBid", ty := uint256St },
    { name := "pendingReturns", ty := .mapping .address uint256St } ]

/-! ## Constructor

`constructor(uint biddingTime, uint revealTime, address payable beneficiaryAddress)`.
-/
def constructorDecl : ConstructorDecl :=
  { params :=
      [ { name := "biddingTime", ty := uint256 },
        { name := "revealTime", ty := uint256 },
        { name := "beneficiaryAddress", ty := addr } ]
    body :=
      [ .assign .storage beneficiaryRef (.var "beneficiaryAddress"),
        .assign .storage biddingEndRef (u256 (.binary .add now (.var "biddingTime"))),
        .assign .storage revealEndRef
          (u256 (.binary .add (.storage biddingEndRef) (.var "revealTime"))) ] }

/-! ## Internal helper -/

/-- `placeBid(address bidder, uint value) internal returns (bool)` — promote a revealed bid to the
    new high bid, queueing the prior leader's funds for withdrawal. -/
def placeBidFn : FunctionDecl :=
  { name := "placeBid"
    params := [{ name := "bidder", ty := addr }, { name := "value", ty := uint256 }]
    returnType := some boolTy
    body :=
      [ .ite (.binary .le (.var "value") (.storage highestBidRef))
          [ .return (.boolLit false) ] [],
        .ite (.binary .ne (.storage highestBidderRef) zeroAddr)
          [ .assign .storage (pendingReturnsRef (.storage highestBidderRef))
              (u256 (.binary .add
                (.storage (pendingReturnsRef (.storage highestBidderRef)))
                (.storage highestBidRef))) ]
          [],
        .assign .storage highestBidRef (.var "value"),
        .assign .storage highestBidderRef (.var "bidder"),
        .return (.boolLit true) ] }

/-! ## Transitions -/

/-- `bid(bytes32 blindedBid) external payable onlyBefore(biddingEnd)` — queue a blinded bid. -/
def bidTransition : TransitionDecl :=
  { name := "bid"
    params := [{ name := "blindedBid", ty := bytes32 }]
    returnType := none
    body :=
      -- `onlyBefore(biddingEnd)`: `if (block.timestamp >= biddingEnd) revert TooLate(biddingEnd);`
      [ .require (.binary .lt now (.storage biddingEndRef)),
        .push (bidsRef sender)
          (some (.structLit "Bid"
            [ ("blindedBid", .var "blindedBid"), ("deposit", .env .callvalue) ])) ] }

/-- A field of the array element `bids[a][i]` is reached through `[.mindex a, .aindex i]`; the alias
    `bidToCheck` below is bound to that element with `letStorage`. -/
def bidElemRef (a i : Expr) : StorageRef := { base := "bids", steps := [.mindex a, .aindex i] }

/-- `reveal(uint[] calldata values, bool[] calldata fakes, bytes32[] calldata secrets) external`
    — reveal each blinded bid, refunding deposits and promoting the highest valid bid.

    The per-entry guard `bidToCheck.blindedBid != keccak256(abi.encodePacked(value, fake, secret))`
    now uses the `keccak256` / `abiEncodePacked` expression nodes; the packed encoding of
    `(uint256, bool, bytes32)` is `32 + 1 + 32 = 65` bytes, matching solc's `abi.encodePacked`. -/
def revealTransition : TransitionDecl :=
  { name := "reveal"
    params := [ { name := "values",  ty := .dynamicArray uint256 },
                { name := "fakes",   ty := .dynamicArray boolTy },
                { name := "secrets", ty := .dynamicArray bytes32 } ]
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        -- `onlyAfter(biddingEnd)`; `onlyBefore(revealEnd)`
        .require (.binary .gt now (.storage biddingEndRef)),
        .require (.binary .lt now (.storage revealEndRef)),
        .letDecl "length" (some uint256) (.arrayLength .storage (bidsRef sender)),
        .require (.binary .eq (.arrayLength .localVar { base := "values" })  (.var "length")),
        .require (.binary .eq (.arrayLength .localVar { base := "fakes" })   (.var "length")),
        .require (.binary .eq (.arrayLength .localVar { base := "secrets" }) (.var "length")),
        .letDecl "refund" (some uint256) (.intLit 0),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ -- `Bid storage bidToCheck = bids[msg.sender][i];`
            .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value"  (some uint256)  (.index (.var "values")  (.var "i")),
            .letDecl "fake"   (some boolTy)   (.index (.var "fakes")   (.var "i")),
            .letDecl "secret" (some bytes32)  (.index (.var "secrets") (.var "i")),
            -- `if (bidToCheck.blindedBid != keccak256(abi.encodePacked(value, fake, secret))) continue;`
            .ite (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                    (.keccak256 (.abiEncodePacked
                      [ (uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret") ])))
              [ .continue ] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite (.binary .and (.unary .not (.var "fake"))
                               (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ]
              [],
            -- `bidToCheck.blindedBid = bytes32(0);`
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ],
        .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ] }

/-- `withdraw() external` — refund a previously overbid amount (revert on a failed send). -/
def withdrawTransition : TransitionDecl :=
  { name := "withdraw"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "amount" (some uint256) (.storage (pendingReturnsRef sender)),
        .ite (.binary .gt (.var "amount") (.intLit 0))
          [ .assign .storage (pendingReturnsRef sender) (.intLit 0),
            .lowLevelCall sender (.var "amount") (.newBytes (.intLit 0)) "success" "_data",
            .require (.var "success") ]
          [] ] }

/-- `auctionEnd() external onlyAfter(revealEnd)` — mark ended and pay the beneficiary. -/
def auctionEndTransition : TransitionDecl :=
  { name := "auctionEnd"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        -- `onlyAfter(revealEnd)`: `if (block.timestamp <= revealEnd) revert TooEarly(revealEnd);`
        .require (.binary .gt now (.storage revealEndRef)),
        -- `if (ended) revert AuctionEndAlreadyCalled();`
        .require (.unary .not (.storage endedRef)),
        .assign .storage endedRef (.boolLit true),
        .lowLevelCall (.storage beneficiaryRef) (.storage highestBidRef)
          (.newBytes (.intLit 0)) "success" "_data",
        .require (.var "success") ] }

/-! ## Transitions — auto-generated public getters -/

def beneficiaryGetter : TransitionDecl :=
  { name := "beneficiary", params := [], returnType := some addr
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage beneficiaryRef) ] }

def biddingEndGetter : TransitionDecl :=
  { name := "biddingEnd", params := [], returnType := some uint256
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage biddingEndRef) ] }

def revealEndGetter : TransitionDecl :=
  { name := "revealEnd", params := [], returnType := some uint256
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage revealEndRef) ] }

def endedGetter : TransitionDecl :=
  { name := "ended", params := [], returnType := some boolTy
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage endedRef) ] }

def highestBidderGetter : TransitionDecl :=
  { name := "highestBidder", params := [], returnType := some addr
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage highestBidderRef) ] }

def highestBidGetter : TransitionDecl :=
  { name := "highestBid", params := [], returnType := some uint256
    body := [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
              .return (.storage highestBidRef) ] }

/-- `bids(address, uint256) view returns (bytes32 blindedBid, uint256 deposit)` — the two-key getter
    solc generates for the public `mapping(address => Bid[])`. -/
def bidsGetter : TransitionDecl :=
  { name := "bids"
    params := [{ name := "a", ty := addr }, { name := "i", ty := uint256 }]
    returnType := some (.tuple [bytes32, uint256])
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.tupleLit
          [ .storage (bidF (.var "a") (.var "i") "blindedBid"),
            .storage (bidF (.var "a") (.var "i") "deposit") ]) ] }

/-! ## Contract + config -/

def blindAuctionContract : ContractDecl :=
  { name := "BlindAuction"
    storage := storageDecls
    ctor := constructorDecl
    structs := [bidStructDecl]
    functions := [placeBidFn]
    transitions :=
      [ bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
        beneficiaryGetter, biddingEndGetter, revealEndGetter, endedGetter,
        highestBidderGetter, highestBidGetter, bidsGetter ] }

/-! ## Hand-written storage layout

`genSolidityLayout`'s nested `mapping → dynamic-array → struct` handling is still WIP, so the layout is
written by hand to match the deployed bytecode (as `Ballot` does).  Solidity's standard layout:
scalars at their declaration slots (`beneficiary`@0 … `pendingReturns`@7), `ended` packed at slot 3
byte offset 0; a mapping entry `m[k]` at `keccak256(k ‖ baseSlot)`; and the dynamic array `bids[a]`
keeps its **length** at its base slot `M = keccak256(a ‖ 4)` with elements (each `Bid` = two words) at
`keccak256(M) + 2·i` (`.blindedBid` at `+0`, `.deposit` at `+1`).
-/

def blindAuctionUint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def blindAuctionAddrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def blindAuctionBoolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def blindAuctionBytes32Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .bytes ⟨31, by decide⟩ }

def blindAuctionMappingSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

/-- Base slot of `bids[a]` (mapping at decl slot 4); the array **length** lives here. -/
def bidsBase (a : KeyValue) : Ethereum.UInt256 :=
  blindAuctionMappingSlot (keyValueToWord a) ⟨4⟩

/-- Slot of `bids[a][i]` — data region `keccak256(base)` plus `2·i` (each `Bid` is two words). -/
def bidsElemSlot (a i : KeyValue) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (bidsBase a).toByteArray)
    + Ethereum.UInt256.ofNat ((keyValueToWord i).toNat * 2)

def pendingReturnsSlot (a : KeyValue) : Ethereum.UInt256 :=
  blindAuctionMappingSlot (keyValueToWord a) ⟨7⟩

def blindAuctionStorageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "beneficiary", [] => some (blindAuctionAddrLoc ⟨0⟩)
    | "biddingEnd", [] => some (blindAuctionUint256Loc ⟨1⟩)
    | "revealEnd", [] => some (blindAuctionUint256Loc ⟨2⟩)
    | "ended", [] => some (blindAuctionBoolLoc ⟨3⟩)
    | "bids", [.mindex a, .length] => some (blindAuctionUint256Loc (bidsBase a))
    | "bids", [.mindex a, .aindex i, .field "blindedBid"] =>
        some (blindAuctionBytes32Loc (bidsElemSlot a i))
    | "bids", [.mindex a, .aindex i, .field "deposit"] =>
        some (blindAuctionUint256Loc (bidsElemSlot a i + ⟨1⟩))
    | "highestBidder", [] => some (blindAuctionAddrLoc ⟨5⟩)
    | "highestBid", [] => some (blindAuctionUint256Loc ⟨6⟩)
    | "pendingReturns", [.mindex a] => some (blindAuctionUint256Loc (pendingReturnsSlot a))
    | _, _ => none

end BlindAuction

def blindAuctionConfig : Config :=
  { storage := BlindAuction.blindAuctionStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment BlindAuction.blindAuctionContract.ctor.params }

@[simp] theorem blindAuctionConfig_storage_beneficiary :
    blindAuctionConfig.storage.layout { base := "beneficiary", steps := [] } =
      fun _ => some (BlindAuction.blindAuctionAddrLoc ⟨0⟩) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_biddingEnd :
    blindAuctionConfig.storage.layout { base := "biddingEnd", steps := [] } =
      fun _ => some (BlindAuction.blindAuctionUint256Loc ⟨1⟩) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_revealEnd :
    blindAuctionConfig.storage.layout { base := "revealEnd", steps := [] } =
      fun _ => some (BlindAuction.blindAuctionUint256Loc ⟨2⟩) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_ended :
    blindAuctionConfig.storage.layout { base := "ended", steps := [] } =
      fun _ => some (BlindAuction.blindAuctionBoolLoc ⟨3⟩) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_bids_length (a : KeyValue) :
    blindAuctionConfig.storage.layout { base := "bids", steps := [.mindex a, .length] } =
      fun _ => some (BlindAuction.blindAuctionUint256Loc (BlindAuction.bidsBase a)) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_bids_blindedBid (a i : KeyValue) :
    blindAuctionConfig.storage.layout
        { base := "bids", steps := [.mindex a, .aindex i, .field "blindedBid"] } =
      fun _ => some (BlindAuction.blindAuctionBytes32Loc (BlindAuction.bidsElemSlot a i)) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_bids_deposit (a i : KeyValue) :
    blindAuctionConfig.storage.layout
        { base := "bids", steps := [.mindex a, .aindex i, .field "deposit"] } =
      fun _ => some (BlindAuction.blindAuctionUint256Loc (BlindAuction.bidsElemSlot a i + ⟨1⟩)) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_highestBidder :
    blindAuctionConfig.storage.layout { base := "highestBidder", steps := [] } =
      fun _ => some (BlindAuction.blindAuctionAddrLoc ⟨5⟩) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_highestBid :
    blindAuctionConfig.storage.layout { base := "highestBid", steps := [] } =
      fun _ => some (BlindAuction.blindAuctionUint256Loc ⟨6⟩) :=
  rfl

@[simp] theorem blindAuctionConfig_storage_pendingReturns (a : KeyValue) :
    blindAuctionConfig.storage.layout { base := "pendingReturns", steps := [.mindex a] } =
      fun _ => some (BlindAuction.blindAuctionUint256Loc (BlindAuction.pendingReturnsSlot a)) :=
  rfl
