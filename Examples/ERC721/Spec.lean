import Solm.Semantics
import Solm.SolidityLayout

/-!
# ERC721 — Solm specification for `ERC721.sol`

A faithful (events-aside) Solm spec of a Solmate-style **ERC721 core**: the IERC721
transfer/approval/ownership surface over four mappings.

Deliberately **out of scope** (see `ERC721.sol` header) and therefore not modelled here:
* the metadata extension (`name`/`symbol`/`tokenURI`) — `string` ABI returns aren't encodable yet;
* `safeTransferFrom` — its body needs `to.code.length` (EXTCODESIZE), not yet expressible in Solm;
* ERC165 `supportsInterface(bytes4)` — needs a fixed-bytes literal compare.

Storage (all four are mappings; each value occupies a full slot):

| variable           | decl slot | value slot                              | type |
|--------------------|-----------|-----------------------------------------|------|
| `_ownerOf`         | 0         | `keccak256(id ‖ 0)`                      | address |
| `_balanceOf`       | 1         | `keccak256(owner ‖ 1)`                   | uint256 |
| `getApproved`      | 2         | `keccak256(id ‖ 2)`                      | address |
| `isApprovedForAll` | 3         | `keccak256(operator ‖ keccak256(owner ‖ 3))` | bool |

As in ERC20/Ballot the layout is **hand-written** to match the deployed bytecode's slots exactly.
This is spec-level data only; bytecode/jump facts live in `Bytecode.lean`, proofs in the per-function
files / `Correct.lean`.
-/

open Solm ABI

namespace ERC721

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
/-- `address(0)`. -/
def zeroAddr : Expr := .cast (.intLit 0) addrSt

def ownerOfRef (id : Expr) : StorageRef := { base := "_ownerOf", steps := [.mindex id] }
def balanceOfRef (a : Expr) : StorageRef := { base := "_balanceOf", steps := [.mindex a] }
def getApprovedRef (id : Expr) : StorageRef := { base := "getApproved", steps := [.mindex id] }
def isApprovedForAllRef (owner operator : Expr) : StorageRef :=
  { base := "isApprovedForAll", steps := [.mindex owner, .mindex operator] }

/-! ## Storage declarations -/

def erc721StorageDecls : List StorageDecl :=
  [ { name := "_ownerOf", ty := .mapping (.int uint256Int) addrSt },
    { name := "_balanceOf", ty := .mapping .address uint256St },
    { name := "getApproved", ty := .mapping (.int uint256Int) addrSt },
    { name := "isApprovedForAll", ty := .mapping .address (.mapping .address boolSt) } ]

/-! ## Storage layout (hand-written, matches deployed bytecode) -/

/-- Solidity mapping slot: `keccak256(key ‖ baseSlot)`. -/
def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def ownerOfSlot (id : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord id) ⟨0⟩
def balanceOfSlot (a : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord a) ⟨1⟩
def getApprovedSlot (id : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord id) ⟨2⟩
def isApprovedForAllSlot (owner operator : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord operator) (mapSlot (keyValueToWord owner) ⟨3⟩)

/-- A full-word `uint256` storage location. -/
def wordLoc (s : Ethereum.UInt256) : StorageLoc :=
  { slot := s, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }
/-- A mapping-value `address` storage location (low 20 bytes of the slot). -/
def addrLoc (s : Ethereum.UInt256) : StorageLoc :=
  { slot := s, offset := 0, size := 20, hbound := by decide, type := .address }
/-- A mapping-value `bool` storage location. -/
def boolLoc (s : Ethereum.UInt256) : StorageLoc :=
  { slot := s, offset := 0, size := 1, hbound := by decide, type := .bool }

def erc721StorageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_ownerOf", [.mindex id]    => some (addrLoc (ownerOfSlot id))
    | "_balanceOf", [.mindex a]   => some (wordLoc (balanceOfSlot a))
    | "getApproved", [.mindex id] => some (addrLoc (getApprovedSlot id))
    | "isApprovedForAll", [.mindex owner, .mindex operator] =>
        some (boolLoc (isApprovedForAllSlot owner operator))
    | _, _ => none

/-! ## Transitions -/

/-- `ownerOf(uint256 id) view returns (address)` — reverts `NOT_MINTED` for the zero owner. -/
def ownerOfTransition : TransitionDecl :=
  { name := "ownerOf"
    params := [{ name := "id", ty := uint256 }]
    returnType := some addr
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "owner" (some addr) (.storage (ownerOfRef (.var "id"))),
        .require (.binary .ne (.var "owner") zeroAddr),
        .return (.var "owner") ] }

/-- `balanceOf(address owner) view returns (uint256)` — reverts `ZERO_ADDRESS`. -/
def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .ne (.var "owner") zeroAddr),
        .return (.storage (balanceOfRef (.var "owner"))) ] }

/-- `approve(address spender, uint256 id)` — owner or operator may approve. -/
def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "id", ty := uint256 }]
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "owner" (some addr) (.storage (ownerOfRef (.var "id"))),
        .require (.binary .or
          (.binary .eq sender (.var "owner"))
          (.storage (isApprovedForAllRef (.var "owner") sender))),
        .assign .storage (getApprovedRef (.var "id")) (.var "spender") ] }

/-- `setApprovalForAll(address operator, bool approved)`. -/
def setApprovalForAllTransition : TransitionDecl :=
  { name := "setApprovalForAll"
    params := [{ name := "operator", ty := addr }, { name := "approved", ty := boolTy }]
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (isApprovedForAllRef sender (.var "operator")) (.var "approved") ] }

/-- `transferFrom(address from, address to, uint256 id)` — checks ownership/recipient/authorization,
    then moves the token (`unchecked` balance dec/inc, matching solc). -/
def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "from", ty := addr }, { name := "to", ty := addr },
      { name := "id", ty := uint256 }]
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.var "from") (.storage (ownerOfRef (.var "id")))),
        .require (.binary .ne (.var "to") zeroAddr),
        .require (.binary .or
          (.binary .or
            (.binary .eq sender (.var "from"))
            (.storage (isApprovedForAllRef (.var "from") sender)))
          (.binary .eq sender (.storage (getApprovedRef (.var "id"))))),
        -- unchecked { _balanceOf[from]--; _balanceOf[to]++; }
        .assign .storage (balanceOfRef (.var "from"))
          (.binary .sub (.storage (balanceOfRef (.var "from"))) (.intLit 1)),
        .assign .storage (balanceOfRef (.var "to"))
          (.binary .add (.storage (balanceOfRef (.var "to"))) (.intLit 1)),
        .assign .storage (ownerOfRef (.var "id")) (.var "to"),
        .delete (getApprovedRef (.var "id")) ] }

/-- `getApproved(uint256) view returns (address)` — auto-generated public getter. -/
def getApprovedGetter : TransitionDecl :=
  { name := "getApproved"
    params := [{ name := "id", ty := uint256 }]
    returnType := some addr
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (getApprovedRef (.var "id"))) ] }

/-- `isApprovedForAll(address, address) view returns (bool)` — auto-generated public getter. -/
def isApprovedForAllGetter : TransitionDecl :=
  { name := "isApprovedForAll"
    params := [{ name := "owner", ty := addr }, { name := "operator", ty := addr }]
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage (isApprovedForAllRef (.var "owner") (.var "operator"))) ] }

/-! ## Contract + config -/

def erc721Contract : ContractDecl :=
  { name := "ERC721"
    storage := erc721StorageDecls
    ctor := { params := [], body := [] }
    transitions :=
      [ approveTransition,            -- 095ea7b3
        balanceOfTransition,          -- 70a08231
        getApprovedGetter,            -- 081812fc
        isApprovedForAllGetter,       -- e985e9c5
        ownerOfTransition,            -- 6352211e
        setApprovalForAllTransition,  -- a22cb465
        transferFromTransition ] }    -- 23b872dd

end ERC721

def erc721Config : Config :=
  { storage := ERC721.erc721StorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment ERC721.erc721Contract.ctor.params }
