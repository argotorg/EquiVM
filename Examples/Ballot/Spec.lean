import Solm.Semantics
import Solm.SolidityLayout

/-!
# Ballot — Solm specification for `Ballot.sol`

A faithful (events-aside) Solm spec of the classic Solidity "Voting with delegation" `Ballot`
contract.  This exercises a broad slice of the Solm surface that earlier examples did not:

* **structs** — `Voter { weight, voted, delegate, vote }` and `Proposal { name, voteCount }`,
  with the solc storage **packing** of `Voter` (`voted`/`delegate` share one slot);
* a **`mapping(address => Voter)`** (`voters`) and a **dynamic array of structs**
  (`Proposal[] proposals`);
* **storage aliases** (`Voter storage sender = voters[msg.sender]`) via `letStorage`;
* a **`while`** delegation-chain walk and two **`for`** loops;
* an **internal call** to a `public` function (`winnerName` ⇒ `winningProposal`) — the `Reuse`
  pattern;
* the three **auto-generated public getters** (`chairperson()`, `voters(address)`,
  `proposals(uint256)`) that solc adds to the external ABI, modelled as transitions returning
  ABI tuples for the struct getters.

The storage layout is **hand-written** to match the deployed bytecode's slot assignment exactly
(rather than relying on `genSolidityLayout`, whose packed-struct layout is still WIP):

| variable          | slot                                   | notes |
|-------------------|----------------------------------------|-------|
| `chairperson`     | `0` (offset 0, 20 bytes)               | address |
| `voters[a]`       | `keccak256(a ‖ 1)` = `B`               | mapping base |
| `…weight`         | `B + 0`                                | uint256 |
| `…voted`          | `B + 1` offset 0, 1 byte               | bool (packed) |
| `…delegate`       | `B + 1` offset 1, 20 bytes             | address (packed) |
| `…vote`           | `B + 2`                                | uint256 |
| `proposals.length`| `2`                                    | dynamic array length |
| `proposals[i].name`| `keccak256(2) + 2·i`                   | bytes32 |
| `proposals[i].voteCount`| `keccak256(2) + 2·i + 1`          | uint256 |

This is spec-level data only; the bytecode/jump facts live in `Bytecode.lean` and the proofs in
the per-function files / `Correct.lean`.
-/

open Solm ABI

namespace Ballot

/-! ## ABI / storage element types -/

def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr    : ABIType := .elem .address
def boolTy  : ABIType := .elem .bool
/-- `bytes32` is the ABI fixed-bytes of width 32 (`ElemType.bytes` stores `n` with width `n+1`). -/
def bytes32 : ABIType := .elem (.bytes ⟨31, by decide⟩)

def uint256St  : StorageType := .elem (.int uint256Int)
def addrSt     : StorageType := .elem .address
def boolSt     : StorageType := .elem .bool
def bytes32St  : StorageType := .elem (.bytes ⟨31, by decide⟩)

/-! ## Expression / ref helpers -/

def sender : Expr := .env .caller
/-- `address(0)`. -/
def zeroAddr : Expr := .cast (.intLit 0) addrSt
/-- Pin a value into the `uint256` range (models solc's *checked* arithmetic: reverts on overflow). -/
def u256 (e : Expr) : Expr := .inRange uint256Int e

def chairpersonRef : StorageRef := { base := "chairperson" }
def proposalsRef   : StorageRef := { base := "proposals" }

/-- The `Voter` struct stored at `voters[a]`. -/
def voterRef (a : Expr) : StorageRef := { base := "voters", steps := [.mindex a] }
/-- A field of `voters[a]`. -/
def voterF (a : Expr) (f : Ident) : StorageRef := { base := "voters", steps := [.mindex a, .field f] }
/-- A field of the storage alias `name` (e.g. `sender.weight`). -/
def aliasF (name : Ident) (f : Ident) : StorageRef := { base := name, steps := [.field f] }
/-- A field of `proposals[i]`. -/
def proposalF (i : Expr) (f : Ident) : StorageRef := { base := "proposals", steps := [.aindex i, .field f] }

/-! ## Storage declarations + struct schemas -/

def voterStructTy : StorageType :=
  .struct "Voter"
    [ ("weight", uint256St), ("voted", boolSt), ("delegate", addrSt), ("vote", uint256St) ]

def proposalStructTy : StorageType :=
  .struct "Proposal" [ ("name", bytes32St), ("voteCount", uint256St) ]

def voterStructDecl : StructDecl :=
  { name := "Voter"
    fields :=
      [ { name := "weight", ty := uint256St }, { name := "voted", ty := boolSt },
        { name := "delegate", ty := addrSt }, { name := "vote", ty := uint256St } ] }

def proposalStructDecl : StructDecl :=
  { name := "Proposal"
    fields := [ { name := "name", ty := bytes32St }, { name := "voteCount", ty := uint256St } ] }

def ballotStorageDecls : List StorageDecl :=
  [ { name := "chairperson", ty := addrSt },
    { name := "voters", ty := .mapping .address voterStructTy },
    { name := "proposals", ty := .dynamicArray proposalStructTy } ]

/-! ## Storage layout (hand-written, matches deployed bytecode) -/

/-- Solidity mapping slot: `keccak256(key ‖ baseSlot)`. -/
def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

/-- Base slot of `voters[a]` (the mapping lives at declaration slot `1`). -/
def voterBase (a : KeyValue) : Ethereum.UInt256 := mapSlot (keyValueToWord a) ⟨1⟩

/-- Data region of `proposals` (the dynamic array length lives at declaration slot `2`). -/
def proposalsDataBase : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (Ethereum.UInt256.toByteArray ⟨2⟩))

/-- Base slot of `proposals[i]` (each `Proposal` element occupies two words). -/
def proposalElemSlot (i : KeyValue) : Ethereum.UInt256 :=
  proposalsDataBase + Ethereum.UInt256.ofNat ((keyValueToWord i).toNat * 2)

/-- A full-word `uint256` storage location. -/
def wordLoc (s : Ethereum.UInt256) : StorageLoc :=
  { slot := s, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def ballotStorageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "chairperson", [] =>
        some { slot := ⟨0⟩, offset := 0, size := 20, hbound := by decide, type := .address }
    | "voters", [.mindex a, .field "weight"]   => some (wordLoc (voterBase a))
    | "voters", [.mindex a, .field "voted"]    =>
        some { slot := voterBase a + ⟨1⟩, offset := 0, size := 1, hbound := by decide, type := .bool }
    | "voters", [.mindex a, .field "delegate"] =>
        some { slot := voterBase a + ⟨1⟩, offset := 1, size := 20, hbound := by decide, type := .address }
    | "voters", [.mindex a, .field "vote"]     => some (wordLoc (voterBase a + ⟨2⟩))
    | "proposals", [.length] => some (wordLoc ⟨2⟩)
    | "proposals", [.aindex i, .field "name"] =>
        some { slot := proposalElemSlot i, offset := 0, size := 32, hbound := by decide,
               type := .bytes ⟨31, by decide⟩ }
    | "proposals", [.aindex i, .field "voteCount"] =>
        some (wordLoc (proposalElemSlot i + ⟨1⟩))
    | _, _ => none

/-! ## Constructor

`constructor(bytes32[] memory proposalNames)`: set the chairperson, give them one vote, and push a
zero-`voteCount` `Proposal` per name.  (Modelled for completeness; the runtime-equivalence theorem
covers the deployed code, not the creation code.)
-/
def constructorDecl : ConstructorDecl :=
  { params := [{ name := "proposalNames", ty := .dynamicArray bytes32 }]
    body :=
      -- The constructor is **non-payable**: solc emits a `callvalue` guard that reverts when the
      -- creation message carries value, exactly as for every non-payable transition (cf.
      -- `giveRightToVoteTransition`, `voteTransition`, …).  Modelled explicitly so the
      -- creation-code equivalence holds for an arbitrary `weiValue`.
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage chairpersonRef sender,
        .assign .storage (voterF (.storage chairpersonRef) "weight") (.intLit 1),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.arrayLength .localVar { base := "proposalNames" }))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .push proposalsRef
              (some (.structLit "Proposal"
                [ ("name", .index (.var "proposalNames") (.var "i")), ("voteCount", .intLit 0) ])) ] ] }

/-! ## Transitions — explicit (hand-written) functions -/

/-- `giveRightToVote(address voter) external` — chairperson grants one vote. -/
def giveRightToVoteTransition : TransitionDecl :=
  { name := "giveRightToVote"
    params := [{ name := "voter", ty := addr }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq sender (.storage chairpersonRef)),
        .require (.unary .not (.storage (voterF (.var "voter") "voted"))),
        .require (.binary .eq (.storage (voterF (.var "voter") "weight")) (.intLit 0)),
        .assign .storage (voterF (.var "voter") "weight") (.intLit 1) ] }

/-- `delegate(address to) external` — walk the delegation chain, then delegate. -/
def delegateTransition : TransitionDecl :=
  { name := "delegate"
    params := [{ name := "to", ty := addr }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        -- `Voter storage sender = voters[msg.sender];`
        .letStorage "sender" (voterRef sender),
        .require (.binary .ne (.storage (aliasF "sender" "weight")) (.intLit 0)),
        .require (.unary .not (.storage (aliasF "sender" "voted"))),
        .require (.binary .ne (.var "to") sender),
        -- `while (voters[to].delegate != address(0)) { to = voters[to].delegate; require(to != msg.sender); }`
        .while (.binary .ne (.storage (voterF (.var "to") "delegate")) zeroAddr)
          [ .assign .localVar { base := "to" } (.storage (voterF (.var "to") "delegate")),
            .require (.binary .ne (.var "to") sender) ],
        -- `Voter storage delegate_ = voters[to];`
        .letStorage "delegate_" (voterRef (.var "to")),
        .require (.binary .ge (.storage (aliasF "delegate_" "weight")) (.intLit 1)),
        .assign .storage (aliasF "sender" "voted") (.boolLit true),
        .assign .storage (aliasF "sender" "delegate") (.var "to"),
        .ite (.storage (aliasF "delegate_" "voted"))
          -- delegate already voted: `proposals[delegate_.vote].voteCount += sender.weight;`
          [ .assign .storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount")
              (u256 (.binary .add
                (.storage (proposalF (.storage (aliasF "delegate_" "vote")) "voteCount"))
                (.storage (aliasF "sender" "weight")))) ]
          -- delegate has not voted: `delegate_.weight += sender.weight;`
          [ .assign .storage (aliasF "delegate_" "weight")
              (u256 (.binary .add
                (.storage (aliasF "delegate_" "weight"))
                (.storage (aliasF "sender" "weight")))) ] ] }

/-- `vote(uint256 proposal) external` — cast your (delegated) weight to a proposal. -/
def voteTransition : TransitionDecl :=
  { name := "vote"
    params := [{ name := "proposal", ty := uint256 }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letStorage "sender" (voterRef sender),
        .require (.binary .ne (.storage (aliasF "sender" "weight")) (.intLit 0)),
        .require (.unary .not (.storage (aliasF "sender" "voted"))),
        .assign .storage (aliasF "sender" "voted") (.boolLit true),
        .assign .storage (aliasF "sender" "vote") (.var "proposal"),
        .assign .storage (proposalF (.var "proposal") "voteCount")
          (u256 (.binary .add
            (.storage (proposalF (.var "proposal") "voteCount"))
            (.storage (aliasF "sender" "weight")))) ] }

/-- `winningProposal() public view returns (uint256)` — argmax of `proposals[*].voteCount`.
    `public`, so it is both an external entry and the internal callee of `winnerName`. -/
def winningProposalTransition : TransitionDecl :=
  { name := "winningProposal"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "winningProposal_" (some uint256) (.intLit 0),
        .letDecl "winningVoteCount" (some uint256) (.intLit 0),
        .for
          [ .letDecl "p" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "p") (.arrayLength .storage proposalsRef))
          -- solc emits an *unchecked* `p++` here (the loop bound proves no overflow)
          [ .assign .localVar { base := "p" } (.binary .add (.var "p") (.intLit 1)) ]
          [ .ite (.binary .gt (.storage (proposalF (.var "p") "voteCount")) (.var "winningVoteCount"))
              [ .assign .localVar { base := "winningVoteCount" }
                  (.storage (proposalF (.var "p") "voteCount")),
                .assign .localVar { base := "winningProposal_" } (.var "p") ]
              [] ],
        .return [(.var "winningProposal_")] ] }

/-- `winnerName() external view returns (bytes32)` — name of the winning proposal.
    Calls `winningProposal()` internally (the shared routine). -/
def winnerNameTransition : TransitionDecl :=
  { name := "winnerName"
    params := []
    returnType := [bytes32]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .internalCall "winningProposal" [] "w",
        .return [(.storage (proposalF (.var "w") "name"))] ] }

/-! ## Transitions — auto-generated public getters -/

/-- `chairperson() view returns (address)`. -/
def chairpersonGetter : TransitionDecl :=
  { name := "chairperson"
    params := []
    returnType := [addr]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage chairpersonRef)] ] }

/-- `voters(address) view returns (uint256 weight, bool voted, address delegate, uint256 vote)`.
    The struct getter returns the members as an ABI tuple. -/
def votersGetter : TransitionDecl :=
  { name := "voters"
    params := [{ name := "a", ty := addr }]
    returnType := [uint256, boolTy, addr, uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return
          [ .storage (voterF (.var "a") "weight"),
            .storage (voterF (.var "a") "voted"),
            .storage (voterF (.var "a") "delegate"),
            .storage (voterF (.var "a") "vote") ] ] }

/-- `proposals(uint256) view returns (bytes32 name, uint256 voteCount)`. -/
def proposalsGetter : TransitionDecl :=
  { name := "proposals"
    params := [{ name := "i", ty := uint256 }]
    returnType := [bytes32, uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return
          [ .storage (proposalF (.var "i") "name"),
            .storage (proposalF (.var "i") "voteCount") ] ] }

/-! ## Contract + config -/

def ballotContract : ContractDecl :=
  { name := "Ballot"
    storage := ballotStorageDecls
    ctor := constructorDecl
    structs := [voterStructDecl, proposalStructDecl]
    transitions :=
      [ voteTransition,            -- 0121b93f
        proposalsGetter,           -- 013cf08b
        chairpersonGetter,         -- 2e4176cf
        delegateTransition,        -- 5c19a95c
        winningProposalTransition, -- 609ff1bd
        giveRightToVoteTransition, -- 9e7b8d61
        votersGetter,              -- a3ec138d
        winnerNameTransition ] }   -- e2ba53f0

end Ballot

def ballotConfig : Config :=
  { storage := Ballot.ballotStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment Ballot.ballotContract.ctor.params }
