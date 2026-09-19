import Solidity.Elab
import Storage.SolcLayout

/-!
# Canonical Solidity storage layout

Derives solc's storage layout for the flattened state variables (declaration order, base-first;
items smaller than 32 bytes packed lower-order aligned, moved to the next slot only when they do
not fit; structs and arrays start on a slot boundary and the following item starts a new slot;
mappings at `keccak256(h(k) . p)`; dynamic-array data at `keccak256(p)`; `bytes`/`string` in the
short/long form).  The result is a `Storage.StorageLayout` over `Solm.EvaledStorageRef` paths, so
`Storage.storageLocLoad`/`storageLocStore` and the `Reasoning/Storage.lean` lemmas apply unchanged.
Slot tables are keccak-free and can be checked with `#guard`.
-/

namespace Solidity

open ABI

/-- Storage tree of a state variable's type. -/
inductive Node where
  | leaf (elem : ElemType) (size : Nat)
  | mapping (key : Ty) (val : Node)
  | dynArray (elem : Node)
  | staticArray (elem : Node) (n : Nat)
  /-- Fields as `(name, relative slot, byte offset, node)`, plus the total slot count. -/
  | struct (name : Ident) (fields : List (Ident × Nat × Nat × Node)) (slots : Nat)
  | bytes
  deriving Repr, Inhabited

namespace Node

def leafSize? : Node → Option Nat
  | .leaf _ s => some s
  | _ => none

/-- Slots occupied when the node starts on a slot boundary. -/
def slots : Node → Nat
  | .leaf .. => 1
  | .mapping .. => 1
  | .dynArray _ => 1
  | .bytes => 1
  | .struct _ _ s => s
  | .staticArray e n =>
    match e.leafSize? with
    | some s => (n + (32 / s) - 1) / (32 / s)
    | none => n * e.slots

end Node

structure Cursor where
  slot : Nat
  offset : Nat
  deriving Repr, Inhabited

/-- Place a node at the cursor: `((slot, offset), next cursor)`. -/
def place (c : Cursor) (n : Node) : (Nat × Nat) × Cursor :=
  match n with
  | .leaf _ size =>
    let (slot, off) := if c.offset + size > 32 then (c.slot + 1, 0) else (c.slot, c.offset)
    let next := if off + size ≥ 32 then ⟨slot + 1, 0⟩ else ⟨slot, off + size⟩
    ((slot, off), next)
  | _ =>
    let slot := if c.offset ≠ 0 then c.slot + 1 else c.slot
    ((slot, 0), ⟨slot + n.slots, 0⟩)

/-- Place a list of nodes in order from cursor `c`. -/
def placeAll (c : Cursor) : List (Ident × Node) → List (Ident × Nat × Nat × Node) × Cursor
  | [] => ([], c)
  | (name, n) :: rest =>
    let ((slot, off), c') := place c n
    let (placed, c'') := placeAll c' rest
    ((name, slot, off, n) :: placed, c'')

/-- Slots covered by a placement that ends at cursor `c`. -/
def Cursor.slotsUsed (c : Cursor) : Nat := if c.offset = 0 then c.slot else c.slot + 1

def nodeOfFuel (env : TypeEnv) : Nat → Ty → Option Node
  | 0, _ => none
  | fuel + 1, ty =>
    match leafElemType env ty with
    | some elem => some (.leaf elem (Storage.elemTypeSoliditySize elem).val)
    | none =>
      match ty with
      | .bytes | .string => some .bytes
      | .mapping k v => (nodeOfFuel env fuel v).map (.mapping k)
      | .array e n => (nodeOfFuel env fuel e).map (.staticArray · n)
      | .dynArray e => (nodeOfFuel env fuel e).map .dynArray
      | .user q n => do
        let s ← env.struct? q n
        let nodes ← s.fields.mapM fun f => (nodeOfFuel env fuel f.1).map (f.2, ·)
        let (fields, c) := placeAll ⟨0, 0⟩ nodes
        pure (.struct s.name fields c.slotsUsed)
      | _ => none

def nodeOf (env : TypeEnv) (ty : Ty) : Option Node :=
  nodeOfFuel env 256 ty

abbrev LayoutTable := List (FlatVar × Nat × Nat × Node)

/-- Slot/offset of every storage variable (constants and immutables take no slot). -/
def layoutVars (env : TypeEnv) (vars : List FlatVar) : Option LayoutTable := do
  let nodes ← vars.mapM fun v => (nodeOf env v.ty).map (v, ·)
  let (placed, _) := placeAll ⟨0, 0⟩ (nodes.map fun (v, n) => (v.key, n))
  pure (placed.zip nodes |>.map fun ((_, slot, off, n), (v, _)) => (v, slot, off, n))

def slotTable (t : LayoutTable) : List (Ident × Nat × Nat) :=
  t.map fun (v, slot, off, _) => (v.key, slot, off)

/-! ## Locations -/

def uint256Elem : ElemType := .int (.uint ⟨256, by decide⟩)

def mkLoc (slot : EVM.Word) (off size : Nat) (elem : ElemType) : Option Storage.StorageLoc :=
  if h : off + size ≤ 32 ∧ 0 < size then
    some { slot := slot, offset := ⟨off, by omega⟩, size := ⟨size, by omega⟩, hbound := by simp; omega,
           bitOffset := none, type := elem }
  else none

def wordLoc (slot : EVM.Word) : Storage.StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, bitOffset := none, type := uint256Elem }

/-- `keccak256(h(k) . p)` — key word first, as `Examples/ERC20/Spec.lean`'s `erc20MappingSlot`. -/
def mappingSlot (k : Solm.KeyValue) (p : EVM.Word) : EVM.Word :=
  Ethereum.uInt256OfByteArray (ffi.KEC ((Solm.keyValueToWord k).toByteArray ++ p.toByteArray))

/-- `keccak256(p)`: dynamic-array / long-bytes data base. -/
def dataSlot (p : EVM.Word) : EVM.Word := Storage.solidityBytesDataBaseSlot p

/-- Location of element `i` of an array whose data starts at `base`. -/
def elemLoc (elem : Node) (base : EVM.Word) (i : Nat) : EVM.Word × Nat :=
  match elem.leafSize? with
  | some s => let per := 32 / s; (base + .ofNat (i / per), (i % per) * s)
  | none => (base + .ofNat (i * elem.slots), 0)

def natOfKey? : Solm.KeyValue → Option Nat
  | .int i => if i < 0 then none else some i.toNat
  | _ => none

/-- Follow an evaluated storage path from a node placed at `(slot, off)`. -/
def follow (evm : EVM.State) : List Solm.EvaledStorageRefStep → Node → EVM.Word → Nat →
    Option Storage.StorageLoc
  | [], .leaf elem size, slot, off => mkLoc slot off size elem
  | [], _, _, _ => none
  | .field f :: rest, .struct _ fields _, slot, _ =>
    (fields.find? (·.1 == f)).bind fun (_, rel, off', n') => follow evm rest n' (slot + .ofNat rel) off'
  | .mindex k :: rest, .mapping _ val, slot, _ => follow evm rest val (mappingSlot k slot) 0
  | .aindex k :: rest, .staticArray e _, slot, _ =>
    (natOfKey? k).bind fun i => let (s, o) := elemLoc e slot i; follow evm rest e s o
  | .aindex k :: rest, .dynArray e, slot, _ =>
    (natOfKey? k).bind fun i => let (s, o) := elemLoc e (dataSlot slot) i; follow evm rest e s o
  | [.length], .dynArray _, slot, _ => some (wordLoc slot)
  | [.length], .bytes, slot, _ => some (Storage.bytesLikeLengthLoc slot evm)
  | [.aindex k], .bytes, slot, _ =>
    (natOfKey? k).bind fun i =>
      if Storage.checkBytesPacked slot evm then mkLoc slot (31 - i) 1 uint8Elem
      else mkLoc (dataSlot slot + .ofNat (i / 32)) (31 - i % 32) 1 uint8Elem
  | _, _, _, _ => none

def layout (t : LayoutTable) (ref : Solm.EvaledStorageRef) (evm : EVM.State) : Option Storage.StorageLoc :=
  (t.find? (·.1.key == ref.base)).bind fun (_, slot, off, n) => follow evm ref.steps n (.ofNat slot) off

/-- The `Storage.StorageLayout` (with the `bytes`/`string` hooks) of a layout table. -/
def storageLayout (t : LayoutTable) : Storage.StorageLayout :=
  Storage.solidityStorageLayout (layout t)

def FlatContract.layoutTable? (fc : FlatContract) : Option LayoutTable :=
  layoutVars fc.types fc.storageVars

end Solidity
