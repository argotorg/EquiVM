import Solidity.Elab
import Solm.SolidityStorage

/-!
# Canonical Solidity storage layout

Derives solc's storage layout for the flattened state variables (declaration order, base-first;
items smaller than 32 bytes packed lower-order aligned, moved to the next slot only when they do
not fit; structs and arrays start on a slot boundary and the following item starts a new slot;
mappings at `keccak256(h(k) . p)`; dynamic-array data at `keccak256(p)`; `bytes`/`string` in the
short/long form).  The result is a `Solm.StorageLayout`: a state-independent locator from
`Solm.EvaledStorageRef` paths to `Solm.StorageAddr` (a leaf location, the header slot of a
dynamically-sized value, or the symbolic byte of a `bytes`/`string`), which `Solm.solidityStorageBackend`
turns into the storage operations the semantics uses.  Slot tables are keccak-free and can be
checked with `#guard`.
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
    | some elem => some (.leaf elem (Solm.elemTypeSoliditySize elem).val)
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

/-- Element type of `bytes`/`string` storage data: indexing yields a `bytes1`. -/
def bytes1Elem : ElemType := .bytes ⟨0, by decide⟩

def mkLoc (slot : EVM.Word) (off size : Nat) (elem : ElemType) : Option Solm.StorageLoc :=
  if h : off + size ≤ 32 ∧ 0 < size then
    some { slot := slot, offset := ⟨off, by omega⟩, size := ⟨size, by omega⟩, hbound := by simp; omega,
           bitOffset := none, type := elem }
  else none

/-- `keccak256(h(k) . p)` — key word first, as `Examples/ERC20/Spec.lean`'s `erc20MappingSlot`. -/
def mappingSlot (k : Solm.KeyValue) (p : EVM.Word) : EVM.Word :=
  Ethereum.uInt256OfByteArray (Ethereum.KEC ((Solm.keyValueToWord k).toByteArray ++ p.toByteArray))

/-- `keccak256(p)`: dynamic-array / long-bytes data base. -/
def dataSlot (p : EVM.Word) : EVM.Word := Solm.solidityBytesDataBaseSlot p

/-- Location of element `i` of an array whose data starts at `base`. -/
def elemLoc (elem : Node) (base : EVM.Word) (i : Nat) : EVM.Word × Nat :=
  match elem.leafSize? with
  | some s => let per := 32 / s; (base + .ofNat (i / per), (i % per) * s)
  | none => (base + .ofNat (i * elem.slots), 0)

def natOfKey? : Solm.KeyValue → Option Nat
  | .int i => if i < 0 then none else some i.toNat
  | _ => none

/-- Follow an evaluated storage path from a node placed at `(slot, off)`: a scalar is a leaf
    location, a dynamic array or `bytes`/`string` locates its header slot (`anchor`), and the
    `i`-th byte of a `bytes`/`string` is the symbolic `byte` the backend resolves from its short or
    long encoding. -/
def follow : List Solm.EvaledStorageRefStep → Node → EVM.Word → Nat → Option Solm.StorageAddr
  | [], .leaf elem size, slot, off => (mkLoc slot off size elem).map .leaf
  | [], .dynArray _, slot, _ => some (.anchor slot)
  | [], .bytes, slot, _ => some (.anchor slot)
  | [], _, _, _ => none
  | .field f :: rest, .struct _ fields _, slot, _ =>
    (fields.find? (·.1 == f)).bind fun (_, rel, off', n') => follow rest n' (slot + .ofNat rel) off'
  | .mindex k :: rest, .mapping _ val, slot, _ => follow rest val (mappingSlot k slot) 0
  | .aindex k :: rest, .staticArray e _, slot, _ =>
    (natOfKey? k).bind fun i => let (s, o) := elemLoc e slot i; follow rest e s o
  | .aindex k :: rest, .dynArray e, slot, _ =>
    (natOfKey? k).bind fun i => let (s, o) := elemLoc e (dataSlot slot) i; follow rest e s o
  | [.aindex k], .bytes, slot, _ => (natOfKey? k).map fun i => .byte slot i
  | _, _, _, _ => none

/-- The locator of a layout table. -/
def layout (t : LayoutTable) (ref : Solm.EvaledStorageRef) : Option Solm.StorageAddr :=
  (t.find? (·.1.key == ref.base)).bind fun (_, slot, off, n) => follow ref.steps n (.ofNat slot) off

/-- The locator of a layout table, as the `Solm.StorageLayout` a backend is built from. -/
def storageLayout (t : LayoutTable) : Solm.StorageLayout := layout t

/-- The Solidity storage backend of a layout table. -/
def storageBackend (t : LayoutTable) : Solm.StorageBackend :=
  Solm.solidityStorageBackend (storageLayout t)

def FlatContract.layoutTable? (fc : FlatContract) : Option LayoutTable :=
  layoutVars fc.types fc.storageVars

end Solidity
