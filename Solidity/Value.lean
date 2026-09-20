import Solidity.Arith
import ABI.Value
import Solm.Syntax

/-!
# Runtime values, memory and locals

Values carry their static type (widths, enum/contract names); integer literals stay exact until
they meet a typed operand.  Reference types live in a heap (`memRef`): memory-to-memory
assignment aliases, storage/calldata copies allocate.  `storageRef` is a storage pointer
(`T storage x`).  At the ABI and storage boundaries values convert to/from `ABI.ABIValue`.
-/

namespace Solidity

open ABI

inductive Value where
  | uint (w : BitWidth) (n : Nat)
  | sint (w : BitWidth) (i : Int)
  /-- An integer literal, exact. -/
  | literal (i : Int)
  | bool (b : Bool)
  | address (a : EVM.Address)
  | contract (ty : Ident) (a : EVM.Address)
  | fixedBytes (n : Fin 32) (bs : List UInt8)
  /-- A string / hex literal, untyped. -/
  | strLit (s : ByteArray)
  | enum (ty : Ident) (i : Nat)
  | memRef (id : Nat)
  | storageRef (er : Solm.EvaledStorageRef) (ty : Ty)
  /-- A calldata word of static type `ty` not yet validated (validated on access). -/
  | raw (ty : Ty) (w : Nat)
  | tuple (vs : List Value)
  | unit
  deriving Inhabited, Repr

inductive HeapObj where
  | struct (ty : Ty) (fields : List (Ident × Value))
  /-- Memory arrays are fixed-size after creation. -/
  | array (elem : Ty) (elems : List Value)
  | bytes (isString : Bool) (data : ByteArray)
  deriving Inhabited, Repr

structure Heap where
  objs : Array HeapObj := #[]
  deriving Inhabited, Repr

namespace Heap

def alloc (h : Heap) (o : HeapObj) : Heap × Nat := ({ objs := h.objs.push o }, h.objs.size)

def get? (h : Heap) (id : Nat) : Option HeapObj := h.objs[id]?

def set (h : Heap) (id : Nat) (o : HeapObj) : Heap :=
  if hlt : id < h.objs.size then { objs := h.objs.set id o hlt } else h

end Heap

structure Local where
  ty : Ty
  loc : Option DataLoc := none
  val : Value
  deriving Inhabited, Repr

abbrev Store := Std.HashMap Ident Local

/-! ## Integer views -/

/-- The integer type and value of a typed integer. -/
def Value.int? : Value → Option (IntTy × Int)
  | .uint w n => some (.uint w, n)
  | .sint w i => some (.sint w, i)
  | _ => none

def mkInt (t : IntTy) (i : Int) : Value :=
  match t with
  | .uint w => .uint w i.toNat
  | .sint w => .sint w i

/-- Static type of a typed runtime value (`none` for literals, references into the heap, tuples). -/
def Value.ty? : Value → Option Ty
  | .uint w _ => some (.uint w)
  | .sint w _ => some (.int w)
  | .bool _ => some .bool
  | .address _ => some (.address false)
  | .contract ty _ => some (.user none ty)
  | .fixedBytes n _ => some (.fixedBytes n)
  | .enum ty _ => some (.user none ty)
  | .storageRef _ ty => some ty
  | .raw ty _ => some ty
  | _ => none

/-! ## Zero values -/

/-- The zero value of a value type. -/
def zeroValue (env : TypeEnv) : Ty → Option Value
  | .uint w => some (.uint w 0)
  | .int w => some (.sint w 0)
  | .bool => some (.bool false)
  | .address _ => some (.address (EVM.address 0))
  | .fixedBytes n => some (.fixedBytes n (List.replicate (n.val + 1) 0))
  | .user q n =>
    if (env.enum? q n).isSome then some (.enum n 0)
    else if (env.contractKind? n).isSome then some (.contract n (EVM.address 0))
    else none
  | _ => none

/-- Zero-initialise a memory object of a reference type (arrays get `len` elements). -/
def zeroObj (env : TypeEnv) : Nat → Ty → Nat → Heap → Option (Value × Heap)
  | 0, _, _, _ => none
  | fuel + 1, ty, len, h =>
    match zeroValue env ty with
    | some v => some (v, h)
    | none =>
      match ty with
      | .bytes => let (h', id) := h.alloc (.bytes false (ByteArray.mk (Array.replicate len 0))); some (.memRef id, h')
      | .string => let (h', id) := h.alloc (.bytes true (ByteArray.mk (Array.replicate len 0))); some (.memRef id, h')
      | .array e n => zeroArray fuel e n h
      | .dynArray e => zeroArray fuel e len h
      | .user q n => do
        let s ← env.struct? q n
        let (fields, h') ← s.fields.foldlM (fun (acc, h) (fty, fname) => do
          let (v, h') ← zeroObj env fuel fty 0 h
          pure (acc ++ [(fname, v)], h')) (([] : List (Ident × Value)), h)
        let (h'', id) := h'.alloc (.struct ty fields)
        pure (.memRef id, h'')
      | _ => none
where
  zeroArray (fuel : Nat) (e : Ty) (n : Nat) (h : Heap) : Option (Value × Heap) := do
    let (elems, h') ← (List.range n).foldlM (fun (acc, h) _ => do
      let (v, h') ← zeroObj env fuel e 0 h
      pure (acc ++ [v], h')) (([] : List Value), h)
    let (h'', id) := h'.alloc (.array e elems)
    pure (.memRef id, h'')

/-! ## ABI boundary -/

def scalarToAbi : Value → Option ABIValue
  | .uint _ n => some (.int n)
  | .sint _ i => some (.int i)
  | .literal i => some (.int i)
  | .enum _ i => some (.int i)
  | .bool b => some (.bool b)
  | .address a => some (.address a)
  | .contract _ a => some (.address a)
  | .fixedBytes n bs => some (.fixedBytes n bs)
  | .strLit s => some (.bytes s)
  | _ => none

/-- Typed reconstruction of a scalar from its ABI/storage value. -/
def scalarOfAbi (env : TypeEnv) : Ty → ABIValue → Option Value
  | .uint w, .int i => if 0 ≤ i ∧ i < 2 ^ w.val then some (.uint w i.toNat) else none
  | .int w, .int i => if -(2 ^ (w.val - 1) : Int) ≤ i ∧ i < 2 ^ (w.val - 1) then some (.sint w i) else none
  | .bool, .bool b => some (.bool b)
  | .address _, .address a => some (.address a)
  | .fixedBytes n, .fixedBytes m bs => if n = m then some (.fixedBytes n bs) else none
  | .user q n, .int i =>
    match env.enum? q n with
    | some e => if i ≥ 0 ∧ i < e.members.length then some (.enum n i.toNat) else none
    | none => none
  | .user q n, .address a =>
    if (env.contractKind? n).isSome && (env.enum? q n).isNone then some (.contract n a) else none
  | _, _ => none

/-- Deep copy of a value into the ABI domain (memory structs become tuples). -/
def toAbi (h : Heap) : Nat → Value → Option ABIValue
  | 0, _ => none
  | fuel + 1, v =>
    match v with
    | .memRef id =>
      match h.get? id with
      | some (.struct _ fields) => (fields.mapM fun f => toAbi h fuel f.2).map .tuple
      | some (.array _ elems) => (elems.mapM (toAbi h fuel)).map .array
      | some (.bytes _ data) => some (.bytes data)
      | none => none
    | .tuple vs => (vs.mapM (toAbi h fuel)).map .tuple
    | .raw _ w => some (.int w)
    | v => scalarToAbi v

/-- Typed reconstruction from an ABI value, allocating reference types in memory.  A calldata
    `bool` array element arrives as the decoder's raw-word marker and stays unvalidated. -/
def ofAbi (env : TypeEnv) : Nat → Ty → ABIValue → Heap → Option (Value × Heap)
  | 0, _, _, _ => none
  | fuel + 1, ty, sv, h =>
    match ty, sv with
    | .bool, .rawBool w => some (.raw .bool w, h)
    | .bytes, .bytes b => let (h', id) := h.alloc (.bytes false b); some (.memRef id, h')
    | .string, .bytes b => let (h', id) := h.alloc (.bytes true b); some (.memRef id, h')
    | .dynArray e, .array vs => ofArray fuel e vs h
    | .array e n, .array vs => if vs.length = n then ofArray fuel e vs h else none
    | .user q n, .tuple vs => do
      let s ← env.struct? q n
      if s.fields.length ≠ vs.length then none
      let (fields, h') ← (s.fields.zip vs).foldlM (fun (acc, h) ((fty, fname), sv) => do
        let (v, h') ← ofAbi env fuel fty sv h
        pure (acc ++ [(fname, v)], h')) (([] : List (Ident × Value)), h)
      let (h'', id) := h'.alloc (.struct ty fields)
      pure (.memRef id, h'')
    | ty, sv => (scalarOfAbi env ty sv).map (·, h)
where
  ofArray (fuel : Nat) (e : Ty) (vs : List ABIValue) (h : Heap) : Option (Value × Heap) := do
    let (elems, h') ← vs.foldlM (fun (acc, h) sv => do
      let (v, h') ← ofAbi env fuel e sv h
      pure (acc ++ [v], h')) (([] : List Value), h)
    let (h'', id) := h'.alloc (.array e elems)
    pure (.memRef id, h'')

def fuelDefault : Nat := 1024

end Solidity
