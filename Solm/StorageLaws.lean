import Solm.Semantics.StorageOps
import Solm.SolidityStorage

/-!
# Storage backend laws (target statements)

The laws a `StorageBackend` should satisfy so that a spec consumer can reason about storage through
the backend's operations instead of unfolding the physical storage map.

This file only *states* the laws: `LawfulStorageBackend` is a structure of propositions, and nothing
here is proven yet. The intended Solidity instance is sketched at the end.

## Shape

* Laws are about **well-typed, canonical references** (`Ref`): the reference follows the contract's
  storage schema, mapping keys are canonical for their key type, and the legacy `.length` step is
  not used. Reads and writes at the wrong type are out of scope.
* Overlap is **syntactic**: two references overlap iff one is a prefix of the other. The one-step
  laws below (same-reference read-after-write, frame for disjoint references, and read
  decomposition of aggregates) together give every prefix case: writing `s` then reading `s.f`
  yields the field, and writing `s.f` then reading `s` updates only that field.
* Physical aliasing is a **parameter** (`Sep`), not a global assumption. For an idealised backend
  `Sep` is `True`. For Solidity it is "the physical footprints are disjoint": this holds without
  assumptions when the references diverge at a static step (struct field, fixed offset), and needs
  a keccak non-collision hypothesis when they diverge at a mapping key or a dynamic-array index.
  A *global* non-collision assumption would be false (pigeonhole), so it must stay local.
* **Mappings cannot be cleared or read whole.** Clear laws only promise a default value for
  mapping-free parts, and leave everything reached through a mapping step unchanged. The same holds
  for a popped element: mapping contents survive `pop`/`delete` and can reappear after `push`.
* Laws are stated in **partial-correctness form** (`op = .ok evm' → …`), with separate progress laws
  where an operation must not get stuck.
-/

namespace Solm
open ABI

/-- Extend a reference by one step. -/
def EvaledStorageRef.child (er : EvaledStorageRef) (step : EvaledStorageRefStep) :
    EvaledStorageRef :=
  { er with steps := er.steps ++ [step] }

/-- Extend a reference by several steps. -/
def EvaledStorageRef.extend (er : EvaledStorageRef) (suffix : List EvaledStorageRefStep) :
    EvaledStorageRef :=
  { er with steps := er.steps ++ suffix }

namespace StorageLaws

/-! ## Reference relations (backend-independent) -/

/-- `p` is `r` or an ancestor of `r`. -/
def Prefix (p r : EvaledStorageRef) : Prop :=
  p.base = r.base ∧ p.steps <+: r.steps

/-- Neither reference contains the other. -/
def Disjoint (r₁ r₂ : EvaledStorageRef) : Prop :=
  ¬ Prefix r₁ r₂ ∧ ¬ Prefix r₂ r₁

/-- A path that passes through a mapping entry. Such storage is never cleared. -/
def ThroughMapping (suffix : List EvaledStorageRefStep) : Prop :=
  ∃ k, EvaledStorageRefStep.mindex k ∈ suffix

/-! ## Typing -/

/-- Canonical (in-range) values of an elementary type. Writing a non-canonical value, e.g.
    `.int 300` at `uint8`, does not read back the same value. -/
def ElemValue : ElemType → Value → Prop
  | .bool, .bool _ => True
  | .address, .address _ => True
  | .int t, .int i => normalizeInt t i = i
  | .bytes n, .fixedBytes m bs => m = n ∧ bs.length = n.val + 1
  | _, _ => False

/-- Canonical mapping keys. Distinct canonical keys of the same type are distinct storage keys. -/
def KeyHasType : ElemType → KeyValue → Prop
  | .bool, .bool _ => True
  | .address, .address _ => True
  | .int t, .int i => normalizeInt t i = i
  | .bytes n, .fixedBytes m bs => m = n ∧ bs.length = n.val + 1
  | _, _ => False

mutual
/-- Values that can be written at a storage type. Mappings have no values. -/
inductive HasType : StorageType → Value → Prop
  | elem {t v} : ElemValue t v → HasType (.elem t) v
  | contract {n a} : HasType (.contract n) (.address a)
  | struct {n fs vs} : FieldsHaveType fs vs → HasType (.struct n fs) (.struct n vs)
  | tuple {ts vs} : AllHaveType ts vs → HasType (.tuple ts) (.tuple vs)
  | array {t n vs} : vs.length = n → (∀ v ∈ vs, HasType t v) → HasType (.array t n) (.array vs)
  | dynamicArray {t vs} : (∀ v ∈ vs, HasType t v) → HasType (.dynamicArray t) (.array vs)
  | bytes {b} : HasType .bytes (.bytes b)
  | string {b} : HasType .string (.bytes b)

inductive FieldsHaveType : List (Ident × StorageType) → List (Ident × Value) → Prop
  | nil : FieldsHaveType [] []
  | cons {f t v fs vs} :
      HasType t v → FieldsHaveType fs vs → FieldsHaveType ((f, t) :: fs) ((f, v) :: vs)

inductive AllHaveType : List StorageType → List Value → Prop
  | nil : AllHaveType [] []
  | cons {t v ts vs} : HasType t v → AllHaveType ts vs → AllHaveType (t :: ts) (v :: vs)
end

mutual
/-- Types with no mapping inside. Only these can be read whole, and only these are fully reset by
    `clear`/`pop`. -/
def MappingFree : StorageType → Bool
  | .mapping _ _ => false
  | .elem _ | .contract _ | .bytes | .string => true
  | .struct _ fields => fieldsMappingFree fields
  | .tuple types => typesMappingFree types
  | .array elem _ | .dynamicArray elem => MappingFree elem

def fieldsMappingFree : List (Ident × StorageType) → Bool
  | [] => true
  | field :: rest => MappingFree field.2 && fieldsMappingFree rest

def typesMappingFree : List StorageType → Bool
  | [] => true
  | ty :: rest => MappingFree ty && typesMappingFree rest
end

/-- Every step is canonical for the type it is applied to: mapping keys are canonical for the key
    type, array indices are non-negative integers, and the legacy `.length` step is not used. -/
def CanonicalSteps (decls : List StorageDecl) (er : EvaledStorageRef) : Prop :=
  ∀ pre step post, er.steps = pre ++ step :: post →
    match storageTypeAt? decls { er with steps := pre }, step with
    | some (.mapping keyTy _), .mindex k => KeyHasType keyTy k
    | some _, .aindex (.int i) => 0 ≤ i
    | some _, .aindex _ => False
    | _, .length => False
    | _, _ => True

/-- `er` is a well-typed, canonical reference of type `ty` in the schema `decls`. -/
def Ref (decls : List StorageDecl) (er : EvaledStorageRef) (ty : StorageType) : Prop :=
  storageTypeAt? decls er = some ty ∧ CanonicalSteps decls er

/-- Every array/bytes index on the path is below the length of what it indexes, in state `evm`.
    Backend operations do not bounds-check (evaluation does), so some laws need this explicitly. -/
def InBounds (decls : List StorageDecl) (B : StorageBackend) (evm : EVM.State)
    (er : EvaledStorageRef) : Prop :=
  ∀ pre (i : Int) post, er.steps = pre ++ .aindex (.int i) :: post →
    match storageTypeAt? decls { er with steps := pre } with
    | some (.array _ n) => i < n
    | some ty => ∃ n : Nat, B.length { er with steps := pre } ty evm = .ok n ∧ i < n
    | none => False

/-- The element type of a byte of `bytes`/`string`, as given by `storageTypeStep?`. -/
abbrev byteType : StorageType := .elem (.int (.uint ⟨8, by decide⟩))

/-! ## State relations -/

/-- Same executing contract, and its storage agrees everywhere. -/
def SameOwnStorage (evm evm' : EVM.State) : Prop :=
  evm.executionEnv.codeOwner = evm'.executionEnv.codeOwner ∧
  ∀ slot, EVM.storageLoad evm evm.executionEnv.codeOwner slot =
    EVM.storageLoad evm' evm'.executionEnv.codeOwner slot

/-- `evm'` differs from `evm` at most in the storage of the executing contract. -/
def OnlyOwnStorageChanged (evm evm' : EVM.State) : Prop :=
  { evm with accountMap := evm'.accountMap } = evm' ∧
  (∀ a, a ≠ evm.executionEnv.codeOwner → evm'.accountMap.get? a = evm.accountMap.get? a) ∧
  ((evm'.accountMap.get? evm.executionEnv.codeOwner).map fun acc => { acc with storage := default }) =
    ((evm.accountMap.get? evm.executionEnv.codeOwner).map fun acc => { acc with storage := default })

/-! ## Mutations and separation -/

/-- The state-changing backend operations, so that frame laws are stated once. -/
inductive Mutation where
  | write (value : Value)
  | clear
  | push (value : Option Value)
  | pop

def Mutation.run (B : StorageBackend) :
    Mutation → EvaledStorageRef → StorageType → EVM.State → EvalResult EVM.State
  | .write value, er, ty, evm => B.write er ty value evm
  | .clear, er, ty, evm => B.clear er ty evm
  | .push value, er, ty, evm => B.push er ty value evm
  | .pop, er, ty, evm => B.pop er ty evm

/-- `Sep evm evm' r₁ t₁ r₂ t₂`: a mutation at `r₁` taking `evm` to `evm'` cannot physically touch
    `r₂`. It sees both states because footprints of dynamic values depend on lengths, and a mutation
    may change them (a write of a longer array touches more elements than were there before). -/
abbrev Separation :=
  (evm evm' : EVM.State) → EvaledStorageRef → StorageType → EvaledStorageRef → StorageType → Prop

/-! ## Read decomposition helpers -/

/-- Read every field of a struct stored at `er`. -/
def readFields (B : StorageBackend) (er : EvaledStorageRef) (evm : EVM.State)
    (fields : List (Ident × StorageType)) : EvalResult (List (Ident × Value)) :=
  fields.mapM fun field => do
    let value <- B.read (er.child (.field field.1)) field.2 evm
    pure (field.1, value)

/-- Read the first `n` elements of an array stored at `er`. -/
def readElems (B : StorageBackend) (er : EvaledStorageRef) (evm : EVM.State)
    (elem : StorageType) (n : Nat) : EvalResult (List Value) :=
  (List.range n).mapM fun i => B.read (er.child (.aindex (.int i))) elem evm

/-! ## The laws -/

structure LawfulStorageBackend (decls : List StorageDecl) (B : StorageBackend)
    (Sep : Separation) : Prop where

  -- ### Locality: storage operations only see and touch the contract's own storage

  read_congr : ∀ {er ty evm evm'},
    SameOwnStorage evm evm' → B.read er ty evm = B.read er ty evm'

  length_congr : ∀ {er ty evm evm'},
    SameOwnStorage evm evm' → B.length er ty evm = B.length er ty evm'

  mutation_local : ∀ {m : Mutation} {er ty evm evm'},
    m.run B er ty evm = .ok evm' → OnlyOwnStorageChanged evm evm'

  -- ### Frame: a mutation leaves disjoint, separated references unchanged

  read_frame : ∀ {m : Mutation} {er₁ ty₁ er₂ ty₂ evm evm'},
    Ref decls er₁ ty₁ → Ref decls er₂ ty₂ → Disjoint er₁ er₂ →
    m.run B er₁ ty₁ evm = .ok evm' → Sep evm evm' er₁ ty₁ er₂ ty₂ →
    B.read er₂ ty₂ evm' = B.read er₂ ty₂ evm

  length_frame : ∀ {m : Mutation} {er₁ ty₁ er₂ ty₂ evm evm'},
    Ref decls er₁ ty₁ → Ref decls er₂ ty₂ → Disjoint er₁ er₂ →
    m.run B er₁ ty₁ evm = .ok evm' → Sep evm evm' er₁ ty₁ er₂ ty₂ →
    B.length er₂ ty₂ evm' = B.length er₂ ty₂ evm

  -- ### Write

  /-- A written value reads back. -/
  read_write : ∀ {er ty value evm evm'},
    Ref decls er ty → HasType ty value →
    B.write er ty value evm = .ok evm' → B.read er ty evm' = .ok value

  /-- Writing a well-typed value never gets stuck. (It may revert, e.g. on a corrupt bytes
      header in an arbitrary pre-state.) -/
  write_progress : ∀ {er ty value evm e},
    Ref decls er ty → HasType ty value → B.write er ty value evm ≠ .error e

  -- ### Read decomposition: aggregates read as their components

  read_struct : ∀ {er name fields evm},
    Ref decls er (.struct name fields) →
    B.read er (.struct name fields) evm = (Value.struct name ·) <$> readFields B er evm fields

  read_array : ∀ {er elem n evm},
    Ref decls er (.array elem n) →
    B.read er (.array elem n) evm = Value.array <$> readElems B er evm elem n

  read_dynamicArray : ∀ {er elem evm},
    Ref decls er (.dynamicArray elem) →
    B.read er (.dynamicArray elem) evm = (do
      let n <- B.length er (.dynamicArray elem) evm
      Value.array <$> readElems B er evm elem n)

  length_array : ∀ {er elem n evm},
    Ref decls er (.array elem n) → B.length er (.array elem n) evm = .ok n

  length_bytes : ∀ {er ty b evm},
    Ref decls er ty → (ty = .bytes ∨ ty = .string) →
    B.read er ty evm = .ok (.bytes b) → B.length er ty evm = .ok b.size

  read_bytes_index : ∀ {er ty b evm} {i : Nat},
    Ref decls er ty → (ty = .bytes ∨ ty = .string) →
    B.read er ty evm = .ok (.bytes b) → i < b.size →
    B.read (er.child (.aindex (.int i))) byteType evm = .ok (.int ((b.get! i).toNat : Int))

  -- ### Clear (Solidity `delete`)

  /-- Everything reachable from a cleared reference without passing through a mapping reads as
      its default value. Indices are bounded by the lengths *before* the clear. -/
  read_clear : ∀ {er ty evm evm' suffix ty'},
    Ref decls er ty → B.clear er ty evm = .ok evm' →
    Ref decls (er.extend suffix) ty' → ¬ ThroughMapping suffix → MappingFree ty' →
    InBounds decls B evm (er.extend suffix) →
    B.read (er.extend suffix) ty' evm' = defaultValue? ty'

  /-- Mapping entries are not cleared. -/
  read_clear_mapping : ∀ {er ty evm evm' suffix ty'},
    Ref decls er ty → B.clear er ty evm = .ok evm' →
    Ref decls (er.extend suffix) ty' → ThroughMapping suffix →
    B.read (er.extend suffix) ty' evm' = B.read (er.extend suffix) ty' evm

  length_clear : ∀ {er ty evm evm'},
    Ref decls er ty → (ty = .bytes ∨ ty = .string ∨ ∃ elem, ty = .dynamicArray elem) →
    B.clear er ty evm = .ok evm' → B.length er ty evm' = .ok 0

  clear_progress : ∀ {er ty evm e},
    Ref decls er ty → B.clear er ty evm ≠ .error e

  -- ### Dynamic arrays: push and pop

  length_push : ∀ {er elem value evm evm' n},
    Ref decls er (.dynamicArray elem) →
    B.length er (.dynamicArray elem) evm = .ok n →
    B.push er (.dynamicArray elem) value evm = .ok evm' →
    B.length er (.dynamicArray elem) evm' = .ok (n + 1)

  read_push_value : ∀ {er elem value evm evm' n},
    Ref decls er (.dynamicArray elem) → HasType elem value →
    B.length er (.dynamicArray elem) evm = .ok n →
    B.push er (.dynamicArray elem) (some value) evm = .ok evm' →
    B.read (er.child (.aindex (.int n))) elem evm' = .ok value

  /-- `push()` does not write the new element: it reads whatever was there. In reachable states
      that is the default value, because `pop` and `clear` reset removed elements (except their
      mapping contents). If the backend is changed to zero the new element, which I believe solc's
      IR code generator does, this becomes "`= defaultValue? elem`" for mapping-free `elem`. -/
  read_push_none : ∀ {er elem evm evm' n},
    Ref decls er (.dynamicArray elem) →
    B.length er (.dynamicArray elem) evm = .ok n →
    B.push er (.dynamicArray elem) none evm = .ok evm' →
    B.read (er.child (.aindex (.int n))) elem evm' =
      B.read (er.child (.aindex (.int n))) elem evm

  /-- Existing elements, and everything below them, are unchanged by `push`. -/
  read_push_old : ∀ {er elem value evm evm' n} {i : Nat} {suffix ty'},
    Ref decls er (.dynamicArray elem) →
    B.length er (.dynamicArray elem) evm = .ok n → i < n →
    B.push er (.dynamicArray elem) value evm = .ok evm' →
    Ref decls (er.extend (.aindex (.int i) :: suffix)) ty' →
    B.read (er.extend (.aindex (.int i) :: suffix)) ty' evm' =
      B.read (er.extend (.aindex (.int i) :: suffix)) ty' evm

  pop_empty : ∀ {er elem evm},
    Ref decls er (.dynamicArray elem) →
    B.length er (.dynamicArray elem) evm = .ok 0 →
    B.pop er (.dynamicArray elem) evm = .revert

  length_pop : ∀ {er elem evm evm' n},
    Ref decls er (.dynamicArray elem) →
    B.length er (.dynamicArray elem) evm = .ok (n + 1) →
    B.pop er (.dynamicArray elem) evm = .ok evm' →
    B.length er (.dynamicArray elem) evm' = .ok n

  /-- The removed element is cleared, with the same mapping exception as `clear`. -/
  read_pop_removed : ∀ {er elem evm evm' n suffix ty'},
    Ref decls er (.dynamicArray elem) →
    B.length er (.dynamicArray elem) evm = .ok (n + 1) →
    B.pop er (.dynamicArray elem) evm = .ok evm' →
    Ref decls (er.extend (.aindex (.int n) :: suffix)) ty' →
    ¬ ThroughMapping suffix → MappingFree ty' →
    InBounds decls B evm (er.extend (.aindex (.int n) :: suffix)) →
    B.read (er.extend (.aindex (.int n) :: suffix)) ty' evm' = defaultValue? ty'

  read_pop_old : ∀ {er elem evm evm' n} {i : Nat} {suffix ty'},
    Ref decls er (.dynamicArray elem) →
    B.length er (.dynamicArray elem) evm = .ok (n + 1) → i < n →
    B.pop er (.dynamicArray elem) evm = .ok evm' →
    Ref decls (er.extend (.aindex (.int i) :: suffix)) ty' →
    B.read (er.extend (.aindex (.int i) :: suffix)) ty' evm' =
      B.read (er.extend (.aindex (.int i) :: suffix)) ty' evm

  -- ### Bytes and strings: push and pop, observed through the whole value

  read_push_byte_none : ∀ {er ty b evm evm'},
    Ref decls er ty → (ty = .bytes ∨ ty = .string) →
    B.read er ty evm = .ok (.bytes b) →
    B.push er ty none evm = .ok evm' →
    B.read er ty evm' = .ok (.bytes (b.push 0))

  read_push_byte : ∀ {er ty b evm evm'} {x : UInt8},
    Ref decls er ty → (ty = .bytes ∨ ty = .string) →
    B.read er ty evm = .ok (.bytes b) →
    B.push er ty (some (.fixedBytes 0 [x])) evm = .ok evm' →
    B.read er ty evm' = .ok (.bytes (b.push x))

  pop_byte_empty : ∀ {er ty evm},
    Ref decls er ty → (ty = .bytes ∨ ty = .string) →
    B.read er ty evm = .ok (.bytes ByteArray.empty) →
    B.pop er ty evm = .revert

  read_pop_byte : ∀ {er ty b evm evm'},
    Ref decls er ty → (ty = .bytes ∨ ty = .string) →
    B.read er ty evm = .ok (.bytes b) → 0 < b.size →
    B.pop er ty evm = .ok evm' →
    B.read er ty evm' = .ok (.bytes (b.extract 0 (b.size - 1)))

/-! ## Intended Solidity instance (not yet stated formally)

```
/-- Bit-level physical footprint of a reference in a state: the bits of its leaf location, the
    header slot and data words of a bytes/string, and for a dynamic array its length slot plus the
    footprints of the elements below its current length. -/
def solidityFootprint (layout : StorageLayout) (er : EvaledStorageRef) (ty : StorageType)
    (evm : EVM.State) : Set (EVM.Word × Fin 256)

def soliditySep (layout : StorageLayout) : Separation :=
  fun evm evm' r₁ t₁ r₂ t₂ =>
    Disjoint (solidityFootprint layout r₁ t₁ evm ∪ solidityFootprint layout r₁ t₁ evm')
             (solidityFootprint layout r₂ t₂ evm)

/-- What the generic proof needs from a locator: well-typed leaves are located at their type with
    the right size, dynamically-sized values at an anchor, and bytes elements symbolically. -/
def SolidityLayoutOK (decls : List StorageDecl) (layout : StorageLayout) : Prop

theorem solidityStorageBackend_lawful (h : SolidityLayoutOK decls layout) :
    LawfulStorageBackend decls (solidityStorageBackend layout) (soliditySep layout)

/-- The non-conflict part: references that diverge at a static step (a struct field, or a fixed
    offset under a shared dynamic prefix) are separated with no keccak assumption, provided the
    static allocation does not overlap. That is a decidable property of the layout, which
    `solidityLayout!` could emit as a theorem. -/
theorem soliditySep_of_static_divergence ...
```
-/

end StorageLaws
end Solm
