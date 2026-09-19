import Solidity.Types

/-!
# Elaboration: program + target contract → `FlatContract`

The static pre-pass solc performs before code generation: C3 linearization, state-variable order
(base-first), override/`super` resolution for functions and modifiers, the constructor chain with
its base arguments, public-variable getters, canonical event/error signatures and the dispatch
table (signature strings only — selectors need keccak and are computed by the semantics).
Everything here is keccak-free, so it evaluates under `#guard`/`decide`.
-/

namespace Solidity

structure FnKey where
  name : Ident
  paramTys : List Ty
  deriving DecidableEq, Repr, Inhabited

abbrev FnId := Nat

structure FnDef where
  id : FnId
  declaredIn : Ident
  decl : FnDecl
  deriving Repr, Inhabited

structure ModDef where
  id : Nat
  declaredIn : Ident
  decl : ModifierDecl
  deriving Repr, Inhabited

structure FlatVar where
  /-- Storage-path base name: the plain name, or `Declaring.name` when shadowed privately. -/
  key : Ident
  name : Ident
  declaredIn : Ident
  ty : Ty
  visibility : Visibility
  mutability : VarMutability
  init : Option Expr
  deriving Repr, Inhabited

structure DispatchEntry where
  sigStr : String
  sig : ABI.Signature
  fn : FnId
  isGetter : Bool
  deriving Repr

structure CtorStep where
  contract : Ident
  fn : Option FnId
  /-- Base-constructor arguments and the contract in whose context they are evaluated. -/
  args : Option (Ident × Args)
  deriving Repr, Inhabited

structure EventInfo where
  declaredIn : Ident
  decl : EventDecl
  sig : ABI.Signature
  sigStr : String
  deriving Repr

structure ErrorInfo where
  declaredIn : Ident
  decl : ErrorDecl
  sig : ABI.Signature
  sigStr : String
  deriving Repr

structure FlatContract where
  name : Ident
  kind : ContractKind
  /-- C3 linearization, most-derived first. -/
  linearization : List Ident
  types : TypeEnv
  /-- Base-first, declaration order; includes constants and immutables. -/
  stateVars : List FlatVar
  /-- Every function and constructor of the hierarchy (getters appended), by `FnId`. -/
  fns : Array FnDef
  /-- Most-derived implementation of each key. -/
  vtable : List (FnKey × FnId)
  /-- `super` target for `(contract containing the call, key)`. -/
  superTable : List ((Ident × FnKey) × FnId)
  modifiers : Array ModDef
  modVtable : List (Ident × Nat)
  modSuper : List ((Ident × Ident) × Nat)
  /-- Base-first. -/
  ctorChain : List CtorStep
  entries : List DispatchEntry
  receive? : Option FnId
  fallback? : Option FnId
  events : List EventInfo
  errors : List ErrorInfo
  /-- `(contract where written, directive)`. -/
  usingFor : List (Ident × UsingFor)
  libraries : List ContractDecl
  /-- Own (non-inherited) function signatures per contract-like unit, for `type(I).interfaceId`. -/
  interfaceSigs : List (Ident × List String)
  /-- Every function (own and inherited) of every contract-like unit, for external calls through
      contract / interface types. -/
  contractFns : List (Ident × List FnDecl)
  /-- Constructor parameter types of every contract-like unit, for `new C(args)`. -/
  contractCtors : List (Ident × List Ty)
  isAbstract : Bool
  deriving Repr, Inhabited

/-! ## C3 linearization -/

/-- C3 merge: repeatedly take the first head that occurs in no tail. -/
def c3Merge : Nat → List (List Ident) → Option (List Ident)
  | 0, _ => none
  | fuel + 1, seqs =>
    let seqs := seqs.filter (!·.isEmpty)
    if seqs.isEmpty then some []
    else
      let candidate := seqs.findSome? fun s =>
        match s with
        | [] => none
        | h :: _ => if seqs.all (fun t => !(t.drop 1).contains h) then some h else none
      match candidate with
      | none => none
      | some h =>
        let seqs' := seqs.map fun s => if s.head? == some h then s.drop 1 else s
        (c3Merge fuel seqs').map (h :: ·)

/-- `L(C) = C :: merge(L(Bn), …, L(B1), [Bn, …, B1])` for `contract C is B1, …, Bn`. -/
def linearize (bases : Ident → Option (List Ident)) : Nat → Ident → Option (List Ident)
  | 0, _ => none
  | fuel + 1, c => do
    let bs ← bases c
    let bsRev := bs.reverse
    let ls ← bsRev.mapM (linearize bases fuel)
    let total := ls.foldl (· + ·.length) 0 + bsRev.length + 1
    let merged ← c3Merge total (ls ++ [bsRev])
    pure (c :: merged)

/-! ## Getters -/

/-- Peel mapping keys / array indices into parameters; returns `(params, access expr, returns)`. -/
def getterShape (env : TypeEnv) : Ty → Nat → List Param → List Stmt → Expr →
    List Param × List Stmt × Expr × List Param
  | .mapping k v, i, ps, gs, e =>
    let arg := s!"arg{i}"
    getterShape env v (i + 1) (ps ++ [{ ty := k, name := some arg }]) gs (.index e (.ident arg))
  | .array el n, i, ps, gs, e =>
    let arg := s!"arg{i}"
    getterShape env el (i + 1) (ps ++ [{ ty := Ty.uint256, name := some arg }])
      (gs ++ [boundsGuard (.ident arg) (.lit (.number n none))]) (.index e (.ident arg))
  | .dynArray el, i, ps, gs, e =>
    let arg := s!"arg{i}"
    getterShape env el (i + 1) (ps ++ [{ ty := Ty.uint256, name := some arg }])
      (gs ++ [boundsGuard (.ident arg) (.member e "length")]) (.index e (.ident arg))
  | .user q n, _, ps, gs, e =>
    match env.struct? q n with
    | some s =>
      let members := s.fields.filter fun (t, _) => isGetterMemberType t
      let rets := members.map fun (t, f) => ({ ty := t, name := some f } : Param)
      let body := match members with
        | [(_, f)] => Expr.member e f
        | _ => .tuple (members.map fun (_, f) => some (.member e f))
      (ps, gs, body, rets)
    | none => (ps, gs, e, [{ ty := .user q n }])
  | t, _, ps, gs, e => (ps, gs, e, [{ ty := t }])
where
  /-- `require(i < len)`: solc's legacy getters revert with empty data on an out-of-range index. -/
  boundsGuard (i len : Expr) : Stmt :=
    .exprStmt (.call (.ident "require") [] (.positional [.binary .lt i len]))

/-- The public getter of a state variable (`external view`; index bounds guards, then
    `return <access>;`). -/
def synthGetter (env : TypeEnv) (v : FlatVar) : FnDecl :=
  let (params, guards, access, rets) := getterShape env v.ty 0 [] [] (.ident v.name)
  { kind := .function, name := v.name, params := params, returns := rets,
    visibility := some .external, mutability := .view,
    body := some (guards ++ [.return (some access)]) }

/-! ## Elaboration -/

private def fnKeyOf (d : FnDecl) : FnKey := ⟨d.name, d.params.map (·.ty)⟩

private def isExternal (d : FnDecl) : Bool :=
  d.visibility == some .external || d.visibility == some .pub

private def tysOfParams (ps : List Param) : List Ty := ps.map (·.ty)

private def eventTys (e : EventDecl) : List Ty := e.params.map (·.ty)

/-- Explicit base-constructor arguments written for base `b` anywhere in the hierarchy. -/
private def ctorArgsFor (hier : List ContractDecl) (b : Ident) : Except String (Option (Ident × Args)) := do
  let found := hier.filterMap fun d =>
    let inBases := d.bases.findSome? fun bs => if bs.name == b then bs.args.map (d.name, ·) else none
    let inCtor := (d.ctor?.bind fun c => c.modifiers.findSome? fun m =>
      if m.name == b then m.args.map (d.name, ·) else none)
    match inBases, inCtor with
    | some a, none => some (some a)
    | none, some a => some (some a)
    | some _, some _ => some none        -- both forms in one contract
    | none, none => none
  match found with
  | [] => pure none
  | [some a] => pure (some a)
  | _ => throw s!"base constructor arguments for `{b}` given more than once"

def elabProgram (p : Program) (target : Ident) : Except String FlatContract := do
  let contracts := p.filterMap SourceUnit.contract?
  let find (n : Ident) : Option ContractDecl := contracts.find? (·.name == n)
  let some root := find target | throw s!"unknown contract `{target}`"
  let some lin := linearize (fun c => (find c).map (·.bases.map (·.name))) (contracts.length + 1) target
    | throw s!"cannot linearize `{target}` (missing base or inconsistent order)"
  let hier ← lin.mapM fun c => match find c with
    | some d => pure d
    | none => throw s!"unknown base contract `{c}`"
  -- Type environment: hierarchy (most-derived first), file-level, then everything else.
  let structsOf (d : ContractDecl) : List StructInfo :=
    d.structs.map fun s => { qual := some d.name, name := s.name, fields := s.fields }
  let enumsOf (d : ContractDecl) : List EnumInfo :=
    d.enums.map fun e => { qual := some d.name, name := e.name, members := e.members }
  let fileStructs := p.filterMap fun | .struct s => some ({ qual := none, name := s.name, fields := s.fields } : StructInfo) | _ => none
  let fileEnums := p.filterMap fun | .enum e => some ({ qual := none, name := e.name, members := e.members } : EnumInfo) | _ => none
  let others := contracts.filter fun d => !lin.contains d.name
  let env : TypeEnv :=
    { structs := hier.flatMap structsOf ++ fileStructs ++ others.flatMap structsOf
      enums := hier.flatMap enumsOf ++ fileEnums ++ others.flatMap enumsOf
      contracts := contracts.map fun d => (d.name, d.kind) }
  -- State variables, base-first.
  let baseFirst := hier.reverse
  let rawVars := baseFirst.flatMap fun d => d.stateVars.map fun v => (d.name, v)
  let dup (n : Ident) : Bool := (rawVars.filter (·.2.name == n)).length > 1
  let stateVars : List FlatVar := rawVars.map fun (c, v) =>
    { key := if dup v.name then s!"{c}.{v.name}" else v.name, name := v.name, declaredIn := c,
      ty := v.ty, visibility := v.visibility, mutability := v.mutability, init := v.init }
  -- Functions (most-derived first) with ids.
  let rawFns := hier.flatMap fun d => d.fns.map fun f => (d.name, f)
  let fns0 : Array FnDef := (rawFns.zipIdx.map fun ((c, f), i) => ({ id := i, declaredIn := c, decl := f } : FnDef)).toArray
  let functionDefs := fns0.toList.filter (·.decl.kind == .function)
  let keys := (functionDefs.map (fnKeyOf ·.decl)).eraseDups
  let vtable0 : List (FnKey × FnId) := keys.filterMap fun k =>
    (functionDefs.find? fun f => fnKeyOf f.decl == k).map fun f => (k, f.id)
  let superTable : List ((Ident × FnKey) × FnId) := lin.flatMap fun c =>
    let after := (lin.dropWhile (· != c)).drop 1
    keys.filterMap fun k =>
      (functionDefs.find? fun f => after.contains f.declaredIn && fnKeyOf f.decl == k).map fun f =>
        ((c, k), f.id)
  -- Modifiers.
  let rawMods := hier.flatMap fun d => d.modifiers.map fun m => (d.name, m)
  let modifiers : Array ModDef := (rawMods.zipIdx.map fun ((c, m), i) => ({ id := i, declaredIn := c, decl := m } : ModDef)).toArray
  let modNames := (modifiers.toList.map (·.decl.name)).eraseDups
  let modVtable := modNames.filterMap fun n =>
    (modifiers.toList.find? (·.decl.name == n)).map fun m => (n, m.id)
  let modSuper : List ((Ident × Ident) × Nat) := lin.flatMap fun c =>
    let after := (lin.dropWhile (· != c)).drop 1
    modNames.filterMap fun n =>
      (modifiers.toList.find? fun m => after.contains m.declaredIn && m.decl.name == n).map fun m =>
        ((c, n), m.id)
  -- Getters for public state variables (appended, shadowing same-key functions in the vtable).
  let publicVars := stateVars.filter (·.visibility == .pub)
  let getterDefs : List FnDef := publicVars.zipIdx.map fun (v, i) =>
    { id := fns0.size + i, declaredIn := v.declaredIn, decl := synthGetter env v }
  let fns := fns0 ++ getterDefs.toArray
  let vtable := getterDefs.foldl (fun vt g =>
      let k := fnKeyOf g.decl
      (k, g.id) :: vt.filter (·.1 != k)) vtable0
  -- Constructor chain, base-first.
  let ctorChain ← baseFirst.mapM fun d => do
    let fn := (fns0.toList.find? fun f => f.declaredIn == d.name && f.decl.kind == .ctor).map (·.id)
    let args ← ctorArgsFor hier d.name
    pure ({ contract := d.name, fn := fn, args := args } : CtorStep)
  -- Dispatch entries: external/public functions (most-derived) + getters.
  let entryOpts ← vtable.reverse.mapM fun e => do
    let f := fns[e.2]!
    if !(isExternal f.decl) then pure (none : Option DispatchEntry)
    else
      match sigOf env e.1.name e.1.paramTys with
      | some sig =>
        let entry : DispatchEntry :=
          { sigStr := ABI.printSignature sig, sig := sig, fn := e.2, isGetter := e.2 ≥ fns0.size }
        pure (some entry)
      | none => throw s!"function `{e.1.name}` has a parameter type without ABI encoding"
  let entries := entryOpts.filterMap id
  let receive? := (fns0.toList.find? (·.decl.kind == .receive)).map (·.id)
  let fallback? := (fns0.toList.find? (·.decl.kind == .fallback)).map (·.id)
  -- Events and errors across the hierarchy.
  let events ← hier.flatMapM fun d => d.events.mapM fun e =>
    match sigOf env e.name (eventTys e) with
    | some sig => pure ({ declaredIn := d.name, decl := e, sig := sig, sigStr := ABI.printSignature sig } : EventInfo)
    | none => throw s!"event `{e.name}` has a parameter type without ABI encoding"
  let errors ← hier.flatMapM fun d => d.errors.mapM fun e =>
    match sigOf env e.name (tysOfParams e.params) with
    | some sig => pure ({ declaredIn := d.name, decl := e, sig := sig, sigStr := ABI.printSignature sig } : ErrorInfo)
    | none => throw s!"error `{e.name}` has a parameter type without ABI encoding"
  let usingFor := hier.flatMap fun d => d.usings.map fun u => (d.name, u)
  let libraries := contracts.filter (·.kind == .library)
  let interfaceSigs := contracts.map fun d =>
    (d.name, d.functions.filterMap fun f => sigStrOf env f.name (tysOfParams f.params))
  let contractFns := contracts.map fun d =>
    let hierOf := (linearize (fun c => (find c).map (·.bases.map (·.name))) (contracts.length + 1) d.name).getD [d.name]
    (d.name, hierOf.flatMap fun c => ((find c).map (·.functions)).getD [])
  let contractCtors := contracts.map fun d => (d.name, (d.ctor?.map fun f => f.params.map (·.ty)).getD [])
  let isAbstract := root.kind == .abstractContract || root.kind == .interface ||
    vtable.any fun e => (fns[e.2]!).decl.body.isNone
  pure
    { name := target, kind := root.kind, linearization := lin, types := env,
      stateVars := stateVars, fns := fns, vtable := vtable, superTable := superTable,
      modifiers := modifiers, modVtable := modVtable, modSuper := modSuper,
      ctorChain := ctorChain, entries := entries, receive? := receive?, fallback? := fallback?,
      events := events, errors := errors, usingFor := usingFor, libraries := libraries,
      interfaceSigs := interfaceSigs, contractFns := contractFns, contractCtors := contractCtors,
      isAbstract := isAbstract }

/-! ## Queries -/

namespace FlatContract

def fn? (fc : FlatContract) (id : FnId) : Option FnDef := fc.fns[id]?

def var? (fc : FlatContract) (name : Ident) : Option FlatVar :=
  fc.stateVars.find? (·.name == name)

/-- Vtable candidates named `name` (overloads). -/
def fnsNamed (fc : FlatContract) (name : Ident) : List (FnKey × FnId) :=
  fc.vtable.filter (·.1.name == name)

def superFn? (fc : FlatContract) (from_ : Ident) (k : FnKey) : Option FnId :=
  (fc.superTable.find? (·.1 == (from_, k))).map (·.2)

def modifier? (fc : FlatContract) (name : Ident) : Option ModDef :=
  (fc.modVtable.find? (·.1 == name)).bind fun (_, id) => fc.modifiers[id]?

def event? (fc : FlatContract) (name : Ident) : Option EventInfo :=
  fc.events.find? (·.decl.name == name)

def error? (fc : FlatContract) (name : Ident) : Option ErrorInfo :=
  fc.errors.find? (·.decl.name == name)

def sigStrs (fc : FlatContract) : List String := fc.entries.map (·.sigStr)

/-- Functions named `name` of contract-like unit `c` (external-call resolution). -/
def contractFnsNamed (fc : FlatContract) (c name : Ident) : List FnDecl :=
  ((fc.contractFns.find? (·.1 == c)).map (·.2)).getD [] |>.filter (·.name == name)

/-- Constructor parameter types of contract-like unit `c`. -/
def ctorTys? (fc : FlatContract) (c : Ident) : Option (List Ty) :=
  (fc.contractCtors.find? (·.1 == c)).map (·.2)

def library? (fc : FlatContract) (name : Ident) : Option ContractDecl :=
  fc.libraries.find? (·.name == name)

/-- Storage-relevant variables (constants and immutables take no slot). -/
def storageVars (fc : FlatContract) : List FlatVar :=
  fc.stateVars.filter (·.mutability == .mutable)

end FlatContract

end Solidity
