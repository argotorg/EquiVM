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
  /-- Explicit base call `B.f(…)`: the implementation `B` itself would use, for `(B, key)`. -/
  baseTable : List ((Ident × FnKey) × FnId)
  /-- The hierarchy's modifiers, then the libraries'. -/
  modifiers : Array ModDef
  /-- Most-derived implementation of each modifier of the hierarchy. -/
  modVtable : List (Ident × Nat)
  modSuper : List ((Ident × Ident) × Nat)
  /-- Base-first. -/
  ctorChain : List CtorStep
  entries : List DispatchEntry
  receive? : Option FnId
  fallback? : Option FnId
  /-- Events and errors of every unit (the hierarchy's, the file's, the libraries', other units'). -/
  events : List EventInfo
  errors : List ErrorInfo
  /-- `(unit where written, directive)`: a directive applies to code of that unit only. -/
  usingFor : List (Ident × UsingFor)
  libraries : List ContractDecl
  /-- Own (non-inherited) function signatures per contract-like unit, for `type(I).interfaceId`. -/
  interfaceSigs : List (Ident × List String)
  /-- Every function (own and inherited) of every contract-like unit, for external calls through
      contract / interface types. -/
  contractFns : List (Ident × List FnDecl)
  /-- Constructor parameters of every contract-like unit, for `new C(args)` and base arguments. -/
  contractCtors : List (Ident × List Param)
  /-- File-level functions (shadowed by contract functions of the same name). -/
  freeFns : List (FnKey × FnId) := []
  /-- Functions of the libraries, by library. -/
  unitFns : List (Ident × FnKey × FnId) := []
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
  -- Type environment: every struct and enum with its declaring unit (the file is `""`).
  let linOf (c : Ident) : List Ident :=
    (linearize (fun c => (find c).map (·.bases.map (·.name))) (contracts.length + 1) c).getD [c]
  let structsOf (d : ContractDecl) : List StructInfo :=
    d.structs.map fun s => { qual := some d.name, name := s.name, fields := s.fields }
  let enumsOf (d : ContractDecl) : List EnumInfo :=
    d.enums.map fun e => { qual := some d.name, name := e.name, members := e.members }
  let fileStructs := p.filterMap fun | .struct s => some ({ qual := some "", name := s.name, fields := s.fields } : StructInfo) | _ => none
  let fileEnums := p.filterMap fun | .enum e => some ({ qual := some "", name := e.name, members := e.members } : EnumInfo) | _ => none
  let env0 : TypeEnv :=
    { structs := contracts.flatMap structsOf ++ fileStructs
      enums := contracts.flatMap enumsOf ++ fileEnums
      contracts := contracts.map fun d => (d.name, d.kind)
      lins := contracts.map fun d => (d.name, linOf d.name) }
  -- Types in declarations are written in the scope of their unit: make them canonical.
  let canon (here : Ident) (t : Ty) : Ty := env0.canonTy here t
  let canonParams (here : Ident) (ps : List Param) : List Param := ps.map fun q => { q with ty := canon here q.ty }
  let canonFn (here : Ident) (f : FnDecl) : FnDecl :=
    { f with params := canonParams here f.params, returns := canonParams here f.returns }
  let canonEvent (here : Ident) (e : EventDecl) : EventDecl :=
    { e with params := e.params.map fun q => { q with ty := canon here q.ty } }
  let canonError (here : Ident) (e : ErrorDecl) : ErrorDecl := { e with params := canonParams here e.params }
  let env : TypeEnv :=
    { env0 with structs := env0.structs.map fun s =>
        { s with fields := s.fields.map fun (t, f) => (canon (s.qual.getD "") t, f) } }
  -- State variables, base-first.
  let baseFirst := hier.reverse
  let rawVars := baseFirst.flatMap fun d => d.stateVars.map fun v => (d.name, v)
  let dup (n : Ident) : Bool := (rawVars.filter (·.2.name == n)).length > 1
  let stateVars : List FlatVar := rawVars.map fun (c, v) =>
    { key := if dup v.name then s!"{c}.{v.name}" else v.name, name := v.name, declaredIn := c,
      ty := canon c v.ty, visibility := v.visibility, mutability := v.mutability, init := v.init }
  -- Immutables are kept by name (`imm_<name>`): two with one name would be one.
  let immNames := (stateVars.filter (·.mutability == .immutable)).map (·.name)
  if immNames.eraseDups.length != immNames.length then
    throw "two immutables with one name (a private one in a base) are not supported"
  -- Functions (most-derived first) with ids.
  let rawFns := hier.flatMap fun d => d.fns.map fun f => (d.name, canonFn d.name f)
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
  let baseTable : List ((Ident × FnKey) × FnId) := lin.flatMap fun c =>
    let from_ := lin.dropWhile (· != c)
    keys.filterMap fun k =>
      (functionDefs.find? fun f => from_.contains f.declaredIn && fnKeyOf f.decl == k).map fun f =>
        ((c, k), f.id)
  -- Modifiers.
  let rawMods := hier.flatMap fun d => d.modifiers.map fun m =>
    (d.name, { m with params := canonParams d.name m.params })
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
  let freeDefs : List FnDef := (p.filterMap fun | .function d => some d | _ => none).zipIdx.map fun (f, i) =>
    { id := fns0.size + getterDefs.length + i, declaredIn := "", decl := canonFn "" f }
  -- Library functions (called by name from their own library, by `L.f` and `using for` elsewhere).
  let libraries := (contracts.filter (·.kind == .library)).map fun d =>
    { d with items := d.items.map fun | .fn f => .fn (canonFn d.name f) | i => i }
  let libDefs : List FnDef := (libraries.flatMap fun d => d.functions.map fun f => (d.name, f)).zipIdx.map fun ((c, f), i) =>
    { id := fns0.size + getterDefs.length + freeDefs.length + i, declaredIn := c, decl := f }
  -- Library modifiers (for the functions of their own library), after the hierarchy's.
  let libMods : List ModDef := (libraries.flatMap fun d => d.modifiers.map fun m =>
      (d.name, { m with params := canonParams d.name m.params })).zipIdx.map fun ((c, m), i) =>
    { id := modifiers.size + i, declaredIn := c, decl := m }
  let fns := fns0 ++ getterDefs.toArray ++ freeDefs.toArray ++ libDefs.toArray
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
  -- Events and errors, each with its declaring unit (the hierarchy's, the file's, the libraries').
  let eventsOfUnit (c : Ident) (es : List EventDecl) : Except String (List EventInfo) :=
    es.mapM fun e =>
      let e := canonEvent c e
      match sigOf env e.name (eventTys e) with
      | some sig => pure ({ declaredIn := c, decl := e, sig := sig, sigStr := ABI.printSignature sig } : EventInfo)
      | none => throw s!"event `{e.name}` has a parameter type without ABI encoding"
  let errorsOfUnit (c : Ident) (es : List ErrorDecl) : Except String (List ErrorInfo) :=
    es.mapM fun e =>
      let e := canonError c e
      match sigOf env e.name (tysOfParams e.params) with
      | some sig => pure ({ declaredIn := c, decl := e, sig := sig, sigStr := ABI.printSignature sig } : ErrorInfo)
      | none => throw s!"error `{e.name}` has a parameter type without ABI encoding"
  let events ← hier.flatMapM fun d => eventsOfUnit d.name d.events
  let errors ← hier.flatMapM fun d => errorsOfUnit d.name d.errors
  let fileEvents ← eventsOfUnit "" (p.filterMap fun | .event e => some e | _ => none)
  let fileErrors ← errorsOfUnit "" (p.filterMap fun | .error e => some e | _ => none)
  let libEvents ← libraries.flatMapM fun d => eventsOfUnit d.name d.events
  let libErrors ← libraries.flatMapM fun d => errorsOfUnit d.name d.errors
  -- Other units (an interface or a contract outside the hierarchy), for `Q.Ev` / `Q.Err`; one
  -- without ABI encoding is left out.
  let others := contracts.filter fun d => d.kind != .library && !lin.contains d.name
  let otherEvents := others.flatMap fun d => d.events.flatMap fun e => (eventsOfUnit d.name [e]).toOption.getD []
  let otherErrors := others.flatMap fun d => d.errors.flatMap fun e => (errorsOfUnit d.name [e]).toOption.getD []
  -- Constants of the file and of the libraries.
  let fileConsts : List FlatVar := (p.filterMap fun | .constant v => some v | _ => none).map fun v =>
    { key := v.name, name := v.name, declaredIn := "", ty := canon "" v.ty, visibility := .internal,
      mutability := .constant, init := v.init }
  let libConsts : List FlatVar := libraries.flatMap fun d =>
    (d.stateVars.filter (·.mutability == .constant)).map fun v =>
      { key := v.name, name := v.name, declaredIn := d.name, ty := canon d.name v.ty, visibility := .internal,
        mutability := .constant, init := v.init }
  let usingFor := contracts.flatMap fun d => d.usings.map fun u => (d.name, { u with ty := u.ty.map (canon d.name) })
  let interfaceSigs := contracts.map fun d =>
    (d.name, d.functions.filterMap fun f => sigStrOf env f.name (tysOfParams (canonParams d.name f.params)))
  let contractFns := contracts.map fun d =>
    (d.name, (linOf d.name).flatMap fun c => ((find c).map fun cd => cd.functions.map (canonFn c)).getD [])
  let contractCtors := contracts.map fun d => (d.name, (d.ctor?.map fun c => canonParams d.name c.params).getD [])
  let isAbstract := root.kind == .abstractContract || root.kind == .interface ||
    vtable.any fun e => (fns[e.2]!).decl.body.isNone
  pure
    { name := target, kind := root.kind, linearization := lin, types := env,
      stateVars := stateVars ++ fileConsts ++ libConsts, fns := fns, vtable := vtable, superTable := superTable,
      baseTable := baseTable,
      modifiers := modifiers ++ libMods.toArray, modVtable := modVtable, modSuper := modSuper,
      ctorChain := ctorChain, entries := entries, receive? := receive?, fallback? := fallback?,
      events := events ++ fileEvents ++ libEvents ++ otherEvents,
      errors := errors ++ fileErrors ++ libErrors ++ otherErrors, usingFor := usingFor,
      libraries := libraries,
      interfaceSigs := interfaceSigs, contractFns := contractFns, contractCtors := contractCtors,
      freeFns := freeDefs.map fun f => (fnKeyOf f.decl, f.id),
      unitFns := libDefs.map fun f => (f.declaredIn, fnKeyOf f.decl, f.id), isAbstract := isAbstract }

/-! ## Queries -/

namespace FlatContract

def fn? (fc : FlatContract) (id : FnId) : Option FnDef := fc.fns[id]?

/-! Names are resolved from the unit whose code is running (`here`: a contract of the hierarchy, a
library, or `""` for a file-level function): its own declarations and those of its bases, then the
file's.  `…Of q` is the qualified form `q.name`. -/

/-- The variable or constant `q.x`: declared in `q`, or visible in it from a base. -/
def varOf (fc : FlatContract) (q x : Ident) : Option FlatVar :=
  (fc.types.unitLin q).findSome? fun u =>
    fc.stateVars.find? fun v => v.name == x && v.declaredIn == u && (u == q || v.visibility != .priv)

/-- The variable or constant `x` names in code of `here`. -/
def varIn (fc : FlatContract) (here x : Ident) : Option FlatVar :=
  match fc.varOf here x with
  | some v => some v
  | none => fc.stateVars.find? fun v => v.name == x && v.declaredIn == ""

/-- The functions named `f` of library `q`. -/
def unitFnsNamed (fc : FlatContract) (q f : Ident) : List (FnKey × FnId) :=
  fc.unitFns.filterMap fun (u, k, id) => if u == q && k.name == f then some (k, id) else none

/-- Candidates for a call of `f` in code of `here` (overloads): the hierarchy's implementations
    when `here` is one of its contracts, the unit's own functions otherwise; else the file's. -/
def fnsNamedIn (fc : FlatContract) (here f : Ident) : List (FnKey × FnId) :=
  match (if fc.linearization.contains here then fc.vtable.filter (·.1.name == f) else fc.unitFnsNamed here f) with
  | [] => fc.freeFns.filter (·.1.name == f)
  | cs => cs

/-- Parameter lists of candidate functions (named-argument matching). -/
def candParams (fc : FlatContract) (cands : List (FnKey × FnId)) : List (List Param) :=
  cands.filterMap fun c => (fc.fns[c.2]?).map (·.decl.params)

def superFn? (fc : FlatContract) (from_ : Ident) (k : FnKey) : Option FnId :=
  (fc.superTable.find? (·.1 == (from_, k))).map (·.2)

def modifier? (fc : FlatContract) (name : Ident) : Option ModDef :=
  (fc.modVtable.find? (·.1 == name)).bind fun (_, id) => fc.modifiers[id]?

/-- The modifier `name` names in code of `here`: the most derived implementation when `here` is a
    contract of the hierarchy, the unit's own modifier otherwise (a library's). -/
def modifierIn (fc : FlatContract) (here name : Ident) : Option ModDef :=
  if fc.linearization.contains here then fc.modifier? name
  else fc.modifiers.toList.find? fun m => m.declaredIn == here && m.decl.name == name

/-- The events `q.ev` (overloads): declared in `q` or inherited by it. -/
def eventsOf (fc : FlatContract) (q ev : Ident) : List EventInfo :=
  fc.events.filter fun e => e.decl.name == ev && (fc.types.unitLin q).contains e.declaredIn

/-- The events `ev` names in code of `here` (overloads). -/
def eventsNamedIn (fc : FlatContract) (here ev : Ident) : List EventInfo :=
  match fc.eventsOf here ev with
  | [] => fc.events.filter fun e => e.decl.name == ev && e.declaredIn == ""
  | es => es

/-- The error `q.name`. -/
def errorOf (fc : FlatContract) (q name : Ident) : Option ErrorInfo :=
  (fc.types.unitLin q).findSome? fun u => fc.errors.find? fun e => e.decl.name == name && e.declaredIn == u

/-- The error `name` names in code of `here`. -/
def errorIn (fc : FlatContract) (here name : Ident) : Option ErrorInfo :=
  match fc.errorOf here name with
  | some e => some e
  | none => fc.errors.find? fun e => e.decl.name == name && e.declaredIn == ""

def sigStrs (fc : FlatContract) : List String := fc.entries.map (·.sigStr)

/-- Functions named `name` of contract-like unit `c` (external-call resolution). -/
def contractFnsNamed (fc : FlatContract) (c name : Ident) : List FnDecl :=
  ((fc.contractFns.find? (·.1 == c)).map (·.2)).getD [] |>.filter (·.name == name)

/-- Constructor parameters of contract-like unit `c`. -/
def ctorParams? (fc : FlatContract) (c : Ident) : Option (List Param) :=
  (fc.contractCtors.find? (·.1 == c)).map (·.2)

def ctorTys? (fc : FlatContract) (c : Ident) : Option (List Ty) :=
  (fc.ctorParams? c).map (·.map (·.ty))

/-- The constructor of `c` as a candidate list (named-argument matching). -/
def ctorParamss (fc : FlatContract) (c : Ident) : List (List Param) :=
  (fc.ctorParams? c).toList

def library? (fc : FlatContract) (name : Ident) : Option ContractDecl :=
  fc.libraries.find? (·.name == name)

/-- Storage-relevant variables (constants and immutables take no slot). -/
def storageVars (fc : FlatContract) : List FlatVar :=
  fc.stateVars.filter (·.mutability == .mutable)

end FlatContract

end Solidity
