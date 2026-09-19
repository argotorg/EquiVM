import Solidity.Semantics.Calls

/-!
# Relational big-step semantics

`EvalExpr`/`ExecStmt`/… are inductive predicates over `Frame × Machine`.  Every premise is a
sub-derivation or an equation on a pure helper from `Ops.lean`, so the interpreter mirrors the
rules one-to-one.  Reverts carry their data; ill-formed programs have no derivation.

Evaluation order is source order (left to right); for assignments the right-hand side is
evaluated before the left-hand side (both solc code generators).  `require`/`revert` messages
are evaluated only when the condition fails.
-/

namespace Solidity

open ABI

/-! ## Pure helpers -/

def unitMul : Option SubDenom → Nat
  | none | some .wei | some .seconds => 1
  | some .gwei => 10 ^ 9
  | some .ether => 10 ^ 18
  | some .minutes => 60
  | some .hours => 3600
  | some .days => 86400
  | some .weeks => 604800

def literalValue : Literal → Option Value
  | .number n u => some (.literal (n * unitMul u))
  | .decimal m e u =>
    if e ≥ 0 then some (.literal (m * 10 ^ e.toNat * unitMul u))
    else
      let d := 10 ^ (-e).toNat
      if m % d = 0 then some (.literal (m / d * unitMul u)) else none
  | .bool b => some (.bool b)
  | .str s => some (.strLit s.toUTF8)
  | .unicodeStr s => some (.strLit s.toUTF8)
  | .hexStr bs => some (.strLit (ByteArray.mk bs.toArray))

def interfaceIdOf (fc : FlatContract) (n : Ident) : Option Value :=
  (fc.interfaceSigs.find? (·.1 == n)).map fun (_, sigs) =>
    let x := sigs.foldl (fun acc s => acc ^^^ bytesToNatBE (selectorOf s).toList) 0
    .fixedBytes ⟨3, by decide⟩ (natToBytesBE x 4)

/-- `type(T).member`. -/
def typeMember (fc : FlatContract) (ty : Ty) (member : Ident) : Option Value :=
  match ty, member with
  | .uint w, "max" => some (.uint w (2 ^ w.val - 1))
  | .uint w, "min" => some (.uint w 0)
  | .int w, "max" => some (.sint w (2 ^ (w.val - 1) - 1))
  | .int w, "min" => some (.sint w (-(2 ^ (w.val - 1) : Nat)))
  | .user _ n, "interfaceId" => interfaceIdOf fc n
  | _, _ => none

def immName (x : Ident) : Ident := "imm_" ++ x

/-- Read of an immutable: the constructor's local, else the deployed value, else zero. -/
def immutableValue (cfg : Config) (env : TypeEnv) (fr : Frame) (v : FlatVar) : Option Value :=
  match fr.get? (immName v.name) with
  | some l => some l.val
  | none =>
    match cfg.immutables.find? (·.1 == v.name) with
    | some (_, x) => some x
    | none => zeroValue env v.ty

/-- Builtin namespaces (`msg.*`, `block.*`, `tx.*`, `abi.*`): never receivers of user calls. -/
def isEnvObj (s : Ident) : Bool := s == "msg" || s == "block" || s == "tx" || s == "abi"

/-- Builtin functions, dispatched before user functions of the same name. -/
def isBuiltinFn (f : Ident) : Bool :=
  f == "require" || f == "assert" || f == "revert" || f == "keccak256" || f == "gasleft" ||
    f == "addmod" || f == "mulmod" || f == "type"

/-- `require(c, E(args))` with a declared custom error `E`. -/
def isCustomError (fc : FlatContract) : Expr → Bool
  | .call (.ident err) [] _ => (fc.error? err).isSome
  | _ => false

/-- Member accesses resolved without evaluating the receiver: `msg.x`, an enum member, `type(T).x`. -/
def directMember (fc : FlatContract) (fr : Frame) : Expr → Bool
  | .ident obj => isEnvObj obj || ((fr.get? obj).isNone && (fc.types.enum? none obj).isSome)
  | .call (.ident "type") [] (.positional [.typeExpr _]) => true
  | _ => false

/-- Member calls with builtin meaning (before `using for`). -/
def specialMemberCall : Value → Ident → Bool
  | .storageRef _ (.dynArray _), "push" => true
  | .storageRef _ (.dynArray _), "pop" => true
  | .contract _ _, _ => true
  | _, "call" | _, "staticcall" | _, "delegatecall" | _, "transfer" | _, "send" => true
  | _, _ => false

def isContractValue : Value → Bool
  | .contract _ _ => true
  | _ => false


def argFits (env : TypeEnv) (h : Heap) (v : Value) (p : Param) : Bool :=
  match v with
  | .storageRef _ ty => p.loc == some .storage && ty == p.ty
  | .memRef _ => !(isValueType env p.ty)
  | .raw ty _ => ty == p.ty
  | v => (implicitConv env h v p.ty).isSome

def fnFits (env : TypeEnv) (h : Heap) (d : FnDecl) (args : List Value) : Bool :=
  d.params.length == args.length && (d.params.zip args).all fun (p, v) => argFits env h v p

/-- Exactly one candidate must accept the arguments. -/
def resolveOverload (env : TypeEnv) (h : Heap) (fc : FlatContract) (cands : List (FnKey × FnId))
    (args : List Value) : Option FnDef :=
  let fits := cands.filterMap fun (_, id) =>
    (fc.fns[id]?).bind fun f => if fnFits env h f.decl args then some f else none
  match fits with
  | [f] => some f
  | _ => none

def resolveDecl (env : TypeEnv) (h : Heap) (decls : List FnDecl) (args : List Value) : Option FnDecl :=
  match decls.filter (fnFits env h · args) with
  | [d] => some d
  | _ => none

def retValue : List Value → Value
  | [] => .unit
  | [v] => v
  | vs => .tuple vs

/-- Values of the return slots. -/
def retVals (fr : Frame) : Option (List Value) :=
  fr.retVars.mapM fun r => (fr.get? r).map (·.val)

/-- Enter a function: fresh frame with parameters bound and return slots zeroed. -/
def enterFn (cfg : Config) (env : TypeEnv) (here : Ident) (d : FnDecl) (args : List Value) (m : Machine)
    (seed : Store := ∅) : Op (Frame × Machine) := do
  if d.params.length ≠ args.length then Op.stuck
  let fr0 : Frame := { here := here, locals := seed, retVars := d.returns.zipIdx.map fun (p, i) => retName i p }
  let (fr1, m1) ← (d.params.zip args).foldlM (fun (fr, m) (p, v) => do
      let some name := p.name | Op.stuck
      declare cfg env fr m p.ty (p.loc <|> some .memory) name (some v)) (fr0, m)
  d.returns.zipIdx.foldlM (fun (fr, m) (p, i) =>
      declare cfg env fr m p.ty (p.loc <|> some .memory) (retName i p) none) (fr1, m1)

/-- Enter a modifier body: a fresh scope for its parameters over the suspended function scope. -/
def pushScope (fr : Frame) (rest : List (ModDef × List Value)) (body : Block) : Frame :=
  { fr with locals := ∅, outer := fr.locals :: fr.outer, chain := rest, body := body }

/-- Back to the suspended scope (the function scope seen from a modifier body). -/
def popFrame (fr : Frame) : Frame :=
  match fr.outer with
  | s :: rest => { fr with locals := s, outer := rest }
  | [] => fr

/-- Leave a modifier body. -/
def popScope : ExecResult → ExecResult
  | .normal fr m => .normal (popFrame fr) m
  | .returned fr m => .returned (popFrame fr) m
  | r => r

/-- Resume the modifier scope `fr` after `_;` ran the rest of the chain in the function scope,
    which is now `fr'.locals`. -/
def resumeScope (fr fr' : Frame) : Frame :=
  { fr' with locals := fr.locals, outer := fr'.locals :: fr'.outer, chain := fr.chain, body := fr.body }

/-- Result of a `_;`: a `return` inside the body only leaves the body. -/
def settlePlaceholder (fr : Frame) : ExecResult → Option ExecResult
  | .normal fr' m => some (.normal (resumeScope fr fr') m)
  | .returned fr' m => some (.normal (resumeScope fr fr') m)
  | .reverted d => some (.reverted d)
  | _ => none

def restoreUnchecked (u : Bool) : ExecResult → ExecResult
  | .normal fr m => .normal { fr with unchecked := u } m
  | .returned fr m => .returned { fr with unchecked := u } m
  | .break fr m => .break { fr with unchecked := u } m
  | .continue fr m => .continue { fr with unchecked := u } m
  | .reverted d => .reverted d

/-- Bytes of a `bytes memory` / `string memory` / literal argument. -/
def bytesArg (h : Heap) : Value → Option ByteArray
  | .strLit s => some s
  | .memRef id => match h.get? id with | some (.bytes _ d) => some d | _ => none
  | _ => none

def allocBytes (m : Machine) (isString : Bool) (d : ByteArray) : Value × Machine :=
  let (h', id) := m.heap.alloc (.bytes isString d)
  (.memRef id, { m with heap := h' })

/-- Order named arguments by the parameter names. -/
def namedArgs (params : List Ident) (fs : List (Ident × Expr)) : Option (List Expr) :=
  if fs.length ≠ params.length then none else params.mapM fun p => (fs.find? (·.1 == p)).map (·.2)

def argExprs (params : List (Option Ident)) : Args → Option (List Expr)
  | .positional es => some es
  | .named fs => (params.mapM id).bind fun names => namedArgs names fs

def paramNames (ps : List Param) : List (Option Ident) := ps.map (·.name)

def codeSize (evm : EVM.State) (a : EVM.Address) : Nat :=
  match evm.lookupAccount a with
  | some acc => acc.code.size
  | none => 0

def valueOpt : List CallOpt → Option Expr
  | [] => none
  | .value e :: _ => some e
  | _ :: rest => valueOpt rest

def gasOpt : List CallOpt → Option Expr
  | [] => none
  | .gas e :: _ => some e
  | _ :: rest => gasOpt rest

def saltOpt : List CallOpt → Option Expr
  | [] => none
  | .salt e :: _ => some e
  | _ :: rest => saltOpt rest

/-- A `bytes32` salt as the 32-byte word `CREATE2` takes. -/
def saltBytes : Value → Option ByteArray
  | .fixedBytes n bs => if n.val = 31 then some ⟨bs.toArray⟩ else none
  | _ => none

/-- `new C(...)`: the contract name and its constructor parameter types. -/
def newContract? (fc : FlatContract) : Ty → Option (Ident × List Ty)
  | .user _ c => (fc.ctorTys? c).map fun tys => (c, tys)
  | _ => none

def natValue : Value → Option Nat
  | .uint _ n => some n
  | .literal i => if i ≥ 0 then some i.toNat else none
  | _ => none

/-- Signature string and ABI types of an external function. -/
def externalSig (env : TypeEnv) (d : FnDecl) : Option (String × List ABIType × List ABIType) := do
  let sig ← sigOf env d.name (d.params.map (·.ty))
  let rets ← d.returns.mapM fun p => abiTypeOf env p.ty
  pure (ABI.printSignature sig, sig.paramTypes, rets)

def decodeRets (cfg : Config) (env : TypeEnv) (m : Machine) (rets : List Param) (retTys : List ABIType)
    (out : ByteArray) : Option (List Value × Machine) := do
  let svs ← ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode retTys out
  if svs.length ≠ rets.length then none
  let (vs, h') ← (rets.zip svs).foldlM (fun (acc, h) (p, sv) => do
    let (v, h') ← ofAbi env fuelDefault p.ty sv h
    pure (acc ++ [v], h')) (([] : List Value), m.heap)
  pure (vs, { m with heap := h' })

def usingLibrary (fc : FlatContract) (here : Ident) (ty : Option Ty) : List ContractDecl :=
  fc.usingFor.filterMap fun (c, u) =>
    if c != here then none
    else match u.target, u.ty with
      | .library l, some t => if some t == ty then fc.library? l else none
      | .library l, none => fc.library? l
      | _, _ => none

def receiverTy (h : Heap) : Value → Option Ty
  | .memRef id => (h.get? id).bind fun | .array e _ => some (.dynArray e) | .bytes s _ => some (if s then .string else .bytes) | .struct t _ => some t
  | v => v.ty?

/-- Head identifier of a receiver expression (to keep `msg`/`block`/`tx` members apart). -/
def headIdent : Expr → Ident
  | .ident x => x
  | _ => ""

def isTupleExpr : Expr → Bool
  | .tuple _ => true
  | _ => false

def isSuperExpr : Expr → Bool
  | .super => true
  | _ => false

/-- A library name in receiver position (`L.f(...)`). -/
def libraryRecv (fc : FlatContract) (fr : Frame) : Expr → Bool
  | .ident l => (fr.get? l).isNone && !(isEnvObj l) && (fc.library? l).isSome
  | _ => false

/-- Member calls resolved without evaluating the receiver: `super.f`, `abi.f`/`msg.f`/..., `L.f`. -/
def memberCallDirect (fc : FlatContract) (fr : Frame) (recv : Expr) : Bool :=
  isSuperExpr recv || isEnvObj (headIdent recv) || libraryRecv fc fr recv

def isRaw : Value → Bool
  | .raw .. => true
  | _ => false

def indexOf (xs : List Ident) (x : Ident) : Option Nat :=
  (xs.zipIdx.find? (·.1 == x)).map (·.2)

def argExprsAny : Args → Option (List Expr)
  | .positional es => some es
  | .named _ => none

/-- `super.f` candidates from the contract containing the call. -/
def superCands (fc : FlatContract) (here f : Ident) : List (FnKey × FnId) :=
  fc.superTable.filterMap fun ((c, k), id) => if c == here && k.name == f then some (k, id) else none

/-- Allocate a struct literal (values in field order, converted to the field types). -/
def structObj (cfg : Config) (env : TypeEnv) (m : Machine) (sd : StructInfo) (vs : List Value) :
    Op (Value × Machine) := do
  if sd.fields.length ≠ vs.length then Op.stuck
  let (fields, m') ← (sd.fields.zip vs).foldlM (fun (acc, m) ((fty, fname), v) => do
    let (v', m') ← coerce cfg env m v fty (some .memory)
    pure (acc ++ [(fname, v')], m')) (([] : List (Ident × Value)), m)
  let (h', id) := m'.heap.alloc (.struct (.user sd.qual sd.name) fields)
  pure (.memRef id, { m' with heap := h' })

/-- Values whose ABI types were derived from the values themselves. -/
def abiArgsAbi (_cfg : Config) (_env : TypeEnv) (m : Machine) (_tys : List ABIType) (vs : List Value) :
    Op (List Solm.Value × Machine) := do
  let svs ← Op.ofOpt (vs.mapM (toAbi m.heap fuelDefault))
  pure (svs, m)

/-- The target types of `abi.decode(data, T)` / `abi.decode(data, (T, U))`. -/
def typeArgs : Expr → Option (List Ty)
  | .typeExpr t => some [t]
  | .tuple es => es.mapM fun | some (.typeExpr t) => some t | _ => none
  | _ => none

def ofAbiList (env : TypeEnv) (tys : List Ty) (svs : List Solm.Value) (h : Heap) : Option (List Value × Heap) := do
  if tys.length ≠ svs.length then none
  (tys.zip svs).foldlM (fun (acc, h) (ty, sv) => do
    let (v, h') ← ofAbi env fuelDefault ty sv h
    pure (acc ++ [v], h')) (([] : List Value), h)

def isIncDec : UnOp → Bool
  | .preInc | .preDec | .postInc | .postDec => true
  | _ => false

def incDecOp : UnOp → BinOp
  | .preInc | .postInc => .add
  | _ => .sub

def isPrefix : UnOp → Bool
  | .preInc | .preDec => true
  | _ => false

def assignOp : AssignOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor | .shl => .shl | .shr => .shr
  | .assign => .add

/-- Allocate an inline array literal; the element type is the first element's. -/
def arrayLitObj (env : TypeEnv) (m : Machine) (vs : List Value) : Op (Value × Machine) := do
  let some v0 := vs.head? | Op.stuck
  let ety ← match v0 with
    | .literal i => Op.ofOpt ((mobileType i).map IntTy.toTy)
    | v => Op.ofOpt (receiverTy m.heap v)
  let (elems, h') ← Op.ofOpt (vs.foldlM (fun (acc, h) v =>
    (implicitConv env h v ety).map fun (v', h') => (acc ++ [v'], h')) (([] : List Value), m.heap))
  let (h'', id) := h'.alloc (.array ety elems)
  pure (.memRef id, { m with heap := h'' })

def bindModParams (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) (params : List Param)
    (vs : List Value) : Op (Frame × Machine) := do
  if params.length ≠ vs.length then Op.stuck
  (params.zip vs).foldlM (fun (fr, m) (p, v) => do
    let some name := p.name | Op.stuck
    declare cfg env fr m p.ty (p.loc <|> some .memory) name (some v)) (fr, m)

/-- A function body has finished when it completes normally or via `return`. -/
def finished : ExecResult → Option (Frame × Machine)
  | .normal fr m => some (fr, m)
  | .returned fr m => some (fr, m)
  | _ => none

/-! ## The rules -/

variable (cfg : Config) (o : Oracle) (fc : FlatContract)


mutual

inductive EvalExpr : Frame → Machine → Expr → Res Value → Prop where
  | lit : literalValue l = some v → EvalExpr fr m (.lit l) (.ok v fr m)
  | thisRef : EvalExpr fr m .this (.ok (.contract fc.name m.this) fr m)
  | local : fr.get? x = some l → EvalExpr fr m (.ident x) (.ok l.val fr m)
  | constVar : fr.get? x = none → fc.var? x = some v → v.mutability = .constant → v.init = some e →
      EvalExpr fr m e r → EvalExpr fr m (.ident x) r
  | immutableVar : fr.get? x = none → fc.var? x = some v → v.mutability = .immutable →
      immutableValue cfg fc.types fr v = some val → EvalExpr fr m (.ident x) (.ok val fr m)
  | stateVar : fr.get? x = none → fc.var? x = some v → v.mutability = .mutable →
      loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty = some val → EvalExpr fr m (.ident x) (.ok val fr m)
  -- members
  | envMember : isEnvObj obj = true → envMember m obj f = some v →
      EvalExpr fr m (.member (.ident obj) f) (.ok v fr m)
  | msgData : allocBytes m false m.evm.executionEnv.calldata = (v, m') →
      EvalExpr fr m (.member (.ident "msg") "data") (.ok v fr m')
  | enumMember : isEnvObj t = false → fr.get? t = none → fc.types.enum? none t = some e → indexOf e.members f = some i →
      EvalExpr fr m (.member (.ident t) f) (.ok (.enum t i) fr m)
  | typeMember : typeMember fc ty f = some v →
      EvalExpr fr m (.member (.call (.ident "type") [] (.positional [.typeExpr ty])) f) (.ok v fr m)
  | memberField : directMember fc fr e = false → f ≠ "length" →
      EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) → storageField fc.types er ty f = some (er', fty) →
      loadIfScalar cfg fc.types m1.evm er' fty = some v → EvalExpr fr m (.member e f) (.ok v fr1 m1)
  | memberStorageLength : directMember fc fr e = false → EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) →
      storageLength cfg m1.evm er ty = some (.ok n) → EvalExpr fr m (.member e "length") (.ok (wordNat n) fr1 m1)
  | memberStorageLengthPanic : directMember fc fr e = false → EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) →
      storageLength cfg m1.evm er ty = some (.error p) → EvalExpr fr m (.member e "length") (.reverted p.data)
  | memberMemField : directMember fc fr e = false → f ≠ "length" →
      EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → memField m1.heap obj f = some v →
      EvalExpr fr m (.member e f) (.ok v fr1 m1)
  | memberMemLength : directMember fc fr e = false → EvalExpr fr m e (.ok (.memRef obj) fr1 m1) →
      memLength m1.heap obj = some n → EvalExpr fr m (.member e "length") (.ok (wordNat n) fr1 m1)
  | memberBalance : directMember fc fr e = false → EvalExpr fr m e (.ok v fr1 m1) → addrNat v = some a →
      EvalExpr fr m (.member e "balance") (.ok (wordNat (balanceOf m1.evm (EVM.address a))) fr1 m1)
  | memberBytesLength : directMember fc fr e = false → EvalExpr fr m e (.ok (.fixedBytes n bs) fr1 m1) →
      EvalExpr fr m (.member e "length") (.ok (wordNat (n.val + 1)) fr1 m1)
  | memberRevert : directMember fc fr e = false → EvalExpr fr m e (.reverted d) → EvalExpr fr m (.member e f) (.reverted d)
  -- indexing
  | indexStorage : EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      storageIndex cfg fc.types m2.evm m2.heap er ty iv = some (.ok (er', ty')) →
      loadIfScalar cfg fc.types m2.evm er' ty' = some v → EvalExpr fr m (.index e i) (.ok v fr2 m2)
  | indexStoragePanic : EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      storageIndex cfg fc.types m2.evm m2.heap er ty iv = some (.error p) → EvalExpr fr m (.index e i) (.reverted p.data)
  | indexMem : EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      memIndex m2.heap obj iv = some (.ok v) → isRaw v = false → EvalExpr fr m (.index e i) (.ok v fr2 m2)
  | indexMemRaw : EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      memIndex m2.heap obj iv = some (.ok (.raw ty w)) → validateRaw ty w = .ok v →
      EvalExpr fr m (.index e i) (.ok v fr2 m2)
  | indexMemRawRevert : EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      memIndex m2.heap obj iv = some (.ok (.raw ty w)) → validateRaw ty w = .error d →
      EvalExpr fr m (.index e i) (.reverted d)
  | indexMemPanic : EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      memIndex m2.heap obj iv = some (.error p) → EvalExpr fr m (.index e i) (.reverted p.data)
  | indexBaseRevert : EvalExpr fr m e (.reverted d) → EvalExpr fr m (.index e i) (.reverted d)
  | indexRevert : EvalExpr fr m e (.ok v fr1 m1) → EvalExpr fr1 m1 i (.reverted d) → EvalExpr fr m (.index e i) (.reverted d)
  -- conversions and struct literals
  | convert : EvalExpr fr m a (.ok v fr1 m1) → explicitConv fc.types m1.heap v ty = some (.ok (v', h')) →
      EvalExpr fr m (.call (.typeExpr ty) [] (.positional [a])) (.ok v' fr1 { m1 with heap := h' })
  | convertPanic : EvalExpr fr m a (.ok v fr1 m1) → explicitConv fc.types m1.heap v ty = some (.error p) →
      EvalExpr fr m (.call (.typeExpr ty) [] (.positional [a])) (.reverted p.data)
  | convertRevert : EvalExpr fr m a (.reverted d) → EvalExpr fr m (.call (.typeExpr ty) [] (.positional [a])) (.reverted d)
  | convertUser : isBuiltinFn c = false → fr.get? c = none → fc.var? c = none → fc.fnsNamed c = [] → fc.types.struct? none c = none →
      (fc.types.contractKind? c).isSome ∨ (fc.types.enum? none c).isSome →
      EvalExpr fr m (.call (.typeExpr (.user none c)) [] (.positional [a])) r →
      EvalExpr fr m (.call (.ident c) [] (.positional [a])) r
  | structLit : isBuiltinFn s = false → fr.get? s = none → fc.fnsNamed s = [] → fc.types.struct? none s = some sd →
      argExprs (sd.fields.map fun f => some f.2) args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → structObj cfg fc.types m1 sd vs = some (.ok (v, m2)) →
      EvalExpr fr m (.call (.ident s) [] args) (.ok v fr1 m2)
  | structLitRevert : isBuiltinFn s = false → fr.get? s = none → fc.fnsNamed s = [] → fc.types.struct? none s = some sd →
      argExprs (sd.fields.map fun f => some f.2) args = some es →
      EvalExprs fr m es (.reverted d) → EvalExpr fr m (.call (.ident s) [] args) (.reverted d)
  | structLitPanic : isBuiltinFn s = false → fr.get? s = none → fc.fnsNamed s = [] → fc.types.struct? none s = some sd →
      argExprs (sd.fields.map fun f => some f.2) args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → structObj cfg fc.types m1 sd vs = some (.error p) →
      EvalExpr fr m (.call (.ident s) [] args) (.reverted p.data)
  -- builtins
  | requireTrue : EvalExpr fr m c (.ok (.bool true) fr1 m1) →
      EvalExpr fr m (.call (.ident "require") [] (.positional (c :: rest))) (.ok .unit fr1 m1)
  | requireFalse : EvalExpr fr m c (.ok (.bool false) fr1 m1) →
      EvalExpr fr m (.call (.ident "require") [] (.positional [c])) (.reverted ByteArray.empty)
  | requireMsg : isCustomError fc msg = false → EvalExpr fr m c (.ok (.bool false) fr1 m1) → EvalExpr fr1 m1 msg (.ok mv fr2 m2) →
      bytesArg m2.heap mv = some s →
      EvalExpr fr m (.call (.ident "require") [] (.positional [c, msg])) (.reverted (errorStringData s))
  | requireMsgRevert : isCustomError fc msg = false → EvalExpr fr m c (.ok (.bool false) fr1 m1) → EvalExpr fr1 m1 msg (.reverted d) →
      EvalExpr fr m (.call (.ident "require") [] (.positional [c, msg])) (.reverted d)
  | requireCustom : EvalExpr fr m c (.ok (.bool false) fr1 m1) → fc.error? err = some ei →
      argExprs (paramNames ei.decl.params) args = some es → EvalExprs fr1 m1 es (.ok vs fr2 m2) →
      abiArgs cfg fc.types m2 (ei.decl.params.map (·.ty)) vs = some (.ok (svs, m3)) →
      customErrorData ei.sigStr ei.sig.paramTypes svs = some d →
      EvalExpr fr m (.call (.ident "require") [] (.positional [c, .call (.ident err) [] args])) (.reverted d)
  | requireCustomArgsRevert : EvalExpr fr m c (.ok (.bool false) fr1 m1) → fc.error? err = some ei →
      argExprs (paramNames ei.decl.params) args = some es → EvalExprs fr1 m1 es (.reverted d) →
      EvalExpr fr m (.call (.ident "require") [] (.positional [c, .call (.ident err) [] args])) (.reverted d)
  | requireCustomPanic : EvalExpr fr m c (.ok (.bool false) fr1 m1) → fc.error? err = some ei →
      argExprs (paramNames ei.decl.params) args = some es → EvalExprs fr1 m1 es (.ok vs fr2 m2) →
      abiArgs cfg fc.types m2 (ei.decl.params.map (·.ty)) vs = some (.error p) →
      EvalExpr fr m (.call (.ident "require") [] (.positional [c, .call (.ident err) [] args])) (.reverted p.data)
  | requireCondRevert : EvalExpr fr m c (.reverted d) →
      EvalExpr fr m (.call (.ident "require") [] (.positional (c :: rest))) (.reverted d)
  | assertTrue : EvalExpr fr m c (.ok (.bool true) fr1 m1) →
      EvalExpr fr m (.call (.ident "assert") [] (.positional [c])) (.ok .unit fr1 m1)
  | assertFalse : EvalExpr fr m c (.ok (.bool false) fr1 m1) →
      EvalExpr fr m (.call (.ident "assert") [] (.positional [c])) (.reverted (panicData 0x01))
  | assertRevert : EvalExpr fr m c (.reverted d) →
      EvalExpr fr m (.call (.ident "assert") [] (.positional [c])) (.reverted d)
  | revertEmpty : EvalExpr fr m (.call (.ident "revert") [] (.positional [])) (.reverted ByteArray.empty)
  | revertMsg : EvalExpr fr m msg (.ok mv fr1 m1) → bytesArg m1.heap mv = some s →
      EvalExpr fr m (.call (.ident "revert") [] (.positional [msg])) (.reverted (errorStringData s))
  | revertMsgRevert : EvalExpr fr m msg (.reverted d) →
      EvalExpr fr m (.call (.ident "revert") [] (.positional [msg])) (.reverted d)
  | keccak : EvalExpr fr m b (.ok v fr1 m1) → bytesArg m1.heap v = some s →
      EvalExpr fr m (.call (.ident "keccak256") [] (.positional [b])) (.ok (.fixedBytes ⟨31, by decide⟩ (ffi.KEC s).toList) fr1 m1)
  | keccakRevert : EvalExpr fr m b (.reverted d) →
      EvalExpr fr m (.call (.ident "keccak256") [] (.positional [b])) (.reverted d)
  | gasleft : EvalExpr fr m (.call (.ident "gasleft") [] (.positional []))
      (.ok (.uint ⟨256, by decide⟩ (o.gasleft m.tick).toNat) fr { m with tick := m.tick + 1 })
  | addmod : EvalExprs fr m [x, y, k] (.ok [xv, yv, kv] fr1 m1) → natValue xv = some a → natValue yv = some b →
      natValue kv = some c → c ≠ 0 →
      EvalExpr fr m (.call (.ident "addmod") [] (.positional [x, y, k])) (.ok (wordNat ((a + b) % c)) fr1 m1)
  | mulmod : EvalExprs fr m [x, y, k] (.ok [xv, yv, kv] fr1 m1) → natValue xv = some a → natValue yv = some b →
      natValue kv = some c → c ≠ 0 →
      EvalExpr fr m (.call (.ident "mulmod") [] (.positional [x, y, k])) (.ok (wordNat ((a * b) % c)) fr1 m1)
  | modZero : EvalExprs fr m [x, y, k] (.ok [xv, yv, kv] fr1 m1) → natValue xv = some a → natValue yv = some b →
      natValue kv = some 0 → (f = "addmod" ∨ f = "mulmod") →
      EvalExpr fr m (.call (.ident f) [] (.positional [x, y, k])) (.reverted (panicData 0x12))
  | modArgsRevert : (f = "addmod" ∨ f = "mulmod") → EvalExprs fr m [x, y, k] (.reverted d) →
      EvalExpr fr m (.call (.ident f) [] (.positional [x, y, k])) (.reverted d)
  -- abi.*
  | abiEncode : EvalExprs fr m es (.ok vs fr1 m1) → vs.mapM (abiTyOfValue fc.types m1.heap) = some tys →
      abiArgsAbi cfg fc.types m1 tys vs = some (.ok (svs, m2)) → encodeABIValues? tys svs = some bs →
      allocBytes m2 false bs.toByteArray = (v, m3) →
      EvalExpr fr m (.call (.member (.ident "abi") "encode") [] (.positional es)) (.ok v fr1 m3)
  | abiEncodePacked : EvalExprs fr m es (.ok vs fr1 m1) → vs.mapM (abiTyOfValue fc.types m1.heap) = some tys →
      abiArgsAbi cfg fc.types m1 tys vs = some (.ok (svs, m2)) →
      (tys.zip svs).mapM (fun (t, sv) => Solm.encodePackedValue? t sv) = some parts →
      allocBytes m2 false parts.flatten.toByteArray = (v, m3) →
      EvalExpr fr m (.call (.member (.ident "abi") "encodePacked") [] (.positional es)) (.ok v fr1 m3)
  | abiEncodeWithSelector : EvalExprs fr m (sel :: es) (.ok (.fixedBytes n sb :: vs) fr1 m1) → n.val = 3 →
      vs.mapM (abiTyOfValue fc.types m1.heap) = some tys → abiArgsAbi cfg fc.types m1 tys vs = some (.ok (svs, m2)) →
      encodeABIValues? tys svs = some bs → allocBytes m2 false ((ByteArray.mk sb.toArray) ++ bs.toByteArray) = (v, m3) →
      EvalExpr fr m (.call (.member (.ident "abi") "encodeWithSelector") [] (.positional (sel :: es))) (.ok v fr1 m3)
  | abiEncodeWithSignature : EvalExprs fr m (sig :: es) (.ok (sv :: vs) fr1 m1) → bytesArg m1.heap sv = some s →
      vs.mapM (abiTyOfValue fc.types m1.heap) = some tys → abiArgsAbi cfg fc.types m1 tys vs = some (.ok (svs, m2)) →
      encodeABIValues? tys svs = some bs → allocBytes m2 false ((ffi.KEC s).extract 0 4 ++ bs.toByteArray) = (v, m3) →
      EvalExpr fr m (.call (.member (.ident "abi") "encodeWithSignature") [] (.positional (sig :: es))) (.ok v fr1 m3)
  | abiDecode : EvalExpr fr m d (.ok dv fr1 m1) → bytesArg m1.heap dv = some s →
      typeArgs tyArg = some tys → tys.mapM (abiTypeOf fc.types) = some atys →
      ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode atys s = some svs →
      ofAbiList fc.types tys svs m1.heap = some (vs, h') →
      EvalExpr fr m (.call (.member (.ident "abi") "decode") [] (.positional [d, tyArg])) (.ok (retValue vs) fr1 { m1 with heap := h' })
  | abiDecodeFail : EvalExpr fr m d (.ok dv fr1 m1) → bytesArg m1.heap dv = some s →
      typeArgs tyArg = some tys → tys.mapM (abiTypeOf fc.types) = some atys →
      ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode atys s = none →
      EvalExpr fr m (.call (.member (.ident "abi") "decode") [] (.positional [d, tyArg])) (.reverted ByteArray.empty)
  | abiEncodeRevert : (f = "encode" ∨ f = "encodePacked" ∨ f = "encodeWithSelector" ∨ f = "encodeWithSignature") →
      EvalExprs fr m es (.reverted d) → EvalExpr fr m (.call (.member (.ident "abi") f) [] (.positional es)) (.reverted d)
  | abiDecodeRevert : EvalExpr fr m d (.reverted dd) →
      EvalExpr fr m (.call (.member (.ident "abi") "decode") [] (.positional [d, tyArg])) (.reverted dd)
  -- memory allocation
  | newArray : newContract? fc ty = none → EvalExpr fr m n (.ok nv fr1 m1) → natValue nv = some len →
      isValueType fc.types ty = false → zeroObj fc.types fuelDefault ty len m1.heap = some (v, h') →
      EvalExpr fr m (.call (.new ty) [] (.positional [n])) (.ok v fr1 { m1 with heap := h' })
  | newArrayRevert : newContract? fc ty = none → EvalExpr fr m n (.reverted d) →
      EvalExpr fr m (.call (.new ty) [] (.positional [n])) (.reverted d)
  -- contract creation `new C{value: v, salt: s}(args)`: `value` is evaluated before `salt`, then the arguments
  | newContract : newContract? fc ty = some (c, tys) → EvalValueOpt fr m (valueOpt opts) (.ok value fr1 m1) →
      EvalSaltOpt fr1 m1 (saltOpt opts) (.ok salt fr2 m2) → argExprsAny args = some es →
      EvalExprs fr2 m2 es (.ok vs fr3 m3) → abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)) →
      newViaEVM cfg o m4 c value svs salt (a, m5, true, out) →
      EvalExpr fr m (.call (.new ty) opts args) (.ok (.contract c a) fr3 m5)
  | newContractFailed : newContract? fc ty = some (c, tys) → EvalValueOpt fr m (valueOpt opts) (.ok value fr1 m1) →
      EvalSaltOpt fr1 m1 (saltOpt opts) (.ok salt fr2 m2) → argExprsAny args = some es →
      EvalExprs fr2 m2 es (.ok vs fr3 m3) → abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)) →
      newViaEVM cfg o m4 c value svs salt (a, m5, false, out) →
      EvalExpr fr m (.call (.new ty) opts args) (.reverted out)
  | newContractAbiPanic : newContract? fc ty = some (c, tys) → EvalValueOpt fr m (valueOpt opts) (.ok value fr1 m1) →
      EvalSaltOpt fr1 m1 (saltOpt opts) (.ok salt fr2 m2) → argExprsAny args = some es →
      EvalExprs fr2 m2 es (.ok vs fr3 m3) → abiArgs cfg fc.types m3 tys vs = some (.error p) →
      EvalExpr fr m (.call (.new ty) opts args) (.reverted p.data)
  | newContractArgsRevert : newContract? fc ty = some (c, tys) → EvalValueOpt fr m (valueOpt opts) (.ok value fr1 m1) →
      EvalSaltOpt fr1 m1 (saltOpt opts) (.ok salt fr2 m2) → argExprsAny args = some es →
      EvalExprs fr2 m2 es (.reverted d) → EvalExpr fr m (.call (.new ty) opts args) (.reverted d)
  | newContractSaltRevert : newContract? fc ty = some (c, tys) → EvalValueOpt fr m (valueOpt opts) (.ok value fr1 m1) →
      EvalSaltOpt fr1 m1 (saltOpt opts) (.reverted d) → EvalExpr fr m (.call (.new ty) opts args) (.reverted d)
  | newContractValueRevert : newContract? fc ty = some (c, tys) → EvalValueOpt fr m (valueOpt opts) (.reverted d) →
      EvalExpr fr m (.call (.new ty) opts args) (.reverted d)
  -- internal calls
  | internalCall : isBuiltinFn f = false → fr.get? f = none → fc.fnsNamed f ≠ [] → argExprsAny args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → resolveOverload fc.types m1.heap fc (fc.fnsNamed f) vs = some fn →
      CallFn fr1 m1 fn vs (.ok rets m2) →
      EvalExpr fr m (.call (.ident f) [] args) (.ok (retValue rets) fr1 m2)
  | internalCallRevert : isBuiltinFn f = false → fr.get? f = none → fc.fnsNamed f ≠ [] → argExprsAny args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → resolveOverload fc.types m1.heap fc (fc.fnsNamed f) vs = some fn →
      CallFn fr1 m1 fn vs (.reverted d) → EvalExpr fr m (.call (.ident f) [] args) (.reverted d)
  | internalArgsRevert : isBuiltinFn f = false → fr.get? f = none → fc.fnsNamed f ≠ [] → argExprsAny args = some es →
      EvalExprs fr m es (.reverted d) → EvalExpr fr m (.call (.ident f) [] args) (.reverted d)
  | superCall : argExprsAny args = some es → EvalExprs fr m es (.ok vs fr1 m1) →
      resolveOverload fc.types m1.heap fc (superCands fc fr.here f) vs = some fn → CallFn fr1 m1 fn vs (.ok rets m2) →
      EvalExpr fr m (.call (.member .super f) [] args) (.ok (retValue rets) fr1 m2)
  | superCallRevert : argExprsAny args = some es → EvalExprs fr m es (.ok vs fr1 m1) →
      resolveOverload fc.types m1.heap fc (superCands fc fr.here f) vs = some fn → CallFn fr1 m1 fn vs (.reverted d) →
      EvalExpr fr m (.call (.member .super f) [] args) (.reverted d)
  | superArgsRevert : argExprsAny args = some es → EvalExprs fr m es (.reverted d) →
      EvalExpr fr m (.call (.member .super f) [] args) (.reverted d)
  | libraryCall : isEnvObj l = false → fr.get? l = none → fc.library? l = some lib → argExprsAny args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → resolveDecl fc.types m1.heap (lib.functions.filter (·.name == f)) vs = some d →
      CallFn fr1 m1 ⟨0, l, d⟩ vs (.ok rets m2) →
      EvalExpr fr m (.call (.member (.ident l) f) [] args) (.ok (retValue rets) fr1 m2)
  | libraryCallRevert : isEnvObj l = false → fr.get? l = none → fc.library? l = some lib → argExprsAny args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → resolveDecl fc.types m1.heap (lib.functions.filter (·.name == f)) vs = some d →
      CallFn fr1 m1 ⟨0, l, d⟩ vs (.reverted dd) →
      EvalExpr fr m (.call (.member (.ident l) f) [] args) (.reverted dd)
  | libraryArgsRevert : isEnvObj l = false → fr.get? l = none → fc.library? l = some lib → argExprsAny args = some es →
      EvalExprs fr m es (.reverted d) → EvalExpr fr m (.call (.member (.ident l) f) [] args) (.reverted d)
  | usingForCall : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → specialMemberCall rv f = false →
      usingLibrary fc fr.here (receiverTy m1.heap rv) = [lib] → argExprsAny args = some es →
      EvalExprs fr1 m1 es (.ok vs fr2 m2) →
      resolveDecl fc.types m2.heap (lib.functions.filter (·.name == f)) (rv :: vs) = some d →
      CallFn fr2 m2 ⟨0, lib.name, d⟩ (rv :: vs) (.ok rets m3) →
      EvalExpr fr m (.call (.member recv f) [] args) (.ok (retValue rets) fr2 m3)
  | usingForArgsRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → specialMemberCall rv f = false →
      usingLibrary fc fr.here (receiverTy m1.heap rv) = [lib] → argExprsAny args = some es →
      EvalExprs fr1 m1 es (.reverted d) → EvalExpr fr m (.call (.member recv f) [] args) (.reverted d)
  | usingForCallRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → specialMemberCall rv f = false →
      usingLibrary fc fr.here (receiverTy m1.heap rv) = [lib] → argExprsAny args = some es →
      EvalExprs fr1 m1 es (.ok vs fr2 m2) →
      resolveDecl fc.types m2.heap (lib.functions.filter (·.name == f)) (rv :: vs) = some d →
      CallFn fr2 m2 ⟨0, lib.name, d⟩ (rv :: vs) (.reverted dd) →
      EvalExpr fr m (.call (.member recv f) [] args) (.reverted dd)
  -- storage array push / pop
  | push1 : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1) → EvalExpr fr1 m1 x (.ok v fr2 m2) →
      storagePush cfg fc.types m2 er e (some v) = some (.ok m3) →
      EvalExpr fr m (.call (.member recv "push") [] (.positional [x])) (.ok .unit fr2 m3)
  | push1Revert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1) → EvalExpr fr1 m1 x (.reverted d) →
      EvalExpr fr m (.call (.member recv "push") [] (.positional [x])) (.reverted d)
  | push1Panic : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1) → EvalExpr fr1 m1 x (.ok v fr2 m2) →
      storagePush cfg fc.types m2 er e (some v) = some (.error p) →
      EvalExpr fr m (.call (.member recv "push") [] (.positional [x])) (.reverted p.data)
  | push0 : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1) →
      storagePush cfg fc.types m1 er e none = some (.ok m2) →
      EvalExpr fr m (.call (.member recv "push") [] (.positional [])) (.ok .unit fr1 m2)
  | push0Panic : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1) →
      storagePush cfg fc.types m1 er e none = some (.error p) →
      EvalExpr fr m (.call (.member recv "push") [] (.positional [])) (.reverted p.data)
  | pop : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1) → storagePop cfg fc.types m1 er e = some (.ok m2) →
      EvalExpr fr m (.call (.member recv "pop") [] (.positional [])) (.ok .unit fr1 m2)
  | popPanic : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1) → storagePop cfg fc.types m1 er e = some (.error p) →
      EvalExpr fr m (.call (.member recv "pop") [] (.positional [])) (.reverted p.data)
  -- external calls through contract types (options evaluated `value` then `gas`, then the arguments)
  | externalCall : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      argExprsAny args = some es → EvalExprs fr3 m3 es (.ok vs fr4 m4) →
      resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d →
      externalSig fc.types d = some (sigStr, ptys, rtys) → abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs = some (.ok (svs, m5)) →
      encodeABIValues? ptys svs = some bs →
      (d.returns = [] → codeSize m4.evm a ≠ 0) →
      callViaEVM o m5 a value (selectorOf sigStr ++ bs.toByteArray) (m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure) (calleeGas o m5 gasReq value) (true, m6, out) →
      decodeRets cfg fc.types m6 d.returns rtys out = some (rets, m7) →
      EvalExpr fr m (.call (.member recv f) opts args) (.ok (retValue rets) fr4 m7)
  | externalCallNoCode : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      argExprsAny args = some es → EvalExprs fr3 m3 es (.ok vs fr4 m4) →
      resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d →
      d.returns = [] → codeSize m4.evm a = 0 →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted ByteArray.empty)
  | externalCallFailed : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      argExprsAny args = some es → EvalExprs fr3 m3 es (.ok vs fr4 m4) →
      resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d →
      externalSig fc.types d = some (sigStr, ptys, rtys) → abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs = some (.ok (svs, m5)) →
      encodeABIValues? ptys svs = some bs →
      (d.returns = [] → codeSize m4.evm a ≠ 0) →
      callViaEVM o m5 a value (selectorOf sigStr ++ bs.toByteArray) (m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure) (calleeGas o m5 gasReq value) (false, m6, out) →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted out)
  | externalCallDecodeFail : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      argExprsAny args = some es → EvalExprs fr3 m3 es (.ok vs fr4 m4) →
      resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d →
      externalSig fc.types d = some (sigStr, ptys, rtys) → abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs = some (.ok (svs, m5)) →
      encodeABIValues? ptys svs = some bs →
      (d.returns = [] → codeSize m4.evm a ≠ 0) →
      callViaEVM o m5 a value (selectorOf sigStr ++ bs.toByteArray) (m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure) (calleeGas o m5 gasReq value) (true, m6, out) →
      decodeRets cfg fc.types m6 d.returns rtys out = none →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted ByteArray.empty)
  | externalValueRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.reverted d) →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted d)
  | externalGasRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.reverted d) →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted d)
  | externalArgsRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      argExprsAny args = some es → EvalExprs fr3 m3 es (.reverted d) →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted d)
  | externalAbiPanic : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok (.contract c a) fr1 m1) →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      argExprsAny args = some es → EvalExprs fr3 m3 es (.ok vs fr4 m4) →
      resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d →
      externalSig fc.types d = some (sigStr, ptys, rtys) → abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs = some (.error p) →
      (d.returns = [] → codeSize m4.evm a ≠ 0) →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted p.data)
  -- low-level calls on addresses
  | lowLevelCall : (f = "call" ∨ f = "staticcall") → memberCallDirect fc fr recv = false →
      EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      EvalExpr fr3 m3 dataE (.ok dv fr4 m4) → bytesArg m4.heap dv = some data →
      callViaEVM o m4 (EVM.address a) value data (f == "call" && m4.evm.executionEnv.perm) (calleeGas o m4 gasReq value) (z, m5, out) →
      allocBytes m5 false out = (ov, m6) →
      EvalExpr fr m (.call (.member recv f) opts (.positional [dataE])) (.ok (.tuple [.bool z, ov]) fr4 m6)
  | lowLevelValueRevert : (f = "call" ∨ f = "staticcall") → memberCallDirect fc fr recv = false →
      EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalValueOpt fr1 m1 (valueOpt opts) (.reverted d) →
      EvalExpr fr m (.call (.member recv f) opts (.positional [dataE])) (.reverted d)
  | lowLevelGasRevert : (f = "call" ∨ f = "staticcall") → memberCallDirect fc fr recv = false →
      EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.reverted d) →
      EvalExpr fr m (.call (.member recv f) opts (.positional [dataE])) (.reverted d)
  | lowLevelDataRevert : (f = "call" ∨ f = "staticcall") → memberCallDirect fc fr recv = false →
      EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalValueOpt fr1 m1 (valueOpt opts) (.ok value fr2 m2) → EvalGasOpt fr2 m2 (gasOpt opts) (.ok gasReq fr3 m3) →
      EvalExpr fr3 m3 dataE (.reverted d) →
      EvalExpr fr m (.call (.member recv f) opts (.positional [dataE])) (.reverted d)
  | delegateCall : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalGasOpt fr1 m1 (gasOpt opts) (.ok gasReq fr2 m2) → EvalExpr fr2 m2 dataE (.ok dv fr3 m3) → bytesArg m3.heap dv = some data →
      delegateCallViaEVM o m3 (EVM.address a) data (calleeGas o m3 gasReq 0) (z, m4, out) → allocBytes m4 false out = (ov, m5) →
      EvalExpr fr m (.call (.member recv "delegatecall") opts (.positional [dataE])) (.ok (.tuple [.bool z, ov]) fr3 m5)
  | delegateCallGasRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalGasOpt fr1 m1 (gasOpt opts) (.reverted d) →
      EvalExpr fr m (.call (.member recv "delegatecall") opts (.positional [dataE])) (.reverted d)
  | delegateCallDataRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalGasOpt fr1 m1 (gasOpt opts) (.ok gasReq fr2 m2) → EvalExpr fr2 m2 dataE (.reverted d) →
      EvalExpr fr m (.call (.member recv "delegatecall") opts (.positional [dataE])) (.reverted d)
  | transfer : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalExpr fr1 m1 amt (.ok av fr2 m2) → natValue av = some value →
      callViaEVM o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) (true, m3, out) →
      EvalExpr fr m (.call (.member recv "transfer") [] (.positional [amt])) (.ok .unit fr2 m3)
  | transferFailed : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalExpr fr1 m1 amt (.ok av fr2 m2) → natValue av = some value →
      callViaEVM o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) (false, m3, out) →
      EvalExpr fr m (.call (.member recv "transfer") [] (.positional [amt])) (.reverted out)
  | send : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a →
      EvalExpr fr1 m1 amt (.ok av fr2 m2) → natValue av = some value →
      callViaEVM o m2 (EVM.address a) value ByteArray.empty m2.evm.executionEnv.perm (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) (z, m3, out) →
      EvalExpr fr m (.call (.member recv "send") [] (.positional [amt])) (.ok (.bool z) fr2 m3)
  | transferAmtRevert : (f = "transfer" ∨ f = "send") → memberCallDirect fc fr recv = false →
      EvalExpr fr m recv (.ok rv fr1 m1) → isContractValue rv = false → addrNat rv = some a → EvalExpr fr1 m1 amt (.reverted d) →
      EvalExpr fr m (.call (.member recv f) [] (.positional [amt])) (.reverted d)
  | callRecvRevert : memberCallDirect fc fr recv = false → EvalExpr fr m recv (.reverted d) →
      EvalExpr fr m (.call (.member recv f) opts args) (.reverted d)
  -- operators
  | unary : EvalExpr fr m e (.ok v fr1 m1) → unop (!fr1.unchecked) op v = some (.ok r) → isIncDec op = false →
      op ≠ .delete → EvalExpr fr m (.unary op e) (.ok r fr1 m1)
  | unaryPanic : EvalExpr fr m e (.ok v fr1 m1) → unop (!fr1.unchecked) op v = some (.error p) → isIncDec op = false →
      op ≠ .delete → EvalExpr fr m (.unary op e) (.reverted p.data)
  | unaryRevert : EvalExpr fr m e (.reverted d) → isIncDec op = false → op ≠ .delete → EvalExpr fr m (.unary op e) (.reverted d)
  | incDec : isIncDec op = true → EvalLValue fr m e (.ok lv fr1 m1) → readLValue cfg fc.types fr1 m1 lv = some (.ok cur) →
      binop (!fr1.unchecked) (incDecOp op) cur (.literal 1) = some (.ok nv) →
      assign cfg fc.types fr1 m1 lv nv = some (.ok (fr2, m2)) →
      EvalExpr fr m (.unary op e) (.ok (if isPrefix op then nv else cur) fr2 m2)
  | incDecPanic : isIncDec op = true → EvalLValue fr m e (.ok lv fr1 m1) → readLValue cfg fc.types fr1 m1 lv = some (.ok cur) →
      binop (!fr1.unchecked) (incDecOp op) cur (.literal 1) = some (.error p) →
      EvalExpr fr m (.unary op e) (.reverted p.data)
  | incDecReadPanic : isIncDec op = true → EvalLValue fr m e (.ok lv fr1 m1) → readLValue cfg fc.types fr1 m1 lv = some (.error p) →
      EvalExpr fr m (.unary op e) (.reverted p.data)
  | incDecAssignPanic : isIncDec op = true → EvalLValue fr m e (.ok lv fr1 m1) → readLValue cfg fc.types fr1 m1 lv = some (.ok cur) →
      binop (!fr1.unchecked) (incDecOp op) cur (.literal 1) = some (.ok nv) →
      assign cfg fc.types fr1 m1 lv nv = some (.error p) →
      EvalExpr fr m (.unary op e) (.reverted p.data)
  | incDecRevert : isIncDec op = true → EvalLValue fr m e (.reverted d) → EvalExpr fr m (.unary op e) (.reverted d)
  | deleteLocal : EvalLValue fr m e (.ok (.local x) fr1 m1) → fr1.get? x = some l →
      zeroObj fc.types fuelDefault l.ty 0 m1.heap = some (z, h') →
      EvalExpr fr m (.unary .delete e) (.ok .unit (fr1.setVal x z) { m1 with heap := h' })
  | deleteStorage : EvalLValue fr m e (.ok (.storage er ty) fr1 m1) →
      clearStorage cfg fc.types fuelDefault m1.evm er ty = some (.ok evm') →
      EvalExpr fr m (.unary .delete e) (.ok .unit fr1 { m1 with evm := evm' })
  | deleteStoragePanic : EvalLValue fr m e (.ok (.storage er ty) fr1 m1) →
      clearStorage cfg fc.types fuelDefault m1.evm er ty = some (.error p) →
      EvalExpr fr m (.unary .delete e) (.reverted p.data)
  | deleteRevert : EvalLValue fr m e (.reverted d) → EvalExpr fr m (.unary .delete e) (.reverted d)
  | andShort : EvalExpr fr m a (.ok (.bool false) fr1 m1) → EvalExpr fr m (.binary .and a b) (.ok (.bool false) fr1 m1)
  | andFull : EvalExpr fr m a (.ok (.bool true) fr1 m1) → EvalExpr fr1 m1 b (.ok (.bool y) fr2 m2) →
      EvalExpr fr m (.binary .and a b) (.ok (.bool y) fr2 m2)
  | orShort : EvalExpr fr m a (.ok (.bool true) fr1 m1) → EvalExpr fr m (.binary .or a b) (.ok (.bool true) fr1 m1)
  | orFull : EvalExpr fr m a (.ok (.bool false) fr1 m1) → EvalExpr fr1 m1 b (.ok (.bool y) fr2 m2) →
      EvalExpr fr m (.binary .or a b) (.ok (.bool y) fr2 m2)
  | binary : op ≠ .and → op ≠ .or → EvalExpr fr m a (.ok va fr1 m1) → EvalExpr fr1 m1 b (.ok vb fr2 m2) →
      binop (!fr2.unchecked) op va vb = some (.ok v) → EvalExpr fr m (.binary op a b) (.ok v fr2 m2)
  | binaryPanic : op ≠ .and → op ≠ .or → EvalExpr fr m a (.ok va fr1 m1) → EvalExpr fr1 m1 b (.ok vb fr2 m2) →
      binop (!fr2.unchecked) op va vb = some (.error p) → EvalExpr fr m (.binary op a b) (.reverted p.data)
  | binaryLeftRevert : EvalExpr fr m a (.reverted d) → EvalExpr fr m (.binary op a b) (.reverted d)
  | binaryRightRevert : EvalExpr fr m a (.ok va fr1 m1) → EvalExpr fr1 m1 b (.reverted d) →
      (op ≠ .and ∨ va = .bool true) → (op ≠ .or ∨ va = .bool false) → EvalExpr fr m (.binary op a b) (.reverted d)
  | condT : EvalExpr fr m c (.ok (.bool true) fr1 m1) → EvalExpr fr1 m1 t r → EvalExpr fr m (.cond c t e) r
  | condF : EvalExpr fr m c (.ok (.bool false) fr1 m1) → EvalExpr fr1 m1 e r → EvalExpr fr m (.cond c t e) r
  | condRevert : EvalExpr fr m c (.reverted d) → EvalExpr fr m (.cond c t e) (.reverted d)
  -- assignment (right-hand side first)
  | assignPlain : isTupleExpr lhs = false → EvalExpr fr m rhs (.ok v fr1 m1) → EvalLValue fr1 m1 lhs (.ok lv fr2 m2) →
      assign cfg fc.types fr2 m2 lv v = some (.ok (fr3, m3)) → EvalExpr fr m (.assign .assign lhs rhs) (.ok v fr3 m3)
  | assignTuple : EvalExpr fr m rhs (.ok (.tuple vs) fr1 m1) → AssignTuple fr1 m1 lhss vs (.ok () fr2 m2) →
      EvalExpr fr m (.assign .assign (.tuple lhss) rhs) (.ok (.tuple vs) fr2 m2)
  | assignTupleRevert : EvalExpr fr m rhs (.ok (.tuple vs) fr1 m1) → AssignTuple fr1 m1 lhss vs (.reverted d) →
      EvalExpr fr m (.assign .assign (.tuple lhss) rhs) (.reverted d)
  | assignPanic : isTupleExpr lhs = false → EvalExpr fr m rhs (.ok v fr1 m1) → EvalLValue fr1 m1 lhs (.ok lv fr2 m2) →
      assign cfg fc.types fr2 m2 lv v = some (.error p) → EvalExpr fr m (.assign .assign lhs rhs) (.reverted p.data)
  | assignCompound : isTupleExpr lhs = false → op ≠ .assign → EvalExpr fr m rhs (.ok v fr1 m1) → EvalLValue fr1 m1 lhs (.ok lv fr2 m2) →
      readLValue cfg fc.types fr2 m2 lv = some (.ok cur) → binop (!fr2.unchecked) (assignOp op) cur v = some (.ok r) →
      assign cfg fc.types fr2 m2 lv r = some (.ok (fr3, m3)) → EvalExpr fr m (.assign op lhs rhs) (.ok r fr3 m3)
  | assignCompoundPanic : isTupleExpr lhs = false → op ≠ .assign → EvalExpr fr m rhs (.ok v fr1 m1) → EvalLValue fr1 m1 lhs (.ok lv fr2 m2) →
      readLValue cfg fc.types fr2 m2 lv = some (.ok cur) → binop (!fr2.unchecked) (assignOp op) cur v = some (.error p) →
      EvalExpr fr m (.assign op lhs rhs) (.reverted p.data)
  | assignCompoundReadPanic : isTupleExpr lhs = false → op ≠ .assign → EvalExpr fr m rhs (.ok v fr1 m1) → EvalLValue fr1 m1 lhs (.ok lv fr2 m2) →
      readLValue cfg fc.types fr2 m2 lv = some (.error p) → EvalExpr fr m (.assign op lhs rhs) (.reverted p.data)
  | assignCompoundAssignPanic : isTupleExpr lhs = false → op ≠ .assign → EvalExpr fr m rhs (.ok v fr1 m1) → EvalLValue fr1 m1 lhs (.ok lv fr2 m2) →
      readLValue cfg fc.types fr2 m2 lv = some (.ok cur) → binop (!fr2.unchecked) (assignOp op) cur v = some (.ok r) →
      assign cfg fc.types fr2 m2 lv r = some (.error p) → EvalExpr fr m (.assign op lhs rhs) (.reverted p.data)
  | assignRhsRevert : EvalExpr fr m rhs (.reverted d) → EvalExpr fr m (.assign op lhs rhs) (.reverted d)
  | assignLhsRevert : isTupleExpr lhs = false → EvalExpr fr m rhs (.ok v fr1 m1) → EvalLValue fr1 m1 lhs (.reverted d) →
      EvalExpr fr m (.assign op lhs rhs) (.reverted d)
  -- tuples and array literals
  | tuple : es.mapM (fun x => x) = some es' → EvalExprs fr m es' (.ok vs fr1 m1) → EvalExpr fr m (.tuple es) (.ok (.tuple vs) fr1 m1)
  | tupleRevert : es.mapM (fun x => x) = some es' → EvalExprs fr m es' (.reverted d) → EvalExpr fr m (.tuple es) (.reverted d)
  | arrayLit : EvalExprs fr m es (.ok vs fr1 m1) → arrayLitObj fc.types m1 vs = some (.ok (v, m2)) →
      EvalExpr fr m (.arrayLit es) (.ok v fr1 m2)
  | arrayLitPanic : EvalExprs fr m es (.ok vs fr1 m1) → arrayLitObj fc.types m1 vs = some (.error p) →
      EvalExpr fr m (.arrayLit es) (.reverted p.data)
  | arrayLitRevert : EvalExprs fr m es (.reverted d) → EvalExpr fr m (.arrayLit es) (.reverted d)

/-- `{value: e}` of a call: `0` when absent. -/
inductive EvalValueOpt : Frame → Machine → Option Expr → Res Nat → Prop where
  | none : EvalValueOpt fr m none (.ok 0 fr m)
  | some : EvalExpr fr m e (.ok v fr1 m1) → natValue v = some n → EvalValueOpt fr m (some e) (.ok n fr1 m1)
  | revert : EvalExpr fr m e (.reverted d) → EvalValueOpt fr m (some e) (.reverted d)

/-- The `{gas: …}` option: `none` forwards all gas. -/
inductive EvalGasOpt : Frame → Machine → Option Expr → Res (Option Nat) → Prop where
  | none : EvalGasOpt fr m none (.ok none fr m)
  | some : EvalExpr fr m e (.ok v fr1 m1) → natValue v = some n → EvalGasOpt fr m (some e) (.ok (some n) fr1 m1)
  | revert : EvalExpr fr m e (.reverted d) → EvalGasOpt fr m (some e) (.reverted d)

inductive EvalSaltOpt : Frame → Machine → Option Expr → Res (Option ByteArray) → Prop where
  | none : EvalSaltOpt fr m none (.ok none fr m)
  | some : EvalExpr fr m e (.ok v fr1 m1) → saltBytes v = some s → EvalSaltOpt fr m (some e) (.ok (some s) fr1 m1)
  | revert : EvalExpr fr m e (.reverted d) → EvalSaltOpt fr m (some e) (.reverted d)

inductive EvalExprs : Frame → Machine → List Expr → Res (List Value) → Prop where
  | nil : EvalExprs fr m [] (.ok [] fr m)
  | cons : EvalExpr fr m e (.ok v fr1 m1) → EvalExprs fr1 m1 es (.ok vs fr2 m2) →
      EvalExprs fr m (e :: es) (.ok (v :: vs) fr2 m2)
  | headRevert : EvalExpr fr m e (.reverted d) → EvalExprs fr m (e :: es) (.reverted d)
  | tailRevert : EvalExpr fr m e (.ok v fr1 m1) → EvalExprs fr1 m1 es (.reverted d) →
      EvalExprs fr m (e :: es) (.reverted d)

inductive EvalLValue : Frame → Machine → Expr → Res LValue → Prop where
  | local : fr.get? x = some l → EvalLValue fr m (.ident x) (.ok (.local x) fr m)
  | stateVar : fr.get? x = none → fc.var? x = some v → v.mutability = .mutable →
      EvalLValue fr m (.ident x) (.ok (.storage ⟨v.key, []⟩ v.ty) fr m)
  | immutableVar : fr.get? x = none → fc.var? x = some v → v.mutability = .immutable →
      EvalLValue fr m (.ident x) (.ok (.local (immName x)) fr m)
  | memberStorage : EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) → storageField fc.types er ty f = some (er', fty) →
      EvalLValue fr m (.member e f) (.ok (.storage er' fty) fr1 m1)
  | memberMem : EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → EvalLValue fr m (.member e f) (.ok (.memField obj f) fr1 m1)
  | memberRevert : EvalExpr fr m e (.reverted d) → EvalLValue fr m (.member e f) (.reverted d)
  | indexStorage : EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      storageIndex cfg fc.types m2.evm m2.heap er ty iv = some (.ok (er', ty')) →
      EvalLValue fr m (.index e i) (.ok (.storage er' ty') fr2 m2)
  | indexStoragePanic : EvalExpr fr m e (.ok (.storageRef er ty) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      storageIndex cfg fc.types m2.evm m2.heap er ty iv = some (.error p) → EvalLValue fr m (.index e i) (.reverted p.data)
  | indexMem : EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      natOperand iv = some n → memLength m2.heap obj = some len → n < len →
      EvalLValue fr m (.index e i) (.ok (.memIndex obj n) fr2 m2)
  | indexMemPanic : EvalExpr fr m e (.ok (.memRef obj) fr1 m1) → EvalExpr fr1 m1 i (.ok iv fr2 m2) →
      natOperand iv = some n → memLength m2.heap obj = some len → n ≥ len →
      EvalLValue fr m (.index e i) (.reverted (panicData 0x32))
  | indexBaseRevert : EvalExpr fr m e (.reverted d) → EvalLValue fr m (.index e i) (.reverted d)
  | indexRevert : EvalExpr fr m e (.ok v fr1 m1) → EvalExpr fr1 m1 i (.reverted d) → EvalLValue fr m (.index e i) (.reverted d)

/-- Assign the components of a tuple to the (optional) component lvalues, left to right. -/
inductive AssignTuple : Frame → Machine → List (Option Expr) → List Value → Res Unit → Prop where
  | nil : AssignTuple fr m [] [] (.ok () fr m)
  | skip : AssignTuple fr m ls vs r → AssignTuple fr m (none :: ls) (v :: vs) r
  | cons : EvalLValue fr m l (.ok lv fr1 m1) → assign cfg fc.types fr1 m1 lv v = some (.ok (fr2, m2)) →
      AssignTuple fr2 m2 ls vs r → AssignTuple fr m (some l :: ls) (v :: vs) r
  | revert : EvalLValue fr m l (.reverted d) → AssignTuple fr m (some l :: ls) (v :: vs) (.reverted d)
  | assignPanic : EvalLValue fr m l (.ok lv fr1 m1) → assign cfg fc.types fr1 m1 lv v = some (.error p) →
      AssignTuple fr m (some l :: ls) (v :: vs) (.reverted p.data)

inductive ExecStmt : Frame → Machine → Stmt → ExecResult → Prop where
  | block : ExecBlock fr m ss r → ExecStmt fr m (.block ss) r
  | varDeclNone : declare cfg fc.types fr m ty loc x none = some (.ok (fr', m')) →
      ExecStmt fr m (.varDecl ty loc x none) (.normal fr' m')
  | varDecl : EvalExpr fr m e (.ok v fr1 m1) → declare cfg fc.types fr1 m1 ty loc x (some v) = some (.ok (fr2, m2)) →
      ExecStmt fr m (.varDecl ty loc x (some e)) (.normal fr2 m2)
  | varDeclRevert : EvalExpr fr m e (.reverted d) → ExecStmt fr m (.varDecl ty loc x (some e)) (.reverted d)
  | varDeclNonePanic : declare cfg fc.types fr m ty loc x none = some (.error p) →
      ExecStmt fr m (.varDecl ty loc x none) (.reverted p.data)
  | varDeclPanic : EvalExpr fr m e (.ok v fr1 m1) → declare cfg fc.types fr1 m1 ty loc x (some v) = some (.error p) →
      ExecStmt fr m (.varDecl ty loc x (some e)) (.reverted p.data)
  | tupleDecl : EvalExpr fr m rhs (.ok (.tuple vs) fr1 m1) → DeclareTuple fr1 m1 binders vs (.ok () fr2 m2) →
      ExecStmt fr m (.tupleDecl binders rhs) (.normal fr2 m2)
  | tupleDeclRevert : EvalExpr fr m rhs (.reverted d) → ExecStmt fr m (.tupleDecl binders rhs) (.reverted d)
  | tupleDeclPanic : EvalExpr fr m rhs (.ok (.tuple vs) fr1 m1) → DeclareTuple fr1 m1 binders vs (.reverted d) →
      ExecStmt fr m (.tupleDecl binders rhs) (.reverted d)
  | exprStmt : EvalExpr fr m e (.ok v fr1 m1) → ExecStmt fr m (.exprStmt e) (.normal fr1 m1)
  | exprStmtRevert : EvalExpr fr m e (.reverted d) → ExecStmt fr m (.exprStmt e) (.reverted d)
  | iteT : EvalExpr fr m c (.ok (.bool true) fr1 m1) → ExecStmt fr1 m1 t r → ExecStmt fr m (.ite c t e) r
  | iteF : EvalExpr fr m c (.ok (.bool false) fr1 m1) → ExecStmt fr1 m1 s r → ExecStmt fr m (.ite c t (some s)) r
  | iteFNone : EvalExpr fr m c (.ok (.bool false) fr1 m1) → ExecStmt fr m (.ite c t none) (.normal fr1 m1)
  | iteRevert : EvalExpr fr m c (.reverted d) → ExecStmt fr m (.ite c t e) (.reverted d)
  | while : ExecLoop fr m (some c) none body r → ExecStmt fr m (.while c body) r
  | doWhile : ExecStmt fr m body (.normal fr1 m1) → ExecLoop fr1 m1 (some c) none body r →
      ExecStmt fr m (.doWhile body c) r
  | doWhileContinue : ExecStmt fr m body (.continue fr1 m1) → ExecLoop fr1 m1 (some c) none body r →
      ExecStmt fr m (.doWhile body c) r
  | doWhileBreak : ExecStmt fr m body (.break fr1 m1) → ExecStmt fr m (.doWhile body c) (.normal fr1 m1)
  | doWhileReturn : ExecStmt fr m body (.returned fr1 m1) → ExecStmt fr m (.doWhile body c) (.returned fr1 m1)
  | doWhileRevert : ExecStmt fr m body (.reverted d) → ExecStmt fr m (.doWhile body c) (.reverted d)
  | forNoInit : ExecLoop fr m c post body r → ExecStmt fr m (.for none c post body) r
  | forInit : ExecStmt fr m init (.normal fr1 m1) → ExecLoop fr1 m1 c post body r → ExecStmt fr m (.for (some init) c post body) r
  | forInitRevert : ExecStmt fr m init (.reverted d) → ExecStmt fr m (.for (some init) c post body) (.reverted d)
  | break : ExecStmt fr m .break (.break fr m)
  | continue : ExecStmt fr m .continue (.continue fr m)
  | returnNone : ExecStmt fr m (.return none) (.returned fr m)
  | returnSingle : fr.retVars = [r] → EvalExpr fr m e (.ok v fr1 m1) → assign cfg fc.types fr1 m1 (.local r) v = some (.ok (fr2, m2)) →
      ExecStmt fr m (.return (some e)) (.returned fr2 m2)
  | returnMulti : fr.retVars.length ≥ 2 → EvalExpr fr m e (.ok (.tuple vs) fr1 m1) →
      AssignTuple fr1 m1 (fr.retVars.map fun r => some (.ident r)) vs (.ok () fr2 m2) →
      ExecStmt fr m (.return (some e)) (.returned fr2 m2)
  | returnRevert : EvalExpr fr m e (.reverted d) → ExecStmt fr m (.return (some e)) (.reverted d)
  | returnSinglePanic : fr.retVars = [r] → EvalExpr fr m e (.ok v fr1 m1) →
      assign cfg fc.types fr1 m1 (.local r) v = some (.error p) → ExecStmt fr m (.return (some e)) (.reverted p.data)
  | returnMultiRevert : fr.retVars.length ≥ 2 → EvalExpr fr m e (.ok (.tuple vs) fr1 m1) →
      AssignTuple fr1 m1 (fr.retVars.map fun r => some (.ident r)) vs (.reverted d) →
      ExecStmt fr m (.return (some e)) (.reverted d)
  | emit : fc.event? ev = some ei → argExprs (ei.decl.params.map (·.name)) args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) vs = some (.ok (svs, m2)) →
      mkLogEntry m2.this ei svs = some le → ExecStmt fr m (.emit (.ident ev) args) (.normal fr1 (m2.pushLog le))
  | emitRevert : fc.event? ev = some ei → argExprs (ei.decl.params.map (·.name)) args = some es →
      EvalExprs fr m es (.reverted d) → ExecStmt fr m (.emit (.ident ev) args) (.reverted d)
  | emitPanic : fc.event? ev = some ei → argExprs (ei.decl.params.map (·.name)) args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) vs = some (.error p) →
      ExecStmt fr m (.emit (.ident ev) args) (.reverted p.data)
  | revertError : fc.error? err = some ei → argExprs (paramNames ei.decl.params) args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) vs = some (.ok (svs, m2)) →
      customErrorData ei.sigStr ei.sig.paramTypes svs = some d → ExecStmt fr m (.revert (.ident err) args) (.reverted d)
  | revertErrorArgsRevert : fc.error? err = some ei → argExprs (paramNames ei.decl.params) args = some es →
      EvalExprs fr m es (.reverted d) → ExecStmt fr m (.revert (.ident err) args) (.reverted d)
  | revertErrorPanic : fc.error? err = some ei → argExprs (paramNames ei.decl.params) args = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) vs = some (.error p) →
      ExecStmt fr m (.revert (.ident err) args) (.reverted p.data)
  | unchecked : ExecBlock { fr with unchecked := true } m ss r →
      ExecStmt fr m (.unchecked ss) (restoreUnchecked fr.unchecked r)
  | placeholder : ExecChain (popFrame fr) m fr.chain fr.body r → settlePlaceholder fr r = some r' →
      ExecStmt fr m .placeholder r'

/-- Bind tuple-destructuring binders (`none` skips a component). -/
inductive DeclareTuple : Frame → Machine → List (Option Param) → List Value → Res Unit → Prop where
  | nil : DeclareTuple fr m [] [] (.ok () fr m)
  | skip : DeclareTuple fr m bs vs r → DeclareTuple fr m (none :: bs) (v :: vs) r
  | cons : p.name = some x → declare cfg fc.types fr m p.ty p.loc x (some v) = some (.ok (fr1, m1)) →
      DeclareTuple fr1 m1 bs vs r → DeclareTuple fr m (some p :: bs) (v :: vs) r
  | panic : p.name = some x → declare cfg fc.types fr m p.ty p.loc x (some v) = some (.error q) →
      DeclareTuple fr m (some p :: bs) (v :: vs) (.reverted q.data)

/-- A loop iteration: `cond? ; body ; post?` (`while`, `for`). -/
inductive ExecLoop : Frame → Machine → Option Expr → Option Expr → Stmt → ExecResult → Prop where
  | condFalse : EvalExpr fr m c (.ok (.bool false) fr1 m1) → ExecLoop fr m (some c) post body (.normal fr1 m1)
  | condRevert : EvalExpr fr m c (.reverted d) → ExecLoop fr m (some c) post body (.reverted d)
  | iterate : EvalCond fr m c (.ok true fr1 m1) → ExecStmt fr1 m1 body (.normal fr2 m2) →
      ExecPost fr2 m2 post (.ok () fr3 m3) → ExecLoop fr3 m3 c post body r → ExecLoop fr m c post body r
  | iterateContinue : EvalCond fr m c (.ok true fr1 m1) → ExecStmt fr1 m1 body (.continue fr2 m2) →
      ExecPost fr2 m2 post (.ok () fr3 m3) → ExecLoop fr3 m3 c post body r → ExecLoop fr m c post body r
  | postRevert : EvalCond fr m c (.ok true fr1 m1) → ExecStmt fr1 m1 body (.normal fr2 m2) →
      ExecPost fr2 m2 post (.reverted d) → ExecLoop fr m c post body (.reverted d)
  | postRevertContinue : EvalCond fr m c (.ok true fr1 m1) → ExecStmt fr1 m1 body (.continue fr2 m2) →
      ExecPost fr2 m2 post (.reverted d) → ExecLoop fr m c post body (.reverted d)
  | breakOut : EvalCond fr m c (.ok true fr1 m1) → ExecStmt fr1 m1 body (.break fr2 m2) →
      ExecLoop fr m c post body (.normal fr2 m2)
  | returnOut : EvalCond fr m c (.ok true fr1 m1) → ExecStmt fr1 m1 body (.returned fr2 m2) →
      ExecLoop fr m c post body (.returned fr2 m2)
  | bodyRevert : EvalCond fr m c (.ok true fr1 m1) → ExecStmt fr1 m1 body (.reverted d) →
      ExecLoop fr m c post body (.reverted d)

/-- An optional loop condition (`none` is `true`). -/
inductive EvalCond : Frame → Machine → Option Expr → Res Bool → Prop where
  | none : EvalCond fr m none (.ok true fr m)
  | some : EvalExpr fr m c (.ok (.bool b) fr1 m1) → EvalCond fr m (some c) (.ok b fr1 m1)

/-- An optional loop post-expression. -/
inductive ExecPost : Frame → Machine → Option Expr → Res Unit → Prop where
  | none : ExecPost fr m none (.ok () fr m)
  | some : EvalExpr fr m e (.ok v fr1 m1) → ExecPost fr m (some e) (.ok () fr1 m1)
  | revert : EvalExpr fr m e (.reverted d) → ExecPost fr m (some e) (.reverted d)

inductive ExecBlock : Frame → Machine → List Stmt → ExecResult → Prop where
  | nil : ExecBlock fr m [] (.normal fr m)
  | cons : ExecStmt fr m s (.normal fr1 m1) → ExecBlock fr1 m1 ss r → ExecBlock fr m (s :: ss) r
  | consReturn : ExecStmt fr m s (.returned fr1 m1) → ExecBlock fr m (s :: ss) (.returned fr1 m1)
  | consBreak : ExecStmt fr m s (.break fr1 m1) → ExecBlock fr m (s :: ss) (.break fr1 m1)
  | consContinue : ExecStmt fr m s (.continue fr1 m1) → ExecBlock fr m (s :: ss) (.continue fr1 m1)
  | consRevert : ExecStmt fr m s (.reverted d) → ExecBlock fr m (s :: ss) (.reverted d)

/-- Run the remaining modifier chain, then the body. -/
inductive ExecChain : Frame → Machine → List (ModDef × List Value) → Block → ExecResult → Prop where
  | body : ExecBlock fr m body r → ExecChain fr m [] body r
  | modifier : bindModParams cfg fc.types (pushScope fr rest body) m md.decl.params vs = some (.ok (fr1, m1)) →
      md.decl.body = some mb → ExecBlock fr1 m1 mb r → ExecChain fr m ((md, vs) :: rest) body (popScope r)
  | modifierPanic : bindModParams cfg fc.types (pushScope fr rest body) m md.decl.params vs = some (.error p) →
      ExecChain fr m ((md, vs) :: rest) body (.reverted p.data)

/-- Resolve and evaluate the modifier invocations of a function (base-constructor calls are skipped). -/
inductive EvalMods : Frame → Machine → List ModifierInvocation → Res (List (ModDef × List Value)) → Prop where
  | nil : EvalMods fr m [] (.ok [] fr m)
  | cons : fc.modifier? mi.name = some md → argExprs (paramNames md.decl.params) (mi.args.getD (.positional [])) = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → EvalMods fr1 m1 rest (.ok mods fr2 m2) →
      EvalMods fr m (mi :: rest) (.ok ((md, vs) :: mods) fr2 m2)
  | consRevert : fc.modifier? mi.name = some md → argExprs (paramNames md.decl.params) (mi.args.getD (.positional [])) = some es →
      EvalExprs fr m es (.reverted d) → EvalMods fr m (mi :: rest) (.reverted d)
  | consTailRevert : fc.modifier? mi.name = some md → argExprs (paramNames md.decl.params) (mi.args.getD (.positional [])) = some es →
      EvalExprs fr m es (.ok vs fr1 m1) → EvalMods fr1 m1 rest (.reverted d) → EvalMods fr m (mi :: rest) (.reverted d)
  | skipBase : fc.modifier? mi.name = none → fc.linearization.contains mi.name = true →
      EvalMods fr m rest r → EvalMods fr m (mi :: rest) r

/-- Call a function with evaluated arguments in a fresh frame. -/
inductive CallFn : Frame → Machine → FnDef → List Value → FnResult → Prop where
  | ok : enterFn cfg fc.types fn.declaredIn fn.decl args m = some (.ok (fr0, m0)) →
      EvalMods fr0 m0 fn.decl.modifiers (.ok mods fr1 m1) → fn.decl.body = some body →
      ExecChain { fr1 with chain := mods, body := body } m1 mods body r → finished r = some (fr2, m2) →
      retVals fr2 = some rets → CallFn fr m fn args (.ok rets m2)
  | reverted : enterFn cfg fc.types fn.declaredIn fn.decl args m = some (.ok (fr0, m0)) →
      EvalMods fr0 m0 fn.decl.modifiers (.ok mods fr1 m1) → fn.decl.body = some body →
      ExecChain { fr1 with chain := mods, body := body } m1 mods body (.reverted d) → CallFn fr m fn args (.reverted d)
  | modsReverted : enterFn cfg fc.types fn.declaredIn fn.decl args m = some (.ok (fr0, m0)) →
      EvalMods fr0 m0 fn.decl.modifiers (.reverted d) → CallFn fr m fn args (.reverted d)
  | enterPanic : enterFn cfg fc.types fn.declaredIn fn.decl args m = some (.error p) → CallFn fr m fn args (.reverted p.data)

end

end Solidity
