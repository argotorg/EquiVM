import Solm.Syntax

/-!
# Solm — a Solidity-faithful surface syntax

A Lean-embedded frontend that lets a Solm spec be written in syntax as close to Solidity as the
host parser permits, desugaring to the exact `Solm` AST constructors.  A spec written with this
frontend is **definitionally equal** to the hand-written AST (checked by `rfl` in the per-contract
`SpecSyntax.lean` files).

Entry point:

```
def contractGen : ContractDecl := solidity% contract WETH9 {
  mapping(address => uint256) balanceOf;
  uint256 totalSupply;

  constructor() { ... }

  function transfer(address dst, uint256 wad) external returns (bool) {
    balanceOf[msg.sender] = balanceOf[msg.sender] - wad;
    ...
  }
}
```

## Design notes

* **No word becomes a reserved token.**  Reserving e.g. `mapping`, `storage`, `function`, or
  `contract` as syntax atoms would break every identifier of that name in files importing this one
  (specs define `def contract`, `ContractDecl` has a `storage` field, …).  Non-reserved `&"kw"`
  atoms cannot head a syntax-category production (the category dispatcher never fires them for
  ident tokens), so every keyword-headed form is parsed as a *generic ident-headed production* and
  the keyword is recognised by name during macro expansion.  Only symbols and words Lean already
  reserves (`if`, `else`, `while`, `for`, `return`, `break`, `continue`, `try`, `catch`, `delete`,
  `this`) appear as atoms.
* **Name resolution instead of sigils.**  The contract macro first collects declared storage
  variables, structs, and internal functions, then translates bodies with that environment:
  `balanceOf[dst]` resolves to a storage reference, a local `wad` to `Expr.var`, `min(a, b)` to an
  internal call, `vat.move(a, b)` to an external call.  Mapping vs array indexing (`.mindex` vs
  `.aindex`) is decided by walking the declared storage type.
* **Dotted names arrive as single ident tokens** (`msg.sender`, `ilks.rate`); they are split into
  components at expansion time.  `a[i].f` parses via a postfix production.
* **Payability is implicit, as in Solidity.**  Transitions, constructors, and fallbacks that are
  not marked `payable` get the leading `require(msg.value == 0)` guard solc compiles in;
  `receive` and internal functions never do.
* **Escape hatches** for the places specs are parameterized by Lean terms:
  `${e}` embeds a Lean term as an `Expr` (statement position: a `List Stmt` splice, item position:
  a `TransitionDecl`), `#n` embeds a Lean `Int` term as an `Expr.intLit`.
* Solidity names that are Lean keywords (`from`, `to`, `end`) are written with guillemets:
  `«from»`, `«to»`.
-/

open Lean

namespace Solm.Notation
open Solm ABI

private abbrev LIdent := TSyntax `ident

/-! ## Macro-time types -/

/-- Macro-time image of a surface type. -/
private inductive STy where
  | named : String → STy
  | mapping : STy → STy → STy
  | array : STy → Option Nat → STy
  | tuple : List STy → STy
  deriving Inhabited, Repr, BEq

/-- Translation environment: declared names of the enclosing contract plus the local scope. -/
private structure Env where
  storage : List (String × STy) := []
  structs : List (String × List (String × STy)) := []
  /-- internal function names -/
  fns : List String := []
  /-- params, lets, call binders, and storage aliases in scope -/
  locals : List String := []

private def Env.isLocal (env : Env) (s : String) : Bool := env.locals.contains s
private def Env.storageTy? (env : Env) (s : String) : Option STy :=
  if env.isLocal s then none else env.storage.lookup s

/-! ## Scalar type names -/

private def widthOf? (s pfx : String) : Option Nat :=
  if s.startsWith pfx then (s.drop pfx.length).toNat? else none

private def natLit (n : Nat) : NumLit := Syntax.mkNumLit (toString n)

/-- `ABI.ElemType` for a scalar type name, if it is one. -/
private def elemTypeTerm? (s : String) : MacroM (Option Term) := do
  if s == "address" then return some (← `(ABI.ElemType.address))
  else if s == "bool" then return some (← `(ABI.ElemType.bool))
  else if let some n := widthOf? s "uint" then
    return some (← `(ABI.ElemType.int (ABI.IntType.uint ⟨$(natLit n), by decide⟩)))
  else if let some n := widthOf? s "int" then
    return some (← `(ABI.ElemType.int (ABI.IntType.sint ⟨$(natLit n), by decide⟩)))
  else if let some n := widthOf? s "bytes" then
    if n == 0 || n > 32 then return none
    else return some (← `(ABI.ElemType.bytes ⟨$(natLit (n - 1)), by decide⟩))
  else return none

private def intTypeTerm (stx : Syntax) (s : String) : MacroM Term := do
  if let some n := widthOf? s "uint" then `(ABI.IntType.uint ⟨$(natLit n), by decide⟩)
  else if let some n := widthOf? s "int" then `(ABI.IntType.sint ⟨$(natLit n), by decide⟩)
  else Macro.throwErrorAt stx s!"solm: '{s}' is not an integer type"

/-- `Solm.StorageType` for an `STy`, resolving struct names through the environment. -/
private partial def storageTypeTerm (env : Env) (stx : Syntax) : STy → MacroM Term
  | .named "bytes" => `(Solm.StorageType.bytes)
  | .named "string" => `(Solm.StorageType.string)
  | .named s => do
      if let some e ← elemTypeTerm? s then `(Solm.StorageType.elem $e)
      else if let some fields := env.structs.lookup s then
        let fieldTerms ← fields.mapM fun (f, fty) => do
          `(($(quote f), $(← storageTypeTerm env stx fty)))
        `(Solm.StorageType.struct $(quote s) [$(fieldTerms.toArray),*])
      else Macro.throwErrorAt stx s!"solm: unknown type '{s}'"
  | .mapping k v => do
      let kt ← match k with
        | .named s => do
            match ← elemTypeTerm? s with
            | some t => pure t
            | none => Macro.throwErrorAt stx s!"solm: mapping key '{s}' is not a scalar type"
        | _ => Macro.throwErrorAt stx "solm: mapping key must be a scalar type"
      `(Solm.StorageType.mapping $kt $(← storageTypeTerm env stx v))
  | .array t none => do `(Solm.StorageType.dynamicArray $(← storageTypeTerm env stx t))
  | .array t (some n) => do `(Solm.StorageType.array $(← storageTypeTerm env stx t) $(natLit n))
  | .tuple ts => do
      let terms ← ts.mapM (storageTypeTerm env stx)
      `(Solm.StorageType.tuple [$(terms.toArray),*])

/-- `ABI.ABIType` for an `STy` (param and return types).  Structs become ABI tuples. -/
private partial def abiTypeTerm (env : Env) (stx : Syntax) : STy → MacroM Term
  | .named "bytes" => `(ABI.ABIType.bytes)
  | .named "string" => `(ABI.ABIType.string)
  | .named s => do
      if let some e ← elemTypeTerm? s then `(ABI.ABIType.elem $e)
      else if let some fields := env.structs.lookup s then
        let fieldTerms ← fields.mapM fun (_, fty) => abiTypeTerm env stx fty
        `(ABI.ABIType.tuple [$(fieldTerms.toArray),*])
      else Macro.throwErrorAt stx s!"solm: unknown ABI type '{s}'"
  | .mapping _ _ => Macro.throwErrorAt stx "solm: mapping is not an ABI type"
  | .array t none => do `(ABI.ABIType.dynamicArray $(← abiTypeTerm env stx t))
  | .array t (some n) => do `(ABI.ABIType.array $(← abiTypeTerm env stx t) $(natLit n))
  | .tuple ts => do
      let terms ← ts.mapM (abiTypeTerm env stx)
      `(ABI.ABIType.tuple [$(terms.toArray),*])

/-! ## Grammar -/

declare_syntax_cat solTy
syntax:max ident : solTy
-- `atomic` up to the arrow so a failed try (e.g. `bytes(0)` in expressions) backtracks silently.
syntax:max atomic(ident "(" solTy " => ") solTy ")" : solTy   -- mapping(K => V)
syntax:max solTy "[" "]" : solTy
syntax:max solTy "[" num "]" : solTy
syntax:max "(" solTy "," solTy,* ")" : solTy   -- ABI tuple type (address, uint256)

declare_syntax_cat solExpr
declare_syntax_cat solCallOpt
syntax ident : solCallOpt                             -- {view}
syntax ident ": " solExpr : solCallOpt                -- {value: e}
syntax solStructField := ident ": " solExpr

syntax:max num : solExpr
syntax:max str : solExpr
syntax:max ident : solExpr
syntax:max "this" : solExpr
syntax:max "(" solExpr ")" : solExpr
syntax:max ident "(" solExpr,* ")" : solExpr                          -- calls, casts, builtins
syntax:max ident "{" solCallOpt,* "}" "(" solExpr,* ")" : solExpr     -- ext call w/ options
syntax:max ident "(" "{" solStructField,* "}" ")" : solExpr           -- struct literal
syntax:max ident solTy "(" solExpr ")" : solExpr                      -- new bytes(n), new T[](n)
syntax:max solExpr "[" solExpr "]" : solExpr                          -- index
syntax:max solExpr "[" solExpr " : " solExpr "]" : solExpr            -- byte slice
syntax:max solExpr "." ident : solExpr                                -- field / .max / .length …
syntax:max solExpr "." num : solExpr                                  -- tuple projection
syntax:max "${" term "}" : solExpr                                    -- Lean `Expr` escape
syntax:max "#" term:max : solExpr                                     -- Lean `Int` → intLit escape

syntax:75 "!" solExpr:75 : solExpr
syntax:75 "~" solExpr:75 : solExpr
syntax:75 "-" solExpr:75 : solExpr
syntax:74 solExpr:75 " ** " solExpr:74 : solExpr
syntax:70 solExpr:70 " * " solExpr:71 : solExpr
syntax:70 solExpr:70 " / " solExpr:71 : solExpr
syntax:70 solExpr:70 " % " solExpr:71 : solExpr
syntax:65 solExpr:65 " + " solExpr:66 : solExpr
syntax:65 solExpr:65 " - " solExpr:66 : solExpr
syntax:60 solExpr:60 " << " solExpr:61 : solExpr
syntax:60 solExpr:60 " >> " solExpr:61 : solExpr
syntax:57 solExpr:57 " & " solExpr:58 : solExpr
syntax:55 solExpr:55 " ^ " solExpr:56 : solExpr
syntax:53 solExpr:53 " | " solExpr:54 : solExpr
syntax:50 solExpr:51 " < " solExpr:51 : solExpr
syntax:50 solExpr:51 " <= " solExpr:51 : solExpr
syntax:50 solExpr:51 " > " solExpr:51 : solExpr
syntax:50 solExpr:51 " >= " solExpr:51 : solExpr
syntax:47 solExpr:48 " == " solExpr:48 : solExpr
syntax:47 solExpr:48 " != " solExpr:48 : solExpr
syntax:45 solExpr:46 " as " ident : solExpr                           -- Expr.inRange
syntax:35 solExpr:36 " && " solExpr:35 : solExpr
syntax:30 solExpr:31 " || " solExpr:30 : solExpr
syntax:20 solExpr:21 " ? " solExpr " : " solExpr:20 : solExpr

declare_syntax_cat solStmt
declare_syntax_cat solForPost
declare_syntax_cat solBind
syntax solTy ident : solBind
syntax solTy ident ident : solBind                                    -- bytes memory data

syntax solTy ident " = " solExpr ";" : solStmt                        -- T x = e; (also `var x = e;`)
syntax solTy ident ident " = " solExpr ";" : solStmt                  -- T memory x = e; / T storage x = p;
syntax solExpr:max " = " solExpr ";" : solStmt                        -- path assignment
syntax solExpr:max " += " solExpr ";" : solStmt
syntax solExpr:max " -= " solExpr ";" : solStmt
syntax solExpr:max " *= " solExpr ";" : solStmt
syntax solExpr:max " /= " solExpr ";" : solStmt
syntax solExpr:max ";" : solStmt                                      -- require(e); a.push(e); …
syntax solExpr:max "(" solExpr,* ")" ";" : solStmt                    -- path-method call: b[a].push(x);
syntax "(" solBind,* ")" " = " solExpr ";" : solStmt                  -- (bool ok, bytes memory d) = t.call…
syntax "if " "(" solExpr ")" "{" solStmt* "}" : solStmt
syntax "if " "(" solExpr ")" "{" solStmt* "}" " else " "{" solStmt* "}" : solStmt
syntax "if " "(" solExpr ")" "{" solStmt* "}" " else " solStmt : solStmt   -- else-if chain
syntax "while " "(" solExpr ")" "{" solStmt* "}" : solStmt
syntax "for " "(" solStmt solExpr "; " solForPost ")" "{" solStmt* "}" : solStmt
syntax "return " solExpr,* ";" : solStmt
syntax "return " "(" solExpr "," solExpr,* ")" ";" : solStmt          -- multi-value return
syntax "break" ";" : solStmt
syntax "continue" ";" : solStmt
syntax "delete " solExpr:max ";" : solStmt
syntax "try " solExpr:max ident "(" ident ")" "{" solStmt* "}"
    " catch " "(" ident ")" "{" solStmt* "}" : solStmt                -- try …(…) returns (r) {…} catch (e) {…}
syntax "${" term "}" : solStmt                                        -- Lean `List Stmt` splice

syntax solExpr:max " = " solExpr : solForPost
syntax solExpr:max " += " solExpr : solForPost
syntax solExpr:max "++" : solForPost

declare_syntax_cat solParam
syntax solTy ident : solParam
syntax solTy ident ident : solParam                                   -- bytes memory data

declare_syntax_cat solItem
syntax solTy ident ";" : solItem                                      -- storage decl
syntax solTy ident ident ";" : solItem                                -- with visibility
syntax solStructMember := solTy ident ";"
syntax ident ident "{" solStructMember* "}" : solItem                 -- struct S { … }
syntax ident "(" solParam,* ")" ident* "{" solStmt* "}" : solItem     -- constructor/receive/fallback
syntax (name := solItemCtorRets)                                      -- fallback with returns clause
  ident "(" solParam,* ")" ident* "(" solTy,* ")" "{" solStmt* "}" : solItem
syntax ident ident "(" solParam,* ")" ident* "{" solStmt* "}" : solItem
syntax (name := solItemFnRets)
  ident ident "(" solParam,* ")" ident* "(" solTy,* ")" "{" solStmt* "}" : solItem
syntax "${" term "}" : solItem                                        -- Lean `TransitionDecl` splice

syntax:max "solidity% " ident ident "{" solItem* "}" : term

/-! ## Surface-type parsing -/

private partial def parseTy (stx : TSyntax `solTy) : MacroM STy := do
  match stx with
  | `(solTy| $x:ident) => return .named x.getId.toString
  | `(solTy| $m:ident ($k:solTy => $v:solTy)) => do
      unless m.getId.toString == "mapping" do
        Macro.throwErrorAt m.raw "solm: expected 'mapping'"
      return .mapping (← parseTy k) (← parseTy v)
  | `(solTy| $t:solTy []) => return .array (← parseTy t) none
  | `(solTy| $t:solTy [$n:num]) => return .array (← parseTy t) (some n.getNat)
  | `(solTy| ($t0:solTy, $ts:solTy,*)) => do
      return .tuple ((← parseTy t0) :: (← ts.getElems.toList.mapM parseTy))
  | _ => Macro.throwErrorAt stx "solm: unrecognized type"

/-! ## Path resolution -/

/-- One step of a postfix path, still syntactic. -/
private inductive PStep where
  | field : String → PStep
  | index : TSyntax `solExpr → PStep
  | slice : TSyntax `solExpr → TSyntax `solExpr → PStep
  | tup : Nat → PStep

private def PStep.fieldName? : PStep → Option String
  | .field f => some f
  | _ => none

/-- Flatten a postfix chain (`a.b[i].c` …) into head components plus steps.
    Returns `none` if the head is not an ident. -/
private partial def flattenPath (stx : TSyntax `solExpr) :
    Option (Syntax × List String × List PStep) := do
  match stx with
  | `(solExpr| $x:ident) =>
      some (x.raw, x.getId.components.map (·.toString), [])
  | `(solExpr| $a:solExpr [ $i ]) => do
      let (h, cs, steps) ← flattenPath a
      some (h, cs, steps ++ [.index i])
  | `(solExpr| $a:solExpr [ $i : $j ]) => do
      let (h, cs, steps) ← flattenPath a
      some (h, cs, steps ++ [.slice i j])
  | `(solExpr| $a:solExpr . $f:ident) => do
      let (h, cs, steps) ← flattenPath a
      some (h, cs, steps ++ (f.getId.components.map (fun c => .field c.toString)))
  | `(solExpr| $a:solExpr . $n:num) => do
      let (h, cs, steps) ← flattenPath a
      some (h, cs, steps ++ [.tup n.getNat])
  | _ => none

/-- Environment variables reachable as (dotted) identifiers. -/
private def envVarOf? : List String → Option Name
  | ["msg", "sender"] => some `caller
  | ["msg", "value"] => some `callvalue
  | ["msg", "sig"] => some `msgSig
  | ["msg", "data"] => some `msgData
  | ["tx", "origin"] => some `origin
  | ["tx", "gasprice"] => some `gasprice
  | ["block", "timestamp"] => some `timestamp
  | ["block", "chainid"] => some `chainid
  | ["block", "number"] => some `number
  | ["block", "coinbase"] => some `coinbase
  | ["block", "gaslimit"] => some `gaslimit
  | ["block", "prevrandao"] => some `prevrandao
  | ["block", "basefee"] => some `basefee
  | _ => none

private def mkEnvVar (n : Name) : MacroM Term :=
  `(Solm.Expr.env $(mkIdent (`Solm.EnvVar ++ n)))

/-- A resolved reference path. -/
private structure RefInfo where
  origin : VarOrigin
  base : String
  /-- `Solm.StorageRefStep` terms -/
  steps : Array Term
  /-- remaining type after the walk (storage paths only) -/
  ty : Option STy
  /-- a trailing `.length` was consumed -/
  isLength : Bool := false
  /-- contains steps only expressible in expressions (tuple projection, slice) — not assignable -/
  exprOnly : Bool := false

private def refTerm (r : RefInfo) : MacroM Term := do
  if r.steps.isEmpty then
    `(({ base := $(quote r.base) } : Solm.StorageRef))
  else
    `(({ base := $(quote r.base), steps := [$(r.steps),*] } : Solm.StorageRef))

private def originTerm : VarOrigin → MacroM Term
  | .storage => `(Solm.VarOrigin.storage)
  | .localVar => `(Solm.VarOrigin.localVar)

mutual

/-- Resolve a flattened path against the environment.  `none` if the head is not a declared
    variable (caller decides whether that is an error). -/
private partial def resolveRef (env : Env) (stx : Syntax) (comps : List String)
    (steps0 : List PStep) : MacroM (Option RefInfo) := do
  match comps with
  | [] => return none
  | c0 :: rest =>
    let steps := rest.map PStep.field ++ steps0
    -- A trailing `.length` is the array-length accessor, not a struct field.
    let (steps, isLen) :=
      match steps.getLast? with
      | some (.field "length") => (steps.dropLast, true)
      | _ => (steps, false)
    if env.isLocal c0 then
      let mut out : Array Term := #[]
      let mut exprOnly := false
      for s in steps do
        match s with
        | .field f => out := out.push (← `(Solm.StorageRefStep.field $(quote f)))
        | .index e => out := out.push (← `(Solm.StorageRefStep.aindex $(← elabExpr env e)))
        | _ => exprOnly := true  -- tuple projection / slice: expression-fold handles these
      return some { origin := .localVar, base := c0, steps := out, ty := none,
                    isLength := isLen, exprOnly := exprOnly }
    else if let some ty0 := env.storageTy? c0 then
      let mut out : Array Term := #[]
      let mut ty := ty0
      for s in steps do
        match s, ty with
        | .field f, .named sname =>
            let some fields := env.structs.lookup sname
              | Macro.throwErrorAt stx s!"solm: '{sname}' has no fields"
            let some fty := fields.lookup f
              | Macro.throwErrorAt stx s!"solm: struct '{sname}' has no field '{f}'"
            out := out.push (← `(Solm.StorageRefStep.field $(quote f)))
            ty := fty
        | .index k, .mapping _ v =>
            out := out.push (← `(Solm.StorageRefStep.mindex $(← elabExpr env k)))
            ty := v
        | .index k, .array t _ =>
            out := out.push (← `(Solm.StorageRefStep.aindex $(← elabExpr env k)))
            ty := t
        | _, _ => Macro.throwErrorAt stx s!"solm: cannot resolve path step on '{c0}'"
      return some { origin := .storage, base := c0, steps := out, ty := some ty, isLength := isLen }
    else
      return none

/-- Translate an expression. -/
private partial def elabExpr (env : Env) (stx : TSyntax `solExpr) : MacroM Term := do
  -- Path-shaped expressions first: resolution decides var/storage/env-var.
  if let some (head, comps, steps) := flattenPath stx then
    -- Address-inspection builtins on a simple variable come before path resolution.
    let full := comps ++ (steps.filterMap PStep.fieldName?)
    let stepsAllFields := steps.all fun s => s.fieldName?.isSome
    if stepsAllFields then
      -- Base must be a local or an address-typed storage variable (a struct field named
      -- `balance`/`code`/`codehash` still resolves as a field below).
      let addrBase (x : String) : MacroM (Option Term) := do
        if env.isLocal x then return some (← `(Solm.Expr.var $(quote x)))
        else if env.storageTy? x == some (.named "address") then
          return some (← `(Solm.Expr.storage ({ base := $(quote x) } : Solm.StorageRef)))
        else return none
      match full with
      | [x, "code", "length"] =>
          if let some b ← addrBase x then return ← `(Solm.Expr.extCodeSize $b)
      | [x, "balance"] =>
          if let some b ← addrBase x then return ← `(Solm.Expr.balanceOf $b)
      | [x, "codehash"] =>
          if let some b ← addrBase x then return ← `(Solm.Expr.extCodeHash $b)
      | _ => pure ()
    if let some r ← resolveRef env stx comps steps then
      if r.isLength then
        return ← `(Solm.Expr.arrayLength $(← originTerm r.origin) $(← refTerm r))
      match r.origin with
      | .storage => return ← `(Solm.Expr.storage $(← refTerm r))
      | .localVar =>
          -- Fold a local path into pure expression forms.
          let mut e ← `(Solm.Expr.var $(quote r.base))
          let allSteps := comps.tail.map PStep.field ++ steps
          for s in allSteps do
            match s with
            | .field f => e ← `(Solm.Expr.field $e $(quote f))
            | .index i => e ← `(Solm.Expr.index $e $(← elabExpr env i))
            | .slice a b => e ← `(Solm.Expr.bytesSlice $e $(← elabExpr env a) $(← elabExpr env b))
            | .tup n => e ← `(Solm.Expr.tupleGet $e $(natLit n))
          return e
    else
      match comps, steps with
      | cs, [] =>
          if let some v := envVarOf? cs then return ← mkEnvVar v
          else if cs == ["true"] then return ← `(Solm.Expr.boolLit true)
          else if cs == ["false"] then return ← `(Solm.Expr.boolLit false)
          else Macro.throwErrorAt head s!"solm: unknown identifier '{".".intercalate cs}'"
      | _, _ => Macro.throwErrorAt stx "solm: cannot resolve path"
  match stx with
  | `(solExpr| $n:num) => `(Solm.Expr.intLit $n)
  | `(solExpr| $s:str) => `(Solm.Expr.bytesLit (String.toByteArray $s))
  | `(solExpr| this) => mkEnvVar `this
  | `(solExpr| ($e:solExpr)) => elabExpr env e
  | `(solExpr| ${ $t }) => pure t
  | `(solExpr| # $t) => `(Solm.Expr.intLit $t)
  | `(solExpr| $f:ident ($args:solExpr,*)) => elabCall env stx f args.getElems
  | `(solExpr| $_:ident {$_:solCallOpt,*} ($_:solExpr,*)) =>
      Macro.throwErrorAt stx "solm: calls with {…} options are only allowed as statements"
  | `(solExpr| $s:ident ({$fields:solStructField,*})) => do
      let name := s.getId.toString
      unless (env.structs.lookup name).isSome do
        Macro.throwErrorAt s.raw s!"solm: unknown struct '{name}'"
      let fieldTerms ← fields.getElems.mapM fun fstx => do
        match fstx with
        | `(solStructField| $f:ident : $e:solExpr) => do
            `(($(quote f.getId.toString), $(← elabExpr env e)))
        | _ => Macro.throwErrorAt fstx "solm: malformed struct field"
      `(Solm.Expr.structLit $(quote name) [$fieldTerms,*])
  | `(solExpr| $kw:ident $t:solTy ($len:solExpr)) => do
      unless kw.getId.toString == "new" do
        Macro.throwErrorAt kw.raw "solm: expected 'new'"
      match ← parseTy t with
      | .named "bytes" => `(Solm.Expr.newBytes $(← elabExpr env len))
      | .array elt none =>
          `(Solm.Expr.newArray $(← storageTypeTerm env t elt) $(← elabExpr env len))
      | _ => Macro.throwErrorAt t "solm: 'new' expects 'bytes' or a dynamic array type"
  | `(solExpr| $a:solExpr . $f:ident) => do
      let fname := f.getId.toString
      -- `type(T).max` / `type(T).min`
      if let `(solExpr| $g:ident ($targs:solExpr,*)) := a then
        if g.getId.toString == "type" then
          let targs := targs.getElems
          unless targs.size == 1 do Macro.throwErrorAt a "solm: 'type' expects a type name"
          let `(solExpr| $t:ident) := targs[0]!
            | Macro.throwErrorAt a "solm: 'type' expects a type name"
          let tn := t.getId.toString
          if let some n := widthOf? tn "uint" then
            match fname with
            | "max" => return ← `(Solm.Expr.intLit (2 ^ $(natLit n) - 1))
            | "min" => return ← `(Solm.Expr.intLit 0)
            | _ => Macro.throwErrorAt f.raw "solm: expected '.max' or '.min'"
          else if let some n := widthOf? tn "int" then
            match fname with
            | "max" => return ← `(Solm.Expr.intLit (2 ^ ($(natLit n) - 1) - 1))
            | "min" => return ← `(Solm.Expr.intLit (-(2 ^ ($(natLit n) - 1))))
            | _ => Macro.throwErrorAt f.raw "solm: expected '.max' or '.min'"
          else Macro.throwErrorAt t.raw s!"solm: 'type({tn})' is not an integer type"
      if fname == "balance" then
        -- `address(this).balance` is SELFBALANCE; other bases are BALANCE.
        if isThisAddr a then mkEnvVar `selfbalance
        else `(Solm.Expr.balanceOf $(← elabExpr env a))
      else if fname == "codehash" then
        `(Solm.Expr.extCodeHash $(← elabExpr env a))
      else
        `(Solm.Expr.field $(← elabExpr env a) $(quote fname))
  | `(solExpr| $a:solExpr . $n:num) => do
      `(Solm.Expr.tupleGet $(← elabExpr env a) $(natLit n.getNat))
  | `(solExpr| $a:solExpr [ $i:solExpr ]) => do
      `(Solm.Expr.index $(← elabExpr env a) $(← elabExpr env i))
  | `(solExpr| $a:solExpr [ $i:solExpr : $j:solExpr ]) => do
      `(Solm.Expr.bytesSlice $(← elabExpr env a) $(← elabExpr env i) $(← elabExpr env j))
  | `(solExpr| ! $a) => do `(Solm.Expr.unary Solm.UnaryOp.not $(← elabExpr env a))
  | `(solExpr| ~ $a) => do `(Solm.Expr.unary Solm.UnaryOp.bitNot $(← elabExpr env a))
  | `(solExpr| - $a) => do `(Solm.Expr.unary Solm.UnaryOp.neg $(← elabExpr env a))
  | `(solExpr| $a ** $b) => mkBin env `exp a b
  | `(solExpr| $a * $b) => mkBin env `mul a b
  | `(solExpr| $a / $b) => mkBin env `div a b
  | `(solExpr| $a % $b) => mkBin env `mod a b
  | `(solExpr| $a + $b) => mkBin env `add a b
  | `(solExpr| $a - $b) => mkBin env `sub a b
  | `(solExpr| $a << $b) => mkBin env `shl a b
  | `(solExpr| $a >> $b) => mkBin env `shr a b
  | `(solExpr| $a & $b) => mkBin env `bitAnd a b
  | `(solExpr| $a ^ $b) => mkBin env `bitXor a b
  | `(solExpr| $a | $b) => mkBin env `bitOr a b
  | `(solExpr| $a < $b) => mkBin env `lt a b
  | `(solExpr| $a <= $b) => mkBin env `le a b
  | `(solExpr| $a > $b) => mkBin env `gt a b
  | `(solExpr| $a >= $b) => mkBin env `ge a b
  | `(solExpr| $a == $b) => mkBin env `eq a b
  | `(solExpr| $a != $b) => mkBin env `ne a b
  | `(solExpr| $a && $b) => mkBin env `and a b
  | `(solExpr| $a || $b) => mkBin env `or a b
  | `(solExpr| $e as $t:ident) => do
      `(Solm.Expr.inRange $(← intTypeTerm t.raw t.getId.toString) $(← elabExpr env e))
  | `(solExpr| $c ? $a : $b) => do
      `(Solm.Expr.ite $(← elabExpr env c) $(← elabExpr env a) $(← elabExpr env b))
  | _ => Macro.throwErrorAt stx "solm: unrecognized expression"

/-- Whether an expression is the current contract's address (`this` or `address(this)`). -/
private partial def isThisAddr (stx : TSyntax `solExpr) : Bool :=
  match stx with
  | `(solExpr| this) => true
  | `(solExpr| $g:ident ($args:solExpr,*)) =>
      g.getId.toString == "address" && args.getElems.size == 1 &&
        (match args.getElems[0]! with
         | `(solExpr| this) => true
         | _ => false)
  | _ => false

private partial def mkBin (env : Env) (op : Name) (a b : TSyntax `solExpr) : MacroM Term := do
  `(Solm.Expr.binary $(mkIdent (`Solm.BinaryOp ++ op)) $(← elabExpr env a) $(← elabExpr env b))

/-- Translate a call-form expression (`f(args)` with `f` possibly dotted). -/
private partial def elabCall (env : Env) (stx : Syntax) (f : LIdent)
    (args : Array (TSyntax `solExpr)) : MacroM Term := do
  let comps := f.getId.components.map (·.toString)
  let arg1 : MacroM Term := do
    unless args.size == 1 do Macro.throwErrorAt stx "solm: expected one argument"
    elabExpr env args[0]!
  match comps with
  | ["keccak256"] => `(Solm.Expr.keccak256 $(← arg1))
  | ["blockhash"] => `(Solm.Expr.blockhash $(← arg1))
  | ["extCodePrefix"] =>
      if args.size == 2 then
        `(Solm.Expr.extCodePrefix $(← elabExpr env args[0]!) $(← elabExpr env args[1]!))
      else Macro.throwErrorAt stx "solm: extCodePrefix expects (addr, len)"
  | ["tuple"] => do
      let es ← args.mapM (elabExpr env)
      `(Solm.Expr.tupleLit [$es,*])
  | ["gasleft"] =>
      Macro.throwErrorAt stx "solm: gasleft() is only allowed as `uint256 x = gasleft();`"
  | ["type"] => Macro.throwErrorAt stx "solm: 'type(T)' must be followed by '.max' or '.min'"
  | ["abi", "encodePacked"] => do
      let pairs ← args.mapM fun a => do
        match a with
        | `(solExpr| $t:ident ($inner:solExpr,*)) => do
            let tyTerm ← abiTypeTerm env t (.named t.getId.toString)
            let inner := inner.getElems
            unless inner.size == 1 do
              Macro.throwErrorAt a "solm: encodePacked argument must be 'T(e)'"
            `(($tyTerm, $(← elabExpr env inner[0]!)))
        | _ => Macro.throwErrorAt a "solm: encodePacked arguments must be type-annotated: 'T(e)'"
      `(Solm.Expr.abiEncodePacked [$pairs,*])
  | ["abi", "encodeWithSelector"] => do
      unless args.size ≥ 1 do Macro.throwErrorAt stx "solm: missing selector name"
      let fn := args[0]!
      let `(solExpr| $n:ident) := fn
        | Macro.throwErrorAt fn.raw "solm: first argument must be the function name"
      let rest ← (args.toList.drop 1).mapM (elabExpr env)
      `(Solm.Expr.abiEncodeCall $(quote n.getId.toString) [$(rest.toArray),*])
  | ["abi", "decode"] => do
      unless args.size == 2 do Macro.throwErrorAt stx "solm: abi.decode expects (bytes, (T))"
      let a1 := args[1]!
      let `(solExpr| ($t:solExpr)) := a1
        | Macro.throwErrorAt a1.raw "solm: abi.decode expects a parenthesized type"
      let `(solExpr| $tn:ident) := t
        | Macro.throwErrorAt t "solm: abi.decode expects a single type"
      `(Solm.Expr.abiDecode $(← abiTypeTerm env tn (.named tn.getId.toString))
        $(← elabExpr env args[0]!))
  | [tn] => do
      -- Fixed-bytes literal: `bytes4(0xa9059cbb)`, big-endian, left-padded to N bytes.
      if let some n := widthOf? tn "bytes" then
        if 1 ≤ n && n ≤ 32 && args.size == 1 then
          if let `(solExpr| $v:num) := args[0]! then
            let val := v.getNat
            let bytes := (List.range n).map fun i => (val >>> (8 * (n - 1 - i))) % 256
            let byteLits ← bytes.mapM fun b => `(($(natLit b) : UInt8))
            return ← `(Solm.Expr.fixedBytesLit ⟨$(natLit (n - 1)), by decide⟩
              [$(byteLits.toArray),*])
      -- Cast: `T(e)`; `address(this)` is the identity.
      if (← elemTypeTerm? tn).isSome then
        if tn == "address" && args.size == 1 then
          if let `(solExpr| this) := args[0]! then
            return ← mkEnvVar `this
        `(Solm.Expr.cast $(← arg1) $(← storageTypeTerm env stx (.named tn)))
      else if env.fns.contains tn then
        Macro.throwErrorAt stx
          s!"solm: internal call '{tn}(…)' must be bound: 'var x = {tn}(…);'"
      else
        Macro.throwErrorAt f.raw s!"solm: unknown function or type '{tn}'"
  | x :: _ =>
      if env.isLocal x || (env.storageTy? x).isSome then
        Macro.throwErrorAt stx
          s!"solm: external call must be bound: 'var r = …;'"
      else Macro.throwErrorAt f.raw s!"solm: unknown call '{".".intercalate comps}'"
  | [] => Macro.throwErrorAt f.raw "solm: empty call"

end

/-! ## Statements -/

/-- The `require(msg.value == 0)` guard solc inserts for non-payable entry points. -/
private def nonpayableGuard : MacroM Term :=
  `(Solm.Stmt.require (Solm.Expr.binary Solm.BinaryOp.eq
      (Solm.Expr.env Solm.EnvVar.callvalue) (Solm.Expr.intLit 0)))

private def isDataLocation : String → Bool
  | "memory" | "calldata" => true
  | _ => false

private def resolveRefOrThrow (env : Env) (stx : TSyntax `solExpr) : MacroM RefInfo := do
  let some (_, comps, steps) := flattenPath stx
    | Macro.throwErrorAt stx "solm: expected a variable path"
  let some r ← resolveRef env stx comps steps
    | Macro.throwErrorAt stx "solm: unknown variable in path"
  if r.isLength then Macro.throwErrorAt stx "solm: '.length' is not assignable"
  if r.exprOnly then Macro.throwErrorAt stx "solm: this path is not assignable"
  return r

/-- `a.f{value: e}(args)` / `a.f(args)`: (receiver, method, value?, view?, args). -/
private def splitMethodCall (env : Env) (stx : TSyntax `solExpr) :
    MacroM (Term × String × Option Term × Bool × Array (TSyntax `solExpr)) := do
  let (f, opts, args) ← match stx with
    | `(solExpr| $f:ident ($args:solExpr,*)) => pure (f, #[], args.getElems)
    | `(solExpr| $f:ident {$opts:solCallOpt,*} ($args:solExpr,*)) =>
        pure (f, opts.getElems, args.getElems)
    | _ => Macro.throwErrorAt stx "solm: expected a method call"
  let comps := f.getId.components.map (·.toString)
  unless comps.length ≥ 2 do
    Macro.throwErrorAt f.raw "solm: expected a dotted method call"
  let method := comps.getLast!
  let baseComps := comps.dropLast
  let recv ← do
    match ← resolveRef env f.raw baseComps [] with
    | some r =>
      match r.origin with
      | .storage => `(Solm.Expr.storage $(← refTerm r))
      | .localVar => do
          let mut e ← `(Solm.Expr.var $(quote r.base))
          for c in baseComps.tail do
            e ← `(Solm.Expr.field $e $(quote c))
          pure e
    | none =>
      -- `msg.sender.call{…}(…)`, `this.…`
      if let some v := envVarOf? baseComps then mkEnvVar v
      else if baseComps == ["this"] then mkEnvVar `this
      else Macro.throwErrorAt f.raw s!"solm: unknown receiver '{".".intercalate baseComps}'"
  let mut value : Option Term := none
  let mut view := false
  for o in opts do
    match o with
    | `(solCallOpt| $k:ident : $v:solExpr) =>
        if k.getId.toString == "value" then value := some (← elabExpr env v)
        else Macro.throwErrorAt k.raw "solm: unknown call option"
    | `(solCallOpt| $k:ident) =>
        if k.getId.toString == "view" then view := true
        else Macro.throwErrorAt k.raw "solm: unknown call option"
    | _ => Macro.throwErrorAt o "solm: malformed call option"
  return (recv, method, value, view, args)

/-- Names/aliases `finish` has beyond `start` — used to let branch-declared binders stay
    visible after the branch (spec bodies bind in both `if` arms and read afterwards). -/
private def Env.additionsFrom (start finish : Env) : List String × List (String × STy) :=
  (finish.locals.filter (fun n => !start.locals.contains n),
   finish.storage.filter (fun p => (start.storage.lookup p.1).isNone))

private def Env.withAdditions (base : Env) (adds : List (List String × List (String × STy))) : Env :=
  let ls := (adds.flatMap (·.1)).eraseDups
  let ss := adds.flatMap (·.2)
  { base with locals := ls.filter (fun n => !base.locals.contains n) ++ base.locals
              storage := ss.filter (fun p => (base.storage.lookup p.1).isNone) ++ base.storage }

mutual

/-- Translate a statement list, threading the local scope; returns the `List Stmt` term and the
    final scope. -/
private partial def elabStmts (env : Env) (stmts : List (TSyntax `solStmt)) :
    MacroM (Term × Env) := do
  match stmts with
  | [] => return (← `(([] : List Solm.Stmt)), env)
  | s :: rest =>
    match s with
    | `(solStmt| ${ $t }) => do
        let (restT, env') ← elabStmts env rest
        return (← `(($t : List Solm.Stmt) ++ $restT), env')
    | _ => do
        let (t, env') ← elabStmt env s
        let (restT, env'') ← elabStmts env' rest
        return (← `($t :: $restT), env'')

/-- `elabStmts`, keeping only the statement-list term. -/
private partial def elabStmts' (env : Env) (stmts : List (TSyntax `solStmt)) : MacroM Term := do
  return (← elabStmts env stmts).1

/-- Translate one (non-splice) statement; returns the `Stmt` term and the updated scope. -/
private partial def elabStmt (env : Env) (stx : TSyntax `solStmt) : MacroM (Term × Env) := do
  match stx with
  -- declarations -------------------------------------------------------------
  | `(solStmt| $t:solTy $x:ident = $rhs:solExpr ;) =>
      elabDecl env t none x rhs
  | `(solStmt| $t:solTy $loc:ident $x:ident = $rhs:solExpr ;) =>
      elabDecl env t (some loc) x rhs
  -- assignments --------------------------------------------------------------
  | `(solStmt| $lhs:solExpr = $rhs:solExpr ;) => elabAssign env lhs rhs none
  | `(solStmt| $lhs:solExpr += $rhs:solExpr ;) => elabAssign env lhs rhs (some `add)
  | `(solStmt| $lhs:solExpr -= $rhs:solExpr ;) => elabAssign env lhs rhs (some `sub)
  | `(solStmt| $lhs:solExpr *= $rhs:solExpr ;) => elabAssign env lhs rhs (some `mul)
  | `(solStmt| $lhs:solExpr /= $rhs:solExpr ;) => elabAssign env lhs rhs (some `div)
  -- expression statements: require / push / pop on a dotted-ident path -------
  | `(solStmt| $e:solExpr ;) => do
      let `(solExpr| $f:ident ($args:solExpr,*)) := e
        | Macro.throwErrorAt stx "solm: unsupported expression statement"
      let comps := f.getId.components.map (·.toString)
      let args := args.getElems
      if comps == ["require"] then
        let some c := args[0]? | Macro.throwErrorAt stx "solm: require expects a condition"
        -- An optional message argument is dropped, as in the AST.
        return (← `(Solm.Stmt.require $(← elabExpr env c)), env)
      else
        elabPushPop env stx comps.dropLast [] comps.getLast! args
  -- push/pop on a path with postfix steps: `bids[a].push(x);` ----------------
  | `(solStmt| $callee:solExpr ($args:solExpr,*) ;) => do
      let some (_, comps, steps) := flattenPath callee
        | Macro.throwErrorAt stx "solm: unsupported statement"
      let some (.field m) := steps.getLast?
        | Macro.throwErrorAt stx "solm: unsupported statement"
      elabPushPop env stx comps steps.dropLast m args.getElems
  -- tuple-binding low-level calls --------------------------------------------
  | `(solStmt| ($binds:solBind,*) = $rhs:solExpr ;) => do
      let names ← binds.getElems.mapM fun b => do
        match b with
        | `(solBind| $_:solTy $x:ident) => pure x.getId.toString
        | `(solBind| $_:solTy $_:ident $x:ident) => pure x.getId.toString
        | _ => Macro.throwErrorAt b "solm: malformed binder"
      unless names.size == 2 do Macro.throwErrorAt stx "solm: expected two binders"
      let ok := names[0]!
      let dat := names[1]!
      let (target, method, valueOpt, _, callArgs) ← splitMethodCall env rhs
      let env' := { env with locals := dat :: ok :: env.locals }
      unless callArgs.size == 1 do
        Macro.throwErrorAt rhs "solm: low-level call expects one bytes argument"
      let payload ← elabExpr env callArgs[0]!
      match method with
      | "call" =>
          let eth := valueOpt.getD (← `(Solm.Expr.intLit 0))
          return (← `(Solm.Stmt.lowLevelCall $target $eth $payload $(quote ok) $(quote dat)), env')
      | "staticcall" =>
          let eth := valueOpt.getD (← `(Solm.Expr.intLit 0))
          return (← `(Solm.Stmt.lowLevelCall $target $eth $payload $(quote ok) $(quote dat)
            (perm := false)), env')
      | "delegatecall" =>
          return (← `(Solm.Stmt.delegateCall $target $payload $(quote ok) $(quote dat)), env')
      | m => Macro.throwErrorAt rhs s!"solm: unknown low-level call '{m}'"
  -- control flow -------------------------------------------------------------
  -- Branch-declared binders stay visible after the branch: spec bodies bind a name in both
  -- `if` arms (or in a loop body) and keep using it afterwards.
  | `(solStmt| if ($c:solExpr) { $thn:solStmt* }) => do
      let (thnT, thnEnv) ← elabStmts env thn.toList
      let t ← `(Solm.Stmt.ite $(← elabExpr env c) $thnT [])
      return (t, env.withAdditions [Env.additionsFrom env thnEnv])
  | `(solStmt| if ($c:solExpr) { $thn:solStmt* } else { $els:solStmt* }) => do
      let (thnT, thnEnv) ← elabStmts env thn.toList
      let (elsT, elsEnv) ← elabStmts env els.toList
      let t ← `(Solm.Stmt.ite $(← elabExpr env c) $thnT $elsT)
      return (t, env.withAdditions [Env.additionsFrom env thnEnv, Env.additionsFrom env elsEnv])
  | `(solStmt| if ($c:solExpr) { $thn:solStmt* } else $e:solStmt) => do
      let (thnT, thnEnv) ← elabStmts env thn.toList
      let (et, elsEnv) ← elabStmt env e
      let t ← `(Solm.Stmt.ite $(← elabExpr env c) $thnT [$et])
      return (t, env.withAdditions [Env.additionsFrom env thnEnv, Env.additionsFrom env elsEnv])
  | `(solStmt| while ($c:solExpr) { $body:solStmt* }) => do
      let (bodyT, bodyEnv) ← elabStmts env body.toList
      let t ← `(Solm.Stmt.while $(← elabExpr env c) $bodyT)
      return (t, env.withAdditions [Env.additionsFrom env bodyEnv])
  | `(solStmt| for ($init:solStmt $c:solExpr; $post:solForPost) { $body:solStmt* }) => do
      let (initT, env') ← elabStmt env init
      let postT ← elabForPost env' post
      let (bodyT, bodyEnv) ← elabStmts env' body.toList
      let t ← `(Solm.Stmt.for [$initT] $(← elabExpr env' c) [$postT] $bodyT)
      return (t, env.withAdditions [Env.additionsFrom env bodyEnv])
  | `(solStmt| return $es:solExpr,* ;) => do
      let ts ← es.getElems.mapM (elabExpr env)
      return (← `(Solm.Stmt.return [$ts,*]), env)
  | `(solStmt| return ($e0:solExpr, $es:solExpr,*) ;) => do
      let ts ← (#[e0] ++ es.getElems).mapM (elabExpr env)
      return (← `(Solm.Stmt.return [$ts,*]), env)
  | `(solStmt| break ;) => return (← `(Solm.Stmt.break), env)
  | `(solStmt| continue ;) => return (← `(Solm.Stmt.continue), env)
  | `(solStmt| delete $p:solExpr ;) => do
      let r ← resolveRefOrThrow env p
      unless r.origin matches .storage do
        Macro.throwErrorAt p "solm: delete expects a storage path"
      return (← `(Solm.Stmt.delete $(← refTerm r)), env)
  | `(solStmt| try $call:solExpr $rkw:ident ($ret:ident) { $onOk:solStmt* }
        catch ($err:ident) { $onErr:solStmt* }) => do
      unless rkw.getId.toString == "returns" do
        Macro.throwErrorAt rkw.raw "solm: expected 'returns'"
      let (target, method, valueOpt, _, callArgs) ← splitMethodCall env call
      let eth := valueOpt.getD (← `(Solm.Expr.intLit 0))
      let argTs ← callArgs.mapM (elabExpr env)
      let envOk := { env with locals := ret.getId.toString :: env.locals }
      let envErr := { env with locals := err.getId.toString :: env.locals }
      let (okT, okEnv) ← elabStmts envOk onOk.toList
      let (errT, errEnv) ← elabStmts envErr onErr.toList
      let t ← `(Solm.Stmt.checkedCall $target $(quote method) $eth [$argTs,*]
        $(quote ret.getId.toString) $okT $(quote err.getId.toString) $errT)
      return (t, env.withAdditions
        [Env.additionsFrom envOk okEnv, Env.additionsFrom envErr errEnv])
  | _ => Macro.throwErrorAt stx "solm: unrecognized statement"

private partial def elabPushPop (env : Env) (stx : Syntax) (comps : List String)
    (steps : List PStep) (method : String) (args : Array (TSyntax `solExpr)) :
    MacroM (Term × Env) := do
  let resolve : MacroM RefInfo := do
    let some r ← resolveRef env stx comps steps
      | Macro.throwErrorAt stx "solm: unknown push/pop target"
    unless r.origin matches .storage do
      Macro.throwErrorAt stx "solm: push/pop target must be a storage array"
    pure r
  match method with
  | "push" => do
      let r ← resolve
      match args with
      | #[] => return (← `(Solm.Stmt.push $(← refTerm r) none), env)
      | #[v] => return (← `(Solm.Stmt.push $(← refTerm r) (some $(← elabExpr env v))), env)
      | _ => Macro.throwErrorAt stx "solm: push expects at most one argument"
  | "pop" => do
      unless args.isEmpty do Macro.throwErrorAt stx "solm: pop expects no arguments"
      let r ← resolve
      return (← `(Solm.Stmt.pop $(← refTerm r)), env)
  | _ =>
      Macro.throwErrorAt stx "solm: only require(…), ….push(…), and ….pop() can stand alone as statements"

/-- Declarations: dispatch on the right-hand side (calls, gasleft) and location marker. -/
private partial def elabDecl (env : Env) (t : TSyntax `solTy)
    (loc : Option LIdent) (x : LIdent) (rhs : TSyntax `solExpr) : MacroM (Term × Env) := do
  let name := x.getId.toString
  let env' := { env with locals := name :: env.locals }
  -- `T storage x = path;` — the alias behaves like a storage variable of the remaining type.
  if let some l := loc then
    let ls := l.getId.toString
    if ls == "storage" then
      let r ← resolveRefOrThrow env rhs
      unless r.origin matches .storage do
        Macro.throwErrorAt rhs "solm: storage alias must reference storage"
      let some aliasTy := r.ty
        | Macro.throwErrorAt rhs "solm: cannot type the storage alias"
      let envA := { env with
        storage := (name, aliasTy) :: env.storage
        locals := env.locals.filter (· != name) }
      return (← `(Solm.Stmt.letStorage $(quote name) $(← refTerm r)), envA)
    else unless isDataLocation ls do
      Macro.throwErrorAt l.raw s!"solm: unknown data location '{ls}'"
  -- Call-shaped right-hand sides.
  match rhs with
  | `(solExpr| $f:ident ($args:solExpr,*)) =>
      let comps := f.getId.components.map (·.toString)
      let args := args.getElems
      if comps == ["gasleft"] && args.isEmpty then
        return (← `(Solm.Stmt.letGas $(quote name)), env')
      if comps.length == 1 && env.fns.contains comps.head! then
        let ts ← args.mapM (elabExpr env)
        return (← `(Solm.Stmt.internalCall $(quote comps.head!) [$ts,*] $(quote name)), env')
      if comps.length ≥ 2 then
        if (← resolveRef env f.raw comps.dropLast []).isSome then
          let (recv, method, valueOpt, view, callArgs) ← splitMethodCall env rhs
          let eth := valueOpt.getD (← `(Solm.Expr.intLit 0))
          let ts ← callArgs.mapM (elabExpr env)
          if view then
            return (← `(Solm.Stmt.externalCall $recv $(quote method) $eth [$ts,*] $(quote name)
              (perm := false)), env')
          else
            return (← `(Solm.Stmt.externalCall $recv $(quote method) $eth [$ts,*]
              $(quote name)), env')
      pure ()
  | `(solExpr| $_:ident {$_:solCallOpt,*} ($_:solExpr,*)) =>
      let (recv, method, valueOpt, view, callArgs) ← splitMethodCall env rhs
      let eth := valueOpt.getD (← `(Solm.Expr.intLit 0))
      let ts ← callArgs.mapM (elabExpr env)
      if view then
        return (← `(Solm.Stmt.externalCall $recv $(quote method) $eth [$ts,*] $(quote name)
          (perm := false)), env')
      else
        return (← `(Solm.Stmt.externalCall $recv $(quote method) $eth [$ts,*]
          $(quote name)), env')
  | _ => pure ()
  -- Plain let declaration.
  let tySTy ← parseTy t
  let e ← elabExpr env rhs
  if tySTy == .named "var" then
    return (← `(Solm.Stmt.letDecl $(quote name) none $e), env')
  else
    return (← `(Solm.Stmt.letDecl $(quote name) (some $(← abiTypeTerm env t tySTy)) $e), env')

private partial def elabAssign (env : Env) (lhs rhs : TSyntax `solExpr) (op : Option Name) :
    MacroM (Term × Env) := do
  let r ← resolveRefOrThrow env lhs
  let rhsT ← match op with
    | none => elabExpr env rhs
    | some o => do
        `(Solm.Expr.binary $(mkIdent (`Solm.BinaryOp ++ o)) $(← elabExpr env lhs)
          $(← elabExpr env rhs))
  return (← `(Solm.Stmt.assign $(← originTerm r.origin) $(← refTerm r) $rhsT), env)

private partial def elabForPost (env : Env) (stx : TSyntax `solForPost) : MacroM Term := do
  match stx with
  | `(solForPost| $lhs:solExpr = $rhs:solExpr) => do
      let (t, _) ← elabAssign env lhs rhs none
      pure t
  | `(solForPost| $lhs:solExpr += $rhs:solExpr) => do
      let (t, _) ← elabAssign env lhs rhs (some `add)
      pure t
  | `(solForPost| $lhs:solExpr ++) => do
      let one ← `(solExpr| 1)
      let (t, _) ← elabAssign env lhs one (some `add)
      pure t
  | _ => Macro.throwErrorAt stx "solm: unrecognized loop update"

end

/-! ## Declarations and the contract macro -/

private def parseParam (env : Env) (stx : TSyntax `solParam) : MacroM (String × Term) := do
  match stx with
  | `(solParam| $t:solTy $x:ident) => do
      pure (x.getId.toString, ← abiTypeTerm env t (← parseTy t))
  | `(solParam| $t:solTy $l:ident $x:ident) => do
      unless isDataLocation l.getId.toString do
        Macro.throwErrorAt l.raw s!"solm: unknown data location '{l.getId.toString}'"
      pure (x.getId.toString, ← abiTypeTerm env t (← parseTy t))
  | _ => Macro.throwErrorAt stx "solm: malformed parameter"

private def paramTerm (p : String × Term) : MacroM Term := do
  `(({ name := $(quote p.1), ty := $(p.2) } : Solm.Param))

private structure FnInfo where
  name : String
  params : Array (String × Term)
  returns : Array Term
  bodyStx : Array (TSyntax `solStmt)
  /-- external/public ⇒ transition, internal/private ⇒ function -/
  isTransition : Bool
  payable : Bool
  kind : String  -- "function" | "constructor" | "receive" | "fallback"

private def fnBodyTerm (env : Env) (fn : FnInfo) : MacroM Term := do
  let env := { env with locals := fn.params.toList.map (·.1) ++ env.locals }
  let body ← elabStmts' env fn.bodyStx.toList
  -- Non-payable entry points get solc's callvalue guard; internal functions and receive don't.
  let needsGuard :=
    !fn.payable && (fn.kind == "constructor" || fn.kind == "fallback" ||
      (fn.kind == "function" && fn.isTransition))
  if needsGuard then `($(← nonpayableGuard) :: $body) else pure body

private def transitionTerm (env : Env) (fn : FnInfo) : MacroM Term := do
  let ps ← fn.params.mapM paramTerm
  `(({ name := $(quote fn.name), params := [$ps,*], returnType := [$(fn.returns),*],
       body := $(← fnBodyTerm env fn) } : Solm.TransitionDecl))

private def functionTerm (env : Env) (fn : FnInfo) : MacroM Term := do
  let ps ← fn.params.mapM paramTerm
  `(({ name := $(quote fn.name), params := [$ps,*], returnType := [$(fn.returns),*],
       body := $(← fnBodyTerm env fn) } : Solm.FunctionDecl))

private def ctorTerm (env : Env) (fn : FnInfo) : MacroM Term := do
  let ps ← fn.params.mapM paramTerm
  `(({ params := [$ps,*], body := $(← fnBodyTerm env fn) } : Solm.ConstructorDecl))

/-- Modifier lists: (isTransition, payable); unknown markers are errors. -/
private def checkModifiers (mods : Array LIdent) : MacroM (Bool × Bool) := do
  let mut isTransition := true
  let mut payable := false
  for m in mods do
    match m.getId.toString with
    | "external" | "public" => isTransition := true
    | "internal" | "private" => isTransition := false
    | "payable" => payable := true
    | "view" | "pure" | "override" | "virtual" | "returns" => pure ()
    | s => Macro.throwErrorAt m.raw s!"solm: unknown modifier '{s}'"
  return (isTransition, payable)

private def sepElems (n : Syntax) : Array Syntax :=
  (n.getArgs.mapIdx fun i s => if i % 2 == 0 then some s else none).filterMap id

/-- Destructure a `solItemFnRets` node (quotation patterns cannot disambiguate the two
    fn-item productions): (fkw, f, params, mods, rets, body). -/
private def destructFnRets (item : TSyntax `solItem) :
    Option (LIdent × LIdent × Array (TSyntax `solParam) × Array LIdent ×
      Array (TSyntax `solTy) × Array (TSyntax `solStmt)) :=
  let n := item.raw
  if n.isOfKind ``solItemFnRets then
    some (⟨n[0]⟩, ⟨n[1]⟩,
      (sepElems n[3]).map (⟨·⟩),
      n[5].getArgs.map (⟨·⟩),
      (sepElems n[7]).map (⟨·⟩),
      n[10].getArgs.map (⟨·⟩))
  else none

/-- Destructure a `solItemCtorRets` node (fallback with a returns clause):
    (kw, params, mods, rets, body). -/
private def destructCtorRets (item : TSyntax `solItem) :
    Option (LIdent × Array (TSyntax `solParam) × Array LIdent ×
      Array (TSyntax `solTy) × Array (TSyntax `solStmt)) :=
  let n := item.raw
  if n.isOfKind ``solItemCtorRets then
    some (⟨n[0]⟩,
      (sepElems n[2]).map (⟨·⟩),
      n[4].getArgs.map (⟨·⟩),
      (sepElems n[6]).map (⟨·⟩),
      n[9].getArgs.map (⟨·⟩))
  else none

private def mkFnInfo (env : Env) (f : LIdent) (params : Array (TSyntax `solParam))
    (mods : Array LIdent) (rets : Array (TSyntax `solTy)) (body : Array (TSyntax `solStmt)) :
    MacroM (FnInfo × Bool) := do
  let ps ← params.mapM (parseParam env)
  let (isTransition, payable) ← checkModifiers mods
  let retTerms ← rets.mapM fun t => do abiTypeTerm env t (← parseTy t)
  let fn : FnInfo :=
    { name := f.getId.toString
      params := ps
      returns := retTerms
      bodyStx := body
      isTransition := isTransition
      payable := payable
      kind := "function" }
  return (fn, isTransition)

macro_rules
  | `(solidity% $kw:ident $name:ident { $items:solItem* }) => do
    unless kw.getId.toString == "contract" do
      Macro.throwErrorAt kw.raw "solm: expected 'contract'"
    -- Pass 1: collect declared names.
    let mut storage : List (String × STy) := []
    let mut structs : List (String × List (String × STy)) := []
    let mut fnNames : List String := []
    for item in items do
      match item with
      | `(solItem| $t:solTy $x:ident ;) =>
          storage := storage ++ [(x.getId.toString, ← parseTy t)]
      | `(solItem| $t:solTy $_:ident $x:ident ;) =>
          storage := storage ++ [(x.getId.toString, ← parseTy t)]
      | `(solItem| $skw:ident $s:ident { $members:solStructMember* }) => do
          unless skw.getId.toString == "struct" do
            Macro.throwErrorAt skw.raw "solm: expected 'struct'"
          let fields ← members.mapM fun m => do
            match m with
            | `(solStructMember| $t:solTy $f:ident ;) => do
                pure (f.getId.toString, ← parseTy t)
            | _ => Macro.throwErrorAt m "solm: malformed struct member"
          structs := structs ++ [(s.getId.toString, fields.toList)]
      -- Any declared function (any visibility) is a valid bare-call target: solc dispatches
      -- internal calls to public functions too, and specs model those as `internalCall`.
      | `(solItem| $fkw:ident $f:ident ($_:solParam,*) $_:ident* { $_:solStmt* }) => do
          if fkw.getId.toString == "function" then
            fnNames := fnNames ++ [f.getId.toString]
      | _ =>
          if let some (fkw, f, _, _, _, _) := destructFnRets item then
            if fkw.getId.toString == "function" then
              fnNames := fnNames ++ [f.getId.toString]
    let env : Env := { storage := storage, structs := structs, fns := fnNames }
    -- Pass 2: translate items.
    let mut storageTerms : Array Term := #[]
    let mut structTerms : Array Term := #[]
    let mut fnTerms : Array Term := #[]
    let mut transitionTerms : Array Term := #[]
    let mut ctor? : Option Term := none
    let mut receive? : Option Term := none
    let mut fallback? : Option Term := none
    for item in items do
      match item with
      | `(solItem| $t:solTy $x:ident ;) => do
          let ty ← storageTypeTerm env t (← parseTy t)
          storageTerms := storageTerms.push
            (← `(({ name := $(quote x.getId.toString), ty := $ty } : Solm.StorageDecl)))
      | `(solItem| $t:solTy $_:ident $x:ident ;) => do
          let ty ← storageTypeTerm env t (← parseTy t)
          storageTerms := storageTerms.push
            (← `(({ name := $(quote x.getId.toString), ty := $ty } : Solm.StorageDecl)))
      | `(solItem| $_:ident $s:ident { $members:solStructMember* }) => do
          let fieldTerms ← members.mapM fun m => do
            match m with
            | `(solStructMember| $t:solTy $f:ident ;) => do
                let ty ← storageTypeTerm env t (← parseTy t)
                `(({ name := $(quote f.getId.toString), ty := $ty } : Solm.StorageDecl))
            | _ => Macro.throwErrorAt m "solm: malformed struct member"
          structTerms := structTerms.push
            (← `(({ name := $(quote s.getId.toString), fields := [$fieldTerms,*] } : Solm.StructDecl)))
      | `(solItem| $fkw:ident ($params:solParam,*) $mods:ident* { $body:solStmt* }) => do
          let ps ← params.getElems.mapM (parseParam env)
          let (_, payable) ← checkModifiers mods
          let kind := fkw.getId.toString
          let fn : FnInfo :=
            { name := kind
              params := ps
              returns := #[]
              bodyStx := body
              isTransition := true
              payable := payable
              kind := kind }
          match kind with
          | "constructor" => ctor? := some (← ctorTerm env fn)
          | "receive" => receive? := some (← transitionTerm env { fn with payable := true })
          | "fallback" => fallback? := some (← transitionTerm env fn)
          | s => Macro.throwErrorAt fkw.raw s!"solm: unknown declaration '{s}'"
      | `(solItem| $fkw:ident $f:ident ($params:solParam,*) $mods:ident* { $body:solStmt* }) => do
          unless fkw.getId.toString == "function" do
            Macro.throwErrorAt fkw.raw "solm: expected 'function'"
          let (fn, isTransition) ← mkFnInfo env f params.getElems mods #[] body
          if isTransition then
            transitionTerms := transitionTerms.push (← transitionTerm env fn)
          else
            fnTerms := fnTerms.push (← functionTerm env fn)
      | `(solItem| ${ $t }) =>
          transitionTerms := transitionTerms.push (← `(($t : Solm.TransitionDecl)))
      | _ =>
          if let some (kw, params, mods, rets, body) := destructCtorRets item then
            let ps ← params.mapM (parseParam env)
            let (_, payable) ← checkModifiers mods
            unless mods.any (·.getId.toString == "returns") do
              Macro.throwErrorAt item "solm: return types need the 'returns' keyword"
            let retTerms ← rets.mapM fun t => do abiTypeTerm env t (← parseTy t)
            let kind := kw.getId.toString
            let fn : FnInfo :=
              { name := kind
                params := ps
                returns := retTerms
                bodyStx := body
                isTransition := true
                payable := payable
                kind := kind }
            match kind with
            | "receive" => receive? := some (← transitionTerm env { fn with payable := true })
            | "fallback" => fallback? := some (← transitionTerm env fn)
            | s => Macro.throwErrorAt kw.raw s!"solm: '{s}' cannot declare return types"
          else if let some (fkw, f, params, mods, rets, body) := destructFnRets item then
            unless fkw.getId.toString == "function" do
              Macro.throwErrorAt fkw.raw "solm: expected 'function'"
            unless mods.any (·.getId.toString == "returns") do
              Macro.throwErrorAt item "solm: return types need the 'returns' keyword"
            let (fn, isTransition) ← mkFnInfo env f params mods rets body
            if isTransition then
              transitionTerms := transitionTerms.push (← transitionTerm env fn)
            else
              fnTerms := fnTerms.push (← functionTerm env fn)
          else
            Macro.throwErrorAt item "solm: unrecognized contract item"
    let ctorT ← match ctor? with
      | some t => pure t
      | none => do
          -- Solidity's implicit constructor: non-payable, empty body.
          `(({ params := [], body := [$(← nonpayableGuard)] } : Solm.ConstructorDecl))
    let recvT ← match receive? with
      | some t => `(some $t) | none => `((none : Option Solm.TransitionDecl))
    let fbT ← match fallback? with
      | some t => `(some $t) | none => `((none : Option Solm.TransitionDecl))
    `(({ name := $(quote name.getId.toString),
         storage := [$storageTerms,*],
         ctor := $ctorT,
         structs := [$structTerms,*],
         functions := [$fnTerms,*],
         transitions := [$transitionTerms,*],
         receive := $recvT,
         fallback := $fbT } : Solm.ContractDecl))

end Solm.Notation
