import Solm.Syntax

/-!
# Solm — a macro-generated surface syntax

A lightweight, Lean-embedded DSL that desugars to the `Solm` AST (`Expr`, `Stmt`,
`StorageRef`, the `*Decl` structures).  The goal is to let a spec author write something that
*reads* like the Solidity it models, instead of hand-constructing constructor trees.

Everything here is pure `syntax` + `macro_rules` sugar: each surface form expands to the exact
AST constructors, so a spec written with this frontend is **definitionally equal** to the
hand-written one (checked by `rfl` in `Examples/ERC20/SpecSugar.lean`).

## Design notes / deliberate choices

* **No common English words become global keyword tokens.**  `storage`, `mapping`, `value`,
  `function`, `field` are all constructor / field names elsewhere in the project, and reserving
  any of them would break existing `.storage` / `.mapping` projections.  So:
  * storage references use a `@` sigil:        `@balanceOf[msg.sender]`
  * mapping *types* use bare arrows:           `(address => uint256)`
  * declaration keywords are `solm_`-prefixed: `solm_transition`, `solm_constructor`
  * the `uintN` range-cast (`Expr.inRange`) reuses the existing `as` token: `(a + b) as uint256`
* **Storage vs. local is explicit** (`@x` vs `x`) rather than name-resolved, matching the
  "sugar over the AST" remit — solc resolves the origin statically, and a future elaborator with a
  declared-name environment could do the same and drop the sigil.
* **`[k]` indexing desugars to `.mindex`** (mapping key).  Array indexing (`.aindex`) and struct
  field steps are reachable via the `@a.(i)` / `@s.f` forms below.  ERC20 only uses mappings.
-/

open Lean

namespace Solm.Notation
open Solm ABI

/-! ## Type-name parsing (macro-time)

Type names like `uint256` stay ordinary identifiers (so they are never reserved tokens); the
trailing width is parsed at macro-expansion time. -/

/-- `widthOf? "uint256" "uint" = some 256`. -/
private def widthOf? (s pfx : String) : Option Nat :=
  if s.startsWith pfx then (s.drop pfx.length).toNat? else none

/-- An `ABI.ElemType` from a scalar type name (`address`, `bool`, `uintN`, `intN`). -/
private def elemTypeStx (id : Syntax) : MacroM (TSyntax `term) := do
  let s := id.getId.toString
  if s == "address" then `(ABI.ElemType.address)
  else if s == "bool" then `(ABI.ElemType.bool)
  else match widthOf? s "uint" with
    | some n => `(ABI.ElemType.int (ABI.IntType.uint ⟨$(Syntax.mkNumLit (toString n)), by decide⟩))
    | none => match widthOf? s "int" with
      | some n => `(ABI.ElemType.int (ABI.IntType.sint ⟨$(Syntax.mkNumLit (toString n)), by decide⟩))
      | none => Macro.throwErrorAt id s!"solm: unknown scalar type '{s}'"

/-- An `ABI.ABIType` from a scalar type name. -/
private def abiTypeStx (id : Syntax) : MacroM (TSyntax `term) := do
  `(ABI.ABIType.elem $(← elemTypeStx id))

/-- An `ABI.IntType` from an integer type name — used by the `as uintN` range-cast. -/
private def intTypeStx (id : Syntax) : MacroM (TSyntax `term) := do
  let s := id.getId.toString
  match widthOf? s "uint" with
  | some n => `(ABI.IntType.uint ⟨$(Syntax.mkNumLit (toString n)), by decide⟩)
  | none => match widthOf? s "int" with
    | some n => `(ABI.IntType.sint ⟨$(Syntax.mkNumLit (toString n)), by decide⟩)
    | none => Macro.throwErrorAt id s!"solm: '{s}' is not an integer type"

/-! ## Expressions

`solmExpr` and `solmRef` are mutually recursive (`@balanceOf[expr]`), so both categories are
declared before either's productions. -/

declare_syntax_cat solmExpr
declare_syntax_cat solmRef

-- `true`/`false`/`msg.sender`/… are ordinary (dotted) identifiers in Lean — reserving them as
-- syntax atoms would globally break bare `true`/`false`, so they all flow through `ident` and are
-- recognised by name in the macro below.
syntax:max num                                  : solmExpr
syntax:max ident                                : solmExpr   -- var, bool lit, or env keyword
syntax:max "(" solmExpr ")"                     : solmExpr

-- arithmetic
syntax:70 solmExpr:70 " * " solmExpr:71         : solmExpr
syntax:70 solmExpr:70 " / " solmExpr:71         : solmExpr
syntax:70 solmExpr:70 " % " solmExpr:71         : solmExpr
syntax:65 solmExpr:65 " + " solmExpr:66         : solmExpr
syntax:65 solmExpr:65 " - " solmExpr:66         : solmExpr
-- comparison
syntax:50 solmExpr:51 " == " solmExpr:51        : solmExpr
syntax:50 solmExpr:51 " != " solmExpr:51        : solmExpr
syntax:50 solmExpr:51 " < "  solmExpr:51        : solmExpr
syntax:50 solmExpr:51 " <= " solmExpr:51        : solmExpr
syntax:50 solmExpr:51 " > "  solmExpr:51        : solmExpr
syntax:50 solmExpr:51 " >= " solmExpr:51        : solmExpr
-- boolean
syntax:35 solmExpr:36 " && " solmExpr:35        : solmExpr
syntax:30 solmExpr:31 " || " solmExpr:30        : solmExpr
syntax:40 "!" solmExpr:41                       : solmExpr
-- `uintN(e)` range-cast, written `e as uintN`
syntax:45 solmExpr:45 " as " ident              : solmExpr
-- storage read
syntax:max "@" solmRef                          : solmExpr

-- Storage / local reference path: `balanceOf[k]`, `allowance[a][b]`, `s.field`, `arr.(i)`.
syntax:max ident                                : solmRef
syntax:max solmRef "[" solmExpr "]"             : solmRef   -- mapping key  → .mindex
syntax:max solmRef ".(" solmExpr ")"            : solmRef   -- array index  → .aindex
syntax:max solmRef "." ident                    : solmRef   -- struct field → .field

/-- Entry term macro: a `solmExpr` to a `Solm.Expr`. -/
syntax:max "sExpr% " solmExpr                   : term
/-- Entry term macro: a `solmRef` to a `Solm.StorageRef`. -/
syntax:max "sRef% " solmRef                     : term

macro_rules
  | `(sRef% $x:ident) =>
      `(({ base := $(quote x.getId.toString), steps := [] } : Solm.StorageRef))
  | `(sRef% $r:solmRef [ $k:solmExpr ]) =>
      `(let r0 := sRef% $r
        { r0 with steps := r0.steps ++ [Solm.StorageRefStep.mindex (sExpr% $k)] })
  | `(sRef% $r:solmRef .( $i:solmExpr )) =>
      `(let r0 := sRef% $r
        { r0 with steps := r0.steps ++ [Solm.StorageRefStep.aindex (sExpr% $i)] })
  | `(sRef% $r:solmRef . $f:ident) =>
      `(let r0 := sRef% $r
        { r0 with steps := r0.steps ++ [Solm.StorageRefStep.field $(quote f.getId.toString)] })

macro_rules
  | `(sExpr% $n:num)            => `(Solm.Expr.intLit $n)
  | `(sExpr% $x:ident)         =>
      match x.getId.toString with
      | "true"            => `(Solm.Expr.boolLit true)
      | "false"           => `(Solm.Expr.boolLit false)
      | "msg.sender"      => `(Solm.Expr.env Solm.EnvVar.caller)
      | "msg.value"       => `(Solm.Expr.env Solm.EnvVar.callvalue)
      | "tx.origin"       => `(Solm.Expr.env Solm.EnvVar.origin)
      | "block.timestamp" => `(Solm.Expr.env Solm.EnvVar.timestamp)
      | "block.chainid"   => `(Solm.Expr.env Solm.EnvVar.chainid)
      | s                 => `(Solm.Expr.var $(quote s))
  | `(sExpr% ( $e:solmExpr ))  => `(sExpr% $e)
  | `(sExpr% @ $r:solmRef)     => `(Solm.Expr.storage (sRef% $r))
  | `(sExpr% $a * $b)  => `(Solm.Expr.binary Solm.BinaryOp.mul (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a / $b)  => `(Solm.Expr.binary Solm.BinaryOp.div (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a % $b)  => `(Solm.Expr.binary Solm.BinaryOp.mod (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a + $b)  => `(Solm.Expr.binary Solm.BinaryOp.add (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a - $b)  => `(Solm.Expr.binary Solm.BinaryOp.sub (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a == $b) => `(Solm.Expr.binary Solm.BinaryOp.eq (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a != $b) => `(Solm.Expr.binary Solm.BinaryOp.ne (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a < $b)  => `(Solm.Expr.binary Solm.BinaryOp.lt (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a <= $b) => `(Solm.Expr.binary Solm.BinaryOp.le (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a > $b)  => `(Solm.Expr.binary Solm.BinaryOp.gt (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a >= $b) => `(Solm.Expr.binary Solm.BinaryOp.ge (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a && $b) => `(Solm.Expr.binary Solm.BinaryOp.and (sExpr% $a) (sExpr% $b))
  | `(sExpr% $a || $b) => `(Solm.Expr.binary Solm.BinaryOp.or (sExpr% $a) (sExpr% $b))
  | `(sExpr% ! $a)     => `(Solm.Expr.unary Solm.UnaryOp.not (sExpr% $a))
  | `(sExpr% $e as $t:ident) => do `(Solm.Expr.inRange $(← intTypeStx t) (sExpr% $e))

/-! ## Statements -/

declare_syntax_cat solmStmt

syntax "require " solmExpr                               : solmStmt
syntax "let " ident " : " ident " := " solmExpr         : solmStmt
syntax "let " ident " := " solmExpr                     : solmStmt
syntax "@" solmRef " := " solmExpr                       : solmStmt   -- storage assign
syntax ident " := " solmExpr                             : solmStmt   -- local assign
syntax "return " solmExpr,*                              : solmStmt   -- 0+ comma-separated values
syntax "break"                                           : solmStmt
syntax "continue"                                        : solmStmt
syntax "delete " "@" solmRef                             : solmStmt

/-- A single `solmStmt` to a `Solm.Stmt`. -/
syntax "sStmt% " solmStmt : term
/-- A brace-delimited block of statements to a `List Solm.Stmt`. -/
syntax "sBlock% " "{" solmStmt* "}" : term

macro_rules
  | `(sStmt% require $e)            => `(Solm.Stmt.require (sExpr% $e))
  | `(sStmt% let $x:ident : $t:ident := $e) => do
      `(Solm.Stmt.letDecl $(quote x.getId.toString) (some $(← abiTypeStx t)) (sExpr% $e))
  | `(sStmt% let $x:ident := $e) =>
      `(Solm.Stmt.letDecl $(quote x.getId.toString) none (sExpr% $e))
  | `(sStmt% @ $r:solmRef := $e) =>
      `(Solm.Stmt.assign Solm.VarOrigin.storage (sRef% $r) (sExpr% $e))
  | `(sStmt% $x:ident := $e) =>
      `(Solm.Stmt.assign Solm.VarOrigin.localVar
          { base := $(quote x.getId.toString), steps := [] } (sExpr% $e))
  | `(sStmt% return $es,*)         => do
      let elems ← es.getElems.mapM fun e => `(sExpr% $e)
      `(Solm.Stmt.return [$elems,*])
  | `(sStmt% break)                => `(Solm.Stmt.break)
  | `(sStmt% continue)             => `(Solm.Stmt.continue)
  | `(sStmt% delete @ $r:solmRef)  => `(Solm.Stmt.delete (sRef% $r))

macro_rules
  | `(sBlock% { $stmts:solmStmt* }) => `([ $[sStmt% $stmts],* ])

/-! ## Declarations -/

/-- A parameter `(name : type)`. -/
declare_syntax_cat solmParam
syntax "(" ident " : " ident ")" : solmParam
syntax "sParam% " solmParam : term
macro_rules
  | `(sParam% ( $x:ident : $t:ident )) => do
      `(({ name := $(quote x.getId.toString), ty := $(← abiTypeStx t) } : Solm.Param))

/-- A storage variable declaration `type name`, e.g. `(address => uint256) balanceOf`. -/
declare_syntax_cat solmStTy
syntax:max ident                         : solmStTy
syntax:max "(" ident " => " solmStTy ")" : solmStTy   -- mapping(key => value)
syntax "sStTy% " solmStTy : term
macro_rules
  | `(sStTy% $x:ident) => do `(Solm.StorageType.elem $(← elemTypeStx x))
  | `(sStTy% ( $k:ident => $v:solmStTy )) => do
      `(Solm.StorageType.mapping $(← elemTypeStx k) (sStTy% $v))

declare_syntax_cat solmStDecl
syntax solmStTy ident : solmStDecl
/-- A storage-section block `{ type₁ name₁  type₂ name₂  … }` to a `List Solm.StorageDecl`. -/
syntax "sState% " "{" solmStDecl* "}" : term
macro_rules
  | `(sState% { $[$tys:solmStTy $names:ident]* }) =>
      `([ $[({ name := $(names.map (quote ·.getId.toString)), ty := sStTy% $tys } : Solm.StorageDecl)],* ])

/-- `solm_constructor (params) { body }` to a `Solm.ConstructorDecl`. -/
syntax "solm_constructor " solmParam* "{" solmStmt* "}" : term
macro_rules
  | `(solm_constructor $ps:solmParam* { $body:solmStmt* }) =>
      `(({ params := [ $[sParam% $ps],* ], body := sBlock% { $body* } } : Solm.ConstructorDecl))

/-- `solm_transition name (params) -> ret { body }` to a `Solm.TransitionDecl`.
    The `-> ret` return clause is optional. -/
syntax "solm_transition " ident solmParam* (" -> " ident)? "{" solmStmt* "}" : term
macro_rules
  | `(solm_transition $nm:ident $ps:solmParam* $[ -> $ret:ident]? { $body:solmStmt* }) => do
      let retStx ← match ret with
        | some t => `([$(← abiTypeStx t)])
        | none   => `([])
      `(({ name := $(quote nm.getId.toString), params := [ $[sParam% $ps],* ],
           returnType := $retStx, body := sBlock% { $body* } } : Solm.TransitionDecl))

/-- `solm_function name (params) -> ret { body }` to a `Solm.FunctionDecl` (internal fn). -/
syntax "solm_function " ident solmParam* (" -> " ident)? "{" solmStmt* "}" : term
macro_rules
  | `(solm_function $nm:ident $ps:solmParam* $[ -> $ret:ident]? { $body:solmStmt* }) => do
      let retStx ← match ret with
        | some t => `([$(← abiTypeStx t)])
        | none   => `([])
      `(({ name := $(quote nm.getId.toString), params := [ $[sParam% $ps],* ],
           returnType := $retStx, body := sBlock% { $body* } } : Solm.FunctionDecl))

end Solm.Notation
