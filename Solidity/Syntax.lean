import ABI.Types

/-!
# Solidity abstract syntax

Mirrors the Solidity 0.8 grammar (no inline assembly, function types, fixed-point or transient
storage).  Identifiers are raw names; resolution (inheritance, overloads, getters, builtins) is
done by `Solidity.Elab` and the semantics, so one base unit can be shared by many programs.
Elementary type names in expression position are the only lexically classified forms
(`Expr.typeExpr`).
-/

namespace Solidity

abbrev Ident := String

inductive DataLoc where
  | memory | storage | calldata
  deriving DecidableEq, Repr, Inhabited

/-- `pub`/`priv` because `public`/`private` are Lean keywords. -/
inductive Visibility where
  | external | pub | internal | priv
  deriving DecidableEq, Repr, Inhabited

inductive Mutability where
  | nonpayable | view | pure | payable
  deriving DecidableEq, Repr, Inhabited

inductive VarMutability where
  | mutable | constant | immutable
  deriving DecidableEq, Repr, Inhabited

inductive SubDenom where
  | wei | gwei | ether | seconds | minutes | hours | days | weeks
  deriving DecidableEq, Repr, Inhabited

inductive ContractKind where
  | contract | abstractContract | interface | library
  deriving DecidableEq, Repr, Inhabited

inductive Ty where
  | uint (w : ABI.BitWidth)
  | int (w : ABI.BitWidth)
  | bool
  | address (payable : Bool)
  /-- `bytesN` with `N = n + 1`, as `ABI.ElemType.bytes`. -/
  | fixedBytes (n : Fin 32)
  | bytes
  | string
  /-- A struct, enum, contract, interface or library name, optionally qualified (`A.S`). -/
  | user (qual : Option Ident) (name : Ident)
  | mapping (key val : Ty)
  | array (elem : Ty) (n : Nat)
  | dynArray (elem : Ty)
  deriving DecidableEq, Repr, Inhabited

namespace Ty

def bitWidth? (n : Nat) : Option ABI.BitWidth :=
  if h : 0 < n ∧ n ≤ 256 ∧ n % 8 = 0 then some ⟨n, h⟩ else none

def uintN? (n : Nat) : Option Ty := (bitWidth? n).map .uint
def intN? (n : Nat) : Option Ty := (bitWidth? n).map .int
def bytesN? (n : Nat) : Option Ty := if h : 0 < n ∧ n ≤ 32 then some (.fixedBytes ⟨n - 1, by omega⟩) else none

def uint256 : Ty := .uint ⟨256, by decide⟩
def int256 : Ty := .int ⟨256, by decide⟩
def uint8 : Ty := .uint ⟨8, by decide⟩
def bytes32 : Ty := .fixedBytes ⟨31, by decide⟩

end Ty

inductive Literal where
  /-- Integer literal (non-negative; `-1` is unary minus on `1`), with an optional unit suffix. -/
  | number (n : Nat) (unit : Option SubDenom)
  /-- Decimal / scientific literal `mantissa * 10^exp10` (e.g. `2.5` = `25e-1`, `1e18`). -/
  | decimal (mantissa : Nat) (exp10 : Int) (unit : Option SubDenom)
  | bool (b : Bool)
  | str (s : String)
  | unicodeStr (s : String)
  | hexStr (bytes : List UInt8)
  deriving DecidableEq, Repr, Inhabited

inductive UnOp where
  | neg | not | bitNot | preInc | preDec | postInc | postDec | delete
  deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul | div | mod | exp | shl | shr
  | bitAnd | bitOr | bitXor | and | or
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

inductive AssignOp where
  | assign | add | sub | mul | div | mod | bitAnd | bitOr | bitXor | shl | shr
  deriving DecidableEq, Repr, Inhabited

mutual

inductive Expr where
  | lit (l : Literal)
  | ident (x : Ident)
  | this
  | super
  | member (e : Expr) (name : Ident)
  | index (e i : Expr)
  | slice (e : Expr) (lo hi : Option Expr)
  | call (callee : Expr) (opts : List CallOpt) (args : Args)
  /-- `new T` in callee position (`new C{value: v}(a)`, `new bytes(n)`, `new T[](n)`). -/
  | new (ty : Ty)
  /-- A type in expression position: conversion callee `T(e)`, `type(T)`, `abi.decode` targets. -/
  | typeExpr (ty : Ty)
  | unary (op : UnOp) (e : Expr)
  | binary (op : BinOp) (a b : Expr)
  | cond (c t e : Expr)
  | assign (op : AssignOp) (lhs rhs : Expr)
  /-- `(a, , b)`; a missing component is `none`. -/
  | tuple (elems : List (Option Expr))
  | arrayLit (elems : List Expr)

inductive CallOpt where
  | value (e : Expr)
  | gas (e : Expr)
  | salt (e : Expr)

inductive Args where
  | positional (es : List Expr)
  | named (fs : List (Ident × Expr))

end

deriving instance Repr for Expr
deriving instance Repr for CallOpt
deriving instance Repr for Args
deriving instance Inhabited for Expr
deriving instance Inhabited for CallOpt
deriving instance Inhabited for Args

structure Param where
  ty : Ty
  loc : Option DataLoc := none
  name : Option Ident := none
  deriving DecidableEq, Repr, Inhabited

structure EventParam where
  ty : Ty
  indexed : Bool := false
  name : Option Ident := none
  deriving DecidableEq, Repr, Inhabited

mutual

inductive Stmt where
  | block (b : List Stmt)
  | varDecl (ty : Ty) (loc : Option DataLoc) (name : Ident) (init : Option Expr)
  /-- `(uint a, , bool c) = rhs;` — a `none` binder skips a component. -/
  | tupleDecl (binders : List (Option Param)) (rhs : Expr)
  | exprStmt (e : Expr)
  | ite (c : Expr) (t : Stmt) (e : Option Stmt)
  | while (c : Expr) (body : Stmt)
  | doWhile (body : Stmt) (c : Expr)
  | for (init : Option Stmt) (cond : Option Expr) (post : Option Expr) (body : Stmt)
  | break
  | continue
  | return (e : Option Expr)
  | emit (event : Expr) (args : Args)
  /-- `revert E(args);` (a custom error).  `revert("m");` is an `exprStmt` call. -/
  | revert (err : Expr) (args : Args)
  | tryCatch (call : Expr) (returns : List Param) (body : List Stmt) (clauses : List CatchClause)
  | unchecked (b : List Stmt)
  /-- The modifier placeholder `_;`. -/
  | placeholder

inductive CatchClause where
  /-- `kind` is `none` for `catch (bytes memory d)` / `catch {}`, `some "Error"` / `some "Panic"` otherwise. -/
  | mk (kind : Option Ident) (params : List Param) (body : List Stmt)

end

deriving instance Repr for Stmt
deriving instance Repr for CatchClause
deriving instance Inhabited for Stmt
deriving instance Inhabited for CatchClause

abbrev Block := List Stmt

structure StateVarDecl where
  name : Ident
  ty : Ty
  visibility : Visibility := .internal
  mutability : VarMutability := .mutable
  /-- `override` / `override(A, B)` on a public variable implementing an interface function. -/
  overrides : Option (List Ident) := none
  init : Option Expr := none
  deriving Repr, Inhabited

/-- A modifier invocation or a base-constructor call on a constructor (`Base(args)`). -/
structure ModifierInvocation where
  name : Ident
  args : Option Args := none
  deriving Repr, Inhabited

inductive FnKind where
  | function | ctor | receive | fallback
  deriving DecidableEq, Repr, Inhabited

structure FnDecl where
  kind : FnKind := .function
  name : Ident := ""
  params : List Param := []
  /-- Return parameters; named returns carry `name := some _`. -/
  returns : List Param := []
  visibility : Option Visibility := none
  mutability : Mutability := .nonpayable
  modifiers : List ModifierInvocation := []
  isVirtual : Bool := false
  /-- `none`: no `override`; `some []`: bare `override`; `some [A, B]`: `override(A, B)`. -/
  overrides : Option (List Ident) := none
  /-- `none` for abstract / interface functions. -/
  body : Option Block := none
  deriving Repr, Inhabited

structure ModifierDecl where
  name : Ident
  params : List Param := []
  isVirtual : Bool := false
  overrides : Option (List Ident) := none
  body : Option Block := none
  deriving Repr, Inhabited

structure EventDecl where
  name : Ident
  params : List EventParam := []
  anonymous : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure ErrorDecl where
  name : Ident
  params : List Param := []
  deriving DecidableEq, Repr, Inhabited

structure StructDecl where
  name : Ident
  fields : List (Ty × Ident)
  deriving DecidableEq, Repr, Inhabited

structure EnumDecl where
  name : Ident
  members : List Ident
  deriving DecidableEq, Repr, Inhabited

inductive UsingTarget where
  | library (l : Ident)
  | functions (fs : List Ident)
  deriving DecidableEq, Repr, Inhabited

/-- `using L for T;` (`ty := none` for `*`). -/
structure UsingFor where
  target : UsingTarget
  ty : Option Ty := none
  deriving DecidableEq, Repr, Inhabited

/-- One entry of an `is` list: `B` or `B(args)`. -/
structure BaseSpec where
  name : Ident
  args : Option Args := none
  deriving Repr, Inhabited

inductive ContractItem where
  | stateVar (d : StateVarDecl)
  | fn (d : FnDecl)
  | modifier (d : ModifierDecl)
  | event (d : EventDecl)
  | error (d : ErrorDecl)
  | struct (d : StructDecl)
  | enum (d : EnumDecl)
  | usingFor (u : UsingFor)
  deriving Repr, Inhabited

structure ContractDecl where
  kind : ContractKind
  name : Ident
  bases : List BaseSpec := []
  items : List ContractItem := []
  deriving Repr, Inhabited

/-- A top-level source unit item. -/
inductive SourceUnit where
  | contract (c : ContractDecl)
  | struct (d : StructDecl)
  | enum (d : EnumDecl)
  | error (d : ErrorDecl)
  | event (d : EventDecl)
  | constant (d : StateVarDecl)
  deriving Repr, Inhabited

abbrev Program := List SourceUnit

/-! ### Queries -/

namespace ContractDecl

def stateVars (c : ContractDecl) : List StateVarDecl :=
  c.items.filterMap fun | .stateVar d => some d | _ => none

def fns (c : ContractDecl) : List FnDecl :=
  c.items.filterMap fun | .fn d => some d | _ => none

def functions (c : ContractDecl) : List FnDecl :=
  c.fns.filter (·.kind == .function)

def ctor? (c : ContractDecl) : Option FnDecl :=
  c.fns.find? (·.kind == .ctor)

def fn? (c : ContractDecl) (name : Ident) : Option FnDecl :=
  c.functions.find? (·.name == name)

def modifiers (c : ContractDecl) : List ModifierDecl :=
  c.items.filterMap fun | .modifier d => some d | _ => none

def events (c : ContractDecl) : List EventDecl :=
  c.items.filterMap fun | .event d => some d | _ => none

def errors (c : ContractDecl) : List ErrorDecl :=
  c.items.filterMap fun | .error d => some d | _ => none

def structs (c : ContractDecl) : List StructDecl :=
  c.items.filterMap fun | .struct d => some d | _ => none

def enums (c : ContractDecl) : List EnumDecl :=
  c.items.filterMap fun | .enum d => some d | _ => none

def usings (c : ContractDecl) : List UsingFor :=
  c.items.filterMap fun | .usingFor u => some u | _ => none

end ContractDecl

def SourceUnit.contract? : SourceUnit → Option ContractDecl
  | .contract c => some c
  | _ => none

def Program.contract? (p : Program) (name : Ident) : Option ContractDecl :=
  p.findSome? fun u => (u.contract?).bind fun c => if c.name == name then some c else none

end Solidity
