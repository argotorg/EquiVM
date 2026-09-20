import Lean
import Solidity.Syntax

/-!
# `sol%` — Solidity surface syntax

A Lean-embedded frontend for `Solidity.Syntax`.  One `sol% <unit>` term is one `SourceUnit`; a
program is a Lean list of units, so base contracts are written once and shared.

Design:
* The translator is a pure syntax → AST map: no desugaring, no name resolution.  Only elementary
  type names in expression position, `this`/`super`/`true`/`false`, literal units and `hex`/
  `unicode` string prefixes are recognised lexically.
* `solidityExpr`, `solidityStmt`, `solidityItem` and `solidityUnit` use
  `(behavior := both)`, so productions can start with Solidity keywords (`emit`, `revert`,
  `unchecked`, `function`, …) without reserving those words as Lean tokens.  Identifiers that
  are Lean keywords are written `«from»`, `«to»`, `«end»`, ….
* Unsupported spellings: `x--`/`--x` (Lean comment token; write `x -= 1`), single-quoted
  strings, `//` comments (use Lean comments).
* Escapes: `${t}` splices a Lean `Expr` / `Stmt` / `ContractItem` term; `#t` is an integer literal
  from a Lean `Nat` term.
-/

namespace Solidity.Notation

open Lean Elab Macro

/-! ## Grammar -/

-- Escapes live in a default-behavior category: a `(behavior := both)` category never registers the
-- leading atom of a production as a token, so `${`/`#` must be declared here and embedded.
declare_syntax_cat solidityEsc
syntax "${" term "}" : solidityEsc
syntax "#" term:max : solidityEsc
-- Registers tokens for productions in `both` categories (never used as a category): `~` for the
-- prefix operator, `delete` so that `delete x;` cannot also parse as a declaration of type `delete`.
declare_syntax_cat solidityTokens
syntax "~" : solidityTokens
syntax "delete" : solidityTokens

declare_syntax_cat solidityTy
declare_syntax_cat solidityExpr (behavior := both)
declare_syntax_cat solidityStmt (behavior := both)
declare_syntax_cat solidityParam
declare_syntax_cat solidityEventParam
declare_syntax_cat solidityCatch
declare_syntax_cat solidityItem (behavior := both)
declare_syntax_cat solidityUnit (behavior := both)

-- Types
syntax:max ident : solidityTy
syntax:max ident &" payable" : solidityTy                                        -- address payable
syntax:max atomic(ident "(" solidityTy (ident)? " => ") solidityTy (ident)? ")" : solidityTy  -- mapping(K => V)
syntax:max solidityTy "[" "]" : solidityTy
syntax:max solidityTy "[" num "]" : solidityTy

-- Expressions: atoms
syntax:max num : solidityExpr
syntax:max num ident : solidityExpr                                              -- 1 ether, 3 days
syntax:max scientific : solidityExpr
syntax:max scientific ident : solidityExpr
syntax:max str : solidityExpr
syntax:max ident str : solidityExpr                                              -- hex"00ff", unicode"…"
syntax:max ident : solidityExpr
syntax:max (name := solidityParen) "(" sepBy((solidityExpr)?, ",") ")" : solidityExpr   -- (e) / tuples
syntax:max "[" solidityExpr,* "]" : solidityExpr                                 -- inline array
syntax:max "new " solidityTy : solidityExpr
syntax:max solidityEsc : solidityExpr

-- Expressions: postfix
syntax:max solidityExpr:max "(" solidityExpr,* ")" : solidityExpr                -- call
syntax:max solidityExpr:max "(" "{" sepBy(ident ": " solidityExpr, ",") "}" ")" : solidityExpr  -- named args
syntax:max solidityExpr:max atomic("{" sepBy(ident ": " solidityExpr, ",") "}") "(" solidityExpr,* ")" : solidityExpr  -- call options (atomic: a `try` body may follow the call)
syntax:max solidityExpr:max "[" solidityExpr "]" : solidityExpr
syntax:max solidityExpr:max "[" (solidityExpr)? ":" (solidityExpr)? "]" : solidityExpr
syntax:max solidityExpr:max "." ident : solidityExpr
syntax:max solidityExpr:max "++" : solidityExpr

-- Expressions: prefix
syntax:80 "!" solidityExpr:80 : solidityExpr
syntax:80 "~" solidityExpr:80 : solidityExpr
syntax:80 "-" solidityExpr:80 : solidityExpr
syntax:80 "++" solidityExpr:80 : solidityExpr
syntax:80 "delete " solidityExpr:80 : solidityExpr

-- Expressions: binary (Solidity precedence table)
syntax:74 solidityExpr:75 " ** " solidityExpr:74 : solidityExpr
syntax:70 solidityExpr:70 " * " solidityExpr:71 : solidityExpr
syntax:70 solidityExpr:70 " / " solidityExpr:71 : solidityExpr
syntax:70 solidityExpr:70 " % " solidityExpr:71 : solidityExpr
syntax:65 solidityExpr:65 " + " solidityExpr:66 : solidityExpr
syntax:65 solidityExpr:65 " - " solidityExpr:66 : solidityExpr
syntax:60 solidityExpr:60 " << " solidityExpr:61 : solidityExpr
syntax:60 solidityExpr:60 " >> " solidityExpr:61 : solidityExpr
syntax:57 solidityExpr:57 " & " solidityExpr:58 : solidityExpr
syntax:55 solidityExpr:55 " ^ " solidityExpr:56 : solidityExpr
syntax:53 solidityExpr:53 " | " solidityExpr:54 : solidityExpr
syntax:50 solidityExpr:51 " < " solidityExpr:51 : solidityExpr
syntax:50 solidityExpr:51 " <= " solidityExpr:51 : solidityExpr
syntax:50 solidityExpr:51 " > " solidityExpr:51 : solidityExpr
syntax:50 solidityExpr:51 " >= " solidityExpr:51 : solidityExpr
syntax:47 solidityExpr:48 " == " solidityExpr:48 : solidityExpr
syntax:47 solidityExpr:48 " != " solidityExpr:48 : solidityExpr
syntax:35 solidityExpr:36 " && " solidityExpr:35 : solidityExpr
syntax:30 solidityExpr:31 " || " solidityExpr:30 : solidityExpr
syntax:20 solidityExpr:21 " ? " solidityExpr:20 " : " solidityExpr:20 : solidityExpr

-- Expressions: assignment (right associative)
syntax:10 solidityExpr:11 " = " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " += " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " -= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " *= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " /= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " %= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " &= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " |= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " ^= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " <<= " solidityExpr:10 : solidityExpr
syntax:10 solidityExpr:11 " >>= " solidityExpr:10 : solidityExpr

-- Parameters
syntax solidityLoc := &"memory" <|> &"storage" <|> &"calldata"
syntax solidityTy (solidityLoc)? (ident)? : solidityParam
syntax solidityTy (&"indexed")? (ident)? : solidityEventParam

-- Statements
syntax solidityTy (solidityLoc)? ident (" = " solidityExpr)? ";" : solidityStmt
syntax (name := solidityTupleDecl)
  "(" sepBy((atomic(solidityParam))?, ",") ")" " = " solidityExpr ";" : solidityStmt
syntax solidityExpr ";" : solidityStmt
syntax "{" solidityStmt* "}" : solidityStmt
syntax "if " "(" solidityExpr ")" solidityStmt (" else " solidityStmt)? : solidityStmt
syntax "while " "(" solidityExpr ")" solidityStmt : solidityStmt
syntax "do " solidityStmt " while " "(" solidityExpr ")" ";" : solidityStmt
syntax (name := solidityFor)
  "for " "(" (solidityStmt <|> ";") (solidityExpr)? ";" (solidityExpr)? ")" solidityStmt : solidityStmt
syntax "return" (solidityExpr)? ";" : solidityStmt
syntax "break" ";" : solidityStmt
syntax "continue" ";" : solidityStmt
syntax "emit " solidityExpr ";" : solidityStmt
syntax "revert " ident "(" solidityExpr,* ")" ";" : solidityStmt
syntax "revert " ident "(" "{" sepBy(ident ": " solidityExpr, ",") "}" ")" ";" : solidityStmt
syntax (name := solidityTry)
  "try " solidityExpr (&"returns" "(" solidityParam,* ")")? "{" solidityStmt* "}" solidityCatch+ : solidityStmt
syntax (name := solidityCatchClause)
  "catch " (ident)? ("(" solidityParam,* ")")? "{" solidityStmt* "}" : solidityCatch
syntax "unchecked " "{" solidityStmt* "}" : solidityStmt
syntax "_" ";" : solidityStmt
syntax solidityEsc : solidityStmt

-- Items
syntax solidityVarAttr := "public" <|> "private" <|> &"internal" <|> &"constant" <|> &"immutable"
  <|> (&"override" ("(" ident,* ")")?)
syntax solidityFnAttr := "public" <|> "private" <|> &"internal" <|> &"external" <|> &"payable"
  <|> &"view" <|> &"pure" <|> &"virtual" <|> (&"override" ("(" ident,* ")")?)
  <|> (&"returns" "(" solidityParam,* ")") <|> (ident ("(" solidityExpr,* ")")?)
syntax solidityBody := ("{" solidityStmt* "}") <|> ";"
syntax solidityStructMember := solidityTy ident ";"
syntax (name := solidityStateVar)
  solidityTy solidityVarAttr* ident (" = " solidityExpr)? ";" : solidityItem
syntax (name := solidityFunction)
  "function " ident "(" solidityParam,* ")" solidityFnAttr* solidityBody : solidityItem
syntax (name := solidityCtor)
  "constructor " "(" solidityParam,* ")" solidityFnAttr* "{" solidityStmt* "}" : solidityItem
syntax (name := solidityReceive)
  "receive " "(" ")" solidityFnAttr* "{" solidityStmt* "}" : solidityItem
syntax (name := solidityFallback)
  "fallback " "(" solidityParam,* ")" solidityFnAttr* "{" solidityStmt* "}" : solidityItem
syntax (name := solidityModifier)
  "modifier " ident ("(" solidityParam,* ")")? solidityFnAttr* solidityBody : solidityItem
syntax (name := solidityEventItem)
  "event " ident "(" solidityEventParam,* ")" (&"anonymous")? ";" : solidityItem
syntax (name := solidityErrorItem) "error " ident "(" solidityParam,* ")" ";" : solidityItem
syntax (name := solidityStructItem) "struct " ident "{" solidityStructMember* "}" : solidityItem
syntax (name := solidityEnumItem) "enum " ident "{" ident,* "}" : solidityItem
syntax (name := solidityUsing)
  "using " (ident <|> ("{" ident,* "}")) " for " (solidityTy <|> "*") ";" : solidityItem
syntax solidityEsc : solidityItem

-- Units
syntax solidityBase := ident ("(" solidityExpr,* ")")?
syntax (name := solidityContract)
  "contract " ident (&" is " solidityBase,+)? "{" solidityItem* "}" : solidityUnit
syntax (name := solidityAbstract)
  "abstract " "contract " ident (&" is " solidityBase,+)? "{" solidityItem* "}" : solidityUnit
syntax (name := solidityInterface)
  "interface " ident (&" is " solidityBase,+)? "{" solidityItem* "}" : solidityUnit
syntax (name := solidityLibrary) "library " ident "{" solidityItem* "}" : solidityUnit
syntax (name := solidityStructUnit) "struct " ident "{" solidityStructMember* "}" : solidityUnit
syntax (name := solidityEnumUnit) "enum " ident "{" ident,* "}" : solidityUnit
syntax (name := solidityErrorUnit) "error " ident "(" solidityParam,* ")" ";" : solidityUnit
syntax (name := solidityEventUnit)
  "event " ident "(" solidityEventParam,* ")" (&"anonymous")? ";" : solidityUnit
syntax (name := solidityConstUnit) solidityTy &" constant " ident " = " solidityExpr ";" : solidityUnit

syntax:max "sol% " solidityUnit : term

/-! ## Translator -/

private def nameStr (x : Name) : String := x.toString (escape := false)

private def identStr (x : TSyntax `ident) : String := nameStr x.getId

private def identParts (x : TSyntax `ident) : List String :=
  x.getId.components.map nameStr

private def strLit (s : String) : Term := Syntax.mkStrLit s

private def natLit (n : Nat) : Term := Syntax.mkNumLit (toString n)

private def widthAfter? (prefixLen : Nat) (s : String) : Option Nat :=
  let rest := s.drop prefixLen
  if rest.isEmpty then some 256 else rest.toNat?

/-- The elementary type named `s`, if any. -/
private def elemTy? (s : String) : Option (MacroM Term) :=
  if s == "bool" then some `(Solidity.Ty.bool)
  else if s == "address" then some `(Solidity.Ty.address false)
  else if s == "bytes" then some `(Solidity.Ty.bytes)
  else if s == "string" then some `(Solidity.Ty.string)
  else if s.startsWith "uint" then
    (widthAfter? 4 s).map fun n => `(Solidity.Ty.uint ⟨$(natLit n), by decide⟩)
  else if s.startsWith "int" then
    (widthAfter? 3 s).map fun n => `(Solidity.Ty.int ⟨$(natLit n), by decide⟩)
  else if s.startsWith "bytes" then
    ((s.drop 5).toNat?).map fun n => `(Solidity.Ty.fixedBytes ⟨$(natLit (n - 1)), by decide⟩)
  else none

private def userTy (parts : List String) : MacroM Term :=
  match parts with
  | [n] => `(Solidity.Ty.user none $(strLit n))
  | [q, n] => `(Solidity.Ty.user (some $(strLit q)) $(strLit n))
  | _ => Macro.throwError s!"unsupported type name {".".intercalate parts}"

private def tyOfIdent (x : TSyntax `ident) : MacroM Term :=
  match identParts x with
  | [s] => match elemTy? s with
    | some t => t
    | none => userTy [s]
  | parts => userTy parts

partial def elabTy (stx : TSyntax `solidityTy) : MacroM Term := do
  match stx with
  | `(solidityTy| $x:ident) => tyOfIdent x
  | `(solidityTy| $x:ident payable) =>
    if identStr x == "address" then `(Solidity.Ty.address true)
    else Macro.throwError "only `address payable` may carry `payable`"
  | `(solidityTy| $m:ident ( $k $[$_kn:ident]? => $v $[$_vn:ident]? )) =>
    if identStr m == "mapping" then `(Solidity.Ty.mapping $(← elabTy k) $(← elabTy v))
    else Macro.throwError s!"expected `mapping`, got `{identStr m}`"
  | `(solidityTy| $t:solidityTy [ ]) => `(Solidity.Ty.dynArray $(← elabTy t))
  | `(solidityTy| $t:solidityTy [ $n:num ]) => `(Solidity.Ty.array $(← elabTy t) $n)
  | _ => Macro.throwErrorAt stx s!"unsupported type syntax ({stx.raw.getKind})"

private def denomOf? (s : String) : Option Name :=
  match s with
  | "wei" => some ``Solidity.SubDenom.wei | "gwei" => some ``Solidity.SubDenom.gwei
  | "ether" => some ``Solidity.SubDenom.ether | "seconds" => some ``Solidity.SubDenom.seconds
  | "minutes" => some ``Solidity.SubDenom.minutes | "hours" => some ``Solidity.SubDenom.hours
  | "days" => some ``Solidity.SubDenom.days | "weeks" => some ``Solidity.SubDenom.weeks
  | _ => none

private def denomTerm (u : Option (TSyntax `ident)) : MacroM Term :=
  match u with
  | none => `(none)
  | some u =>
    match denomOf? (identStr u) with
    | some n => `(some $(mkIdent n))
    | none => Macro.throwError s!"unknown unit `{identStr u}`"

/-- Digit count of a `0x…` literal token (the `bytesN` conversion rule); `none` for decimal. -/
private def hexDigitsTerm (n : TSyntax `num) : MacroM Term :=
  match n.raw.isLit? numLitKind with
  | some s =>
    if s.startsWith "0x" || s.startsWith "0X" then `(some $(Syntax.mkNumLit (toString (s.length - 2))))
    else `(none)
  | none => `(none)

private def hexNibble? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def decodeHex (s : String) : MacroM (List Nat) := do
  let cs := s.toList.filter (· != '_')
  let rec go : List Char → MacroM (List Nat)
    | [] => pure []
    | [_] => Macro.throwError "hex literal needs an even number of digits"
    | a :: b :: rest => do
      match hexNibble? a, hexNibble? b with
      | some x, some y => return (16 * x + y) :: (← go rest)
      | _, _ => Macro.throwError "invalid hex digit in hex literal"
  go cs

/-- `a.b.c` → `member (member a b) c`, with lexical special cases for the head. -/
private def memberChain (head : Term) (names : List String) : MacroM Term :=
  names.foldlM (fun acc n => `(Solidity.Expr.member $acc $(strLit n))) head

private def headIdent (s : String) : MacroM Term :=
  if s == "this" then `(Solidity.Expr.this)
  else if s == "super" then `(Solidity.Expr.super)
  else if s == "true" then `(Solidity.Expr.lit (Solidity.Literal.bool true))
  else if s == "false" then `(Solidity.Expr.lit (Solidity.Literal.bool false))
  else match elemTy? s with
    | some t => do `(Solidity.Expr.typeExpr $(← t))
    | none => `(Solidity.Expr.ident $(strLit s))

private def exprOfIdent (x : TSyntax `ident) : MacroM Term := do
  match identParts x with
  | [] => Macro.throwUnsupported
  | s :: rest => memberChain (← headIdent s) rest

/-- Is this callee the `type(...)` builtin, or `abi.decode`? -/
private def isIdentNamed (e : TSyntax `solidityExpr) (n : String) : Bool :=
  match e with
  | `(solidityExpr| $x:ident) => identStr x == n
  | _ => false

private def mkList (ts : Array Term) : MacroM Term := `([$ts,*])

private def optTerm (t : Option Term) : MacroM Term :=
  match t with
  | none => `(none)
  | some t => `(some $t)

mutual

/-- An argument in `type(T)` / `abi.decode(d, (T, U))` position: an identifier or tuple of
    identifiers naming types. -/
partial def elabTypeArg (e : TSyntax `solidityExpr) : MacroM Term := do
  match e with
  | `(solidityExpr| $x:ident) => `(Solidity.Expr.typeExpr $(← tyOfIdent x))
  | _ =>
    if e.raw.isOfKind ``solidityParen then
      let elems := e.raw[1].getSepArgs
      let ts ← elems.mapM fun el => do
        if el.getNumArgs = 0 then Macro.throwError "empty component in type tuple"
        `(some $(← elabTypeArg ⟨el[0]⟩))
      `(Solidity.Expr.tuple $(← mkList ts))
    else elabExpr e

partial def elabCallee (f : TSyntax `solidityExpr) : MacroM Term := do
  match f with
  | `(solidityExpr| $x:ident) =>
    if identStr x == "payable" then `(Solidity.Expr.typeExpr (Solidity.Ty.address true))
    else exprOfIdent x
  | _ => elabExpr f

partial def elabArgs (f : TSyntax `solidityExpr) (args : Array (TSyntax `solidityExpr)) :
    MacroM (Array Term) := do
  if isIdentNamed f "type" then
    args.mapM elabTypeArg
  else
    match f with
    | `(solidityExpr| $x:ident) =>
      if identStr x == "abi.decode" && args.size == 2 then
        return #[← elabExpr args[0]!, ← elabTypeArg args[1]!]
      else args.mapM elabExpr
    | _ => args.mapM elabExpr

partial def elabExpr (stx : TSyntax `solidityExpr) : MacroM Term := do
  match stx with
  | `(solidityExpr| $n:num) => `(Solidity.Expr.lit (Solidity.Literal.number $n none $(← hexDigitsTerm n)))
  | `(solidityExpr| $n:num $u:ident) =>
    `(Solidity.Expr.lit (Solidity.Literal.number $n $(← denomTerm (some u)) $(← hexDigitsTerm n)))
  | `(solidityExpr| $s:scientific) => elabScientific s none
  | `(solidityExpr| $s:scientific $u:ident) => elabScientific s (some u)
  | `(solidityExpr| $s:str) => `(Solidity.Expr.lit (Solidity.Literal.str $s))
  | `(solidityExpr| $p:ident $s:str) =>
    match identStr p with
    | "hex" =>
      let bytes ← decodeHex s.getString
      `(Solidity.Expr.lit (Solidity.Literal.hexStr $(← mkList (bytes.toArray.map natLit))))
    | "unicode" => `(Solidity.Expr.lit (Solidity.Literal.unicodeStr $s))
    | other => Macro.throwError s!"unknown string prefix `{other}`"
  | `(solidityExpr| $x:ident) => exprOfIdent x
  | `(solidityExpr| [ $es,* ]) =>
    `(Solidity.Expr.arrayLit $(← mkList (← es.getElems.mapM elabExpr)))
  | `(solidityExpr| new $t:solidityTy) => `(Solidity.Expr.new $(← elabTy t))
  | `(solidityExpr| $e:solidityEsc) =>
    match e with
    | `(solidityEsc| ${ $t }) => `(($t : Solidity.Expr))
    | `(solidityEsc| # $t) => `(Solidity.Expr.lit (Solidity.Literal.number $t none))
    | _ => Macro.throwUnsupported
  | `(solidityExpr| $f:solidityExpr ( $args,* )) =>
    let callee ← elabCallee f
    let argTerms ← elabArgs f args.getElems
    `(Solidity.Expr.call $callee [] (Solidity.Args.positional $(← mkList argTerms)))
  | `(solidityExpr| $f:solidityExpr ( { $[$ks:ident : $vs:solidityExpr],* } )) =>
    let callee ← elabCallee f
    let fields ← (ks.zip vs).mapM fun (k, v) => do `(($(strLit (identStr k)), $(← elabExpr v)))
    `(Solidity.Expr.call $callee [] (Solidity.Args.named $(← mkList fields)))
  | `(solidityExpr| $f:solidityExpr { $[$ks:ident : $vs:solidityExpr],* } ( $args,* )) =>
    let callee ← elabCallee f
    let opts ← (ks.zip vs).mapM fun (k, v) => do
      let v ← elabExpr v
      match identStr k with
      | "value" => `(Solidity.CallOpt.value $v)
      | "gas" => `(Solidity.CallOpt.gas $v)
      | "salt" => `(Solidity.CallOpt.salt $v)
      | other => Macro.throwError s!"unknown call option `{other}`"
    let argTerms ← elabArgs f args.getElems
    `(Solidity.Expr.call $callee $(← mkList opts) (Solidity.Args.positional $(← mkList argTerms)))
  | `(solidityExpr| $e:solidityExpr [ $i:solidityExpr ]) =>
    `(Solidity.Expr.index $(← elabExpr e) $(← elabExpr i))
  | `(solidityExpr| $e:solidityExpr [ $[$lo]? : $[$hi]? ]) =>
    let lo ← optTerm (← lo.mapM elabExpr)
    let hi ← optTerm (← hi.mapM elabExpr)
    `(Solidity.Expr.slice $(← elabExpr e) $lo $hi)
  | `(solidityExpr| $e:solidityExpr . $x:ident) => memberChain (← elabExpr e) (identParts x)
  | `(solidityExpr| $e:solidityExpr ++) => `(Solidity.Expr.unary Solidity.UnOp.postInc $(← elabExpr e))
  | `(solidityExpr| ! $e) => `(Solidity.Expr.unary Solidity.UnOp.not $(← elabExpr e))
  | `(solidityExpr| ~ $e) => `(Solidity.Expr.unary Solidity.UnOp.bitNot $(← elabExpr e))
  | `(solidityExpr| - $e) => `(Solidity.Expr.unary Solidity.UnOp.neg $(← elabExpr e))
  | `(solidityExpr| ++ $e) => `(Solidity.Expr.unary Solidity.UnOp.preInc $(← elabExpr e))
  | `(solidityExpr| delete $e) => `(Solidity.Expr.unary Solidity.UnOp.delete $(← elabExpr e))
  | `(solidityExpr| $a ** $b) => bin ``Solidity.BinOp.exp a b
  | `(solidityExpr| $a * $b) => bin ``Solidity.BinOp.mul a b
  | `(solidityExpr| $a / $b) => bin ``Solidity.BinOp.div a b
  | `(solidityExpr| $a % $b) => bin ``Solidity.BinOp.mod a b
  | `(solidityExpr| $a + $b) => bin ``Solidity.BinOp.add a b
  | `(solidityExpr| $a - $b) => bin ``Solidity.BinOp.sub a b
  | `(solidityExpr| $a << $b) => bin ``Solidity.BinOp.shl a b
  | `(solidityExpr| $a >> $b) => bin ``Solidity.BinOp.shr a b
  | `(solidityExpr| $a & $b) => bin ``Solidity.BinOp.bitAnd a b
  | `(solidityExpr| $a ^ $b) => bin ``Solidity.BinOp.bitXor a b
  | `(solidityExpr| $a | $b) => bin ``Solidity.BinOp.bitOr a b
  | `(solidityExpr| $a < $b) => bin ``Solidity.BinOp.lt a b
  | `(solidityExpr| $a <= $b) => bin ``Solidity.BinOp.le a b
  | `(solidityExpr| $a > $b) => bin ``Solidity.BinOp.gt a b
  | `(solidityExpr| $a >= $b) => bin ``Solidity.BinOp.ge a b
  | `(solidityExpr| $a == $b) => bin ``Solidity.BinOp.eq a b
  | `(solidityExpr| $a != $b) => bin ``Solidity.BinOp.ne a b
  | `(solidityExpr| $a && $b) => bin ``Solidity.BinOp.and a b
  | `(solidityExpr| $a || $b) => bin ``Solidity.BinOp.or a b
  | `(solidityExpr| $c ? $t : $e) =>
    `(Solidity.Expr.cond $(← elabExpr c) $(← elabExpr t) $(← elabExpr e))
  | `(solidityExpr| $a = $b) => assign ``Solidity.AssignOp.assign a b
  | `(solidityExpr| $a += $b) => assign ``Solidity.AssignOp.add a b
  | `(solidityExpr| $a -= $b) => assign ``Solidity.AssignOp.sub a b
  | `(solidityExpr| $a *= $b) => assign ``Solidity.AssignOp.mul a b
  | `(solidityExpr| $a /= $b) => assign ``Solidity.AssignOp.div a b
  | `(solidityExpr| $a %= $b) => assign ``Solidity.AssignOp.mod a b
  | `(solidityExpr| $a &= $b) => assign ``Solidity.AssignOp.bitAnd a b
  | `(solidityExpr| $a |= $b) => assign ``Solidity.AssignOp.bitOr a b
  | `(solidityExpr| $a ^= $b) => assign ``Solidity.AssignOp.bitXor a b
  | `(solidityExpr| $a <<= $b) => assign ``Solidity.AssignOp.shl a b
  | `(solidityExpr| $a >>= $b) => assign ``Solidity.AssignOp.shr a b
  | _ =>
    if stx.raw.isOfKind ``solidityParen then
      let elems := stx.raw[1].getSepArgs
      if elems.size == 1 && elems[0]!.getNumArgs == 1 then
        elabExpr ⟨elems[0]![0]⟩
      else
        let ts ← elems.mapM fun el => do
          if el.getNumArgs == 0 then `(none) else `(some $(← elabExpr ⟨el[0]⟩))
        `(Solidity.Expr.tuple $(← mkList ts))
    else Macro.throwErrorAt stx s!"unsupported expression syntax ({stx.raw.getKind})"

partial def elabScientific (s : TSyntax `scientific) (u : Option (TSyntax `ident)) : MacroM Term := do
  match s.raw.isScientificLit? with
  | some (m, sign, e) =>
    let exp : Int := if sign then -(Int.ofNat e) else Int.ofNat e
    let expTerm ← if exp < 0 then `(-$(natLit exp.natAbs)) else `($(natLit exp.natAbs))
    `(Solidity.Expr.lit (Solidity.Literal.decimal $(natLit m) $expTerm $(← denomTerm u)))
  | none => Macro.throwErrorAt s "malformed scientific literal"

partial def bin (op : Name) (a b : TSyntax `solidityExpr) : MacroM Term := do
  `(Solidity.Expr.binary $(mkIdent op) $(← elabExpr a) $(← elabExpr b))

partial def assign (op : Name) (a b : TSyntax `solidityExpr) : MacroM Term := do
  `(Solidity.Expr.assign $(mkIdent op) $(← elabExpr a) $(← elabExpr b))

end

/-- Text of a keyword node: non-reserved symbols arrive as identifiers, reserved ones as atoms. -/
private def kwText (s : Syntax) : String :=
  if s.isAtom then s.getAtomVal
  else if s.isIdent then nameStr s.getId
  else if s.getNumArgs == 1 && s[0].isAtom then s[0].getAtomVal
  else ""

private def locTerm (l : Option Syntax) : MacroM Term := do
  match l with
  | none => `(none)
  | some l =>
    match kwText l[0] with
    | "memory" => `(some Solidity.DataLoc.memory)
    | "storage" => `(some Solidity.DataLoc.storage)
    | "calldata" => `(some Solidity.DataLoc.calldata)
    | other => Macro.throwError s!"unknown data location `{other}`"

private def optIdentTerm (x : Option (TSyntax `ident)) : MacroM Term :=
  match x with
  | none => `(none)
  | some x => `(some $(strLit (identStr x)))

def elabParam (stx : TSyntax `solidityParam) : MacroM Term := do
  match stx with
  | `(solidityParam| $t:solidityTy $[$l:solidityLoc]? $[$x:ident]?) =>
    `({ ty := $(← elabTy t), loc := $(← locTerm (l.map (·.raw))), name := $(← optIdentTerm x) : Solidity.Param })
  | _ => Macro.throwErrorAt stx "unsupported parameter syntax"

def elabEventParam (stx : TSyntax `solidityEventParam) : MacroM Term := do
  match stx with
  | `(solidityEventParam| $t:solidityTy $[indexed%$ix]? $[$x:ident]?) =>
    let indexed := if ix.isSome then mkIdent ``true else mkIdent ``false
    `({ ty := $(← elabTy t), indexed := $indexed, name := $(← optIdentTerm x) : Solidity.EventParam })
  | _ => Macro.throwErrorAt stx "unsupported event parameter syntax"

private def elabParams (ps : Array (TSyntax `solidityParam)) : MacroM Term := do
  mkList (← ps.mapM elabParam)

mutual

partial def elabBlock (stmts : Array (TSyntax `solidityStmt)) : MacroM Term := do
  mkList (← stmts.mapM elabStmt)

partial def elabStmt (stx : TSyntax `solidityStmt) : MacroM Term := do
  match stx with
  | `(solidityStmt| $t:solidityTy $[$l:solidityLoc]? $x:ident $[= $init]? ;) =>
    let init ← optTerm (← init.mapM elabExpr)
    `(Solidity.Stmt.varDecl $(← elabTy t) $(← locTerm (l.map (·.raw))) $(strLit (identStr x)) $init)
  | `(solidityStmt| $e:solidityExpr ;) => `(Solidity.Stmt.exprStmt $(← elabExpr e))
  | `(solidityStmt| { $ss* }) => `(Solidity.Stmt.block $(← elabBlock ss))
  | `(solidityStmt| if ( $c ) $t $[else $e]?) =>
    let e ← optTerm (← e.mapM elabStmt)
    `(Solidity.Stmt.ite $(← elabExpr c) $(← elabStmt t) $e)
  | `(solidityStmt| while ( $c ) $body) => `(Solidity.Stmt.while $(← elabExpr c) $(← elabStmt body))
  | `(solidityStmt| do $body while ( $c ) ;) =>
    `(Solidity.Stmt.doWhile $(← elabStmt body) $(← elabExpr c))
  | `(solidityStmt| return $[$e:solidityExpr]? ;) => `(Solidity.Stmt.return $(← optTerm (← e.mapM elabExpr)))
  | `(solidityStmt| break ;) => `(Solidity.Stmt.break)
  | `(solidityStmt| continue ;) => `(Solidity.Stmt.continue)
  | `(solidityStmt| emit $e:solidityExpr ;) =>
    match e with
    | `(solidityExpr| $f:solidityExpr ( $args,* )) =>
      let argTerms ← args.getElems.mapM elabExpr
      `(Solidity.Stmt.emit $(← elabExpr f) (Solidity.Args.positional $(← mkList argTerms)))
    | `(solidityExpr| $f:solidityExpr ( { $[$ks:ident : $vs:solidityExpr],* } )) =>
      let fields ← (ks.zip vs).mapM fun (k, v) => do `(($(strLit (identStr k)), $(← elabExpr v)))
      `(Solidity.Stmt.emit $(← elabExpr f) (Solidity.Args.named $(← mkList fields)))
    | _ => Macro.throwError "`emit` expects an event invocation"
  | `(solidityStmt| revert $err:ident ( $args,* ) ;) =>
    let argTerms ← args.getElems.mapM elabExpr
    `(Solidity.Stmt.revert $(← exprOfIdent err) (Solidity.Args.positional $(← mkList argTerms)))
  | `(solidityStmt| revert $err:ident ( { $[$ks:ident : $vs:solidityExpr],* } ) ;) =>
    let fields ← (ks.zip vs).mapM fun (k, v) => do `(($(strLit (identStr k)), $(← elabExpr v)))
    `(Solidity.Stmt.revert $(← exprOfIdent err) (Solidity.Args.named $(← mkList fields)))
  | `(solidityStmt| unchecked { $ss* }) => `(Solidity.Stmt.unchecked $(← elabBlock ss))
  | `(solidityStmt| _ ;) => `(Solidity.Stmt.placeholder)
  | `(solidityStmt| $e:solidityEsc) =>
    match e with
    | `(solidityEsc| ${ $t }) => `(($t : Solidity.Stmt))
    | _ => Macro.throwError "only `${…}` escapes are allowed in statement position"
  | _ =>
    if stx.raw.isOfKind ``solidityFor then
      -- for ( init cond? ; post? ) body
      let initStx := stx.raw[2]
      let init ← if initStx.isAtom then `(none) else do `(some $(← elabStmt ⟨initStx⟩))
      let condStx := stx.raw[3]
      let cond ← if condStx.getNumArgs == 0 then `(none) else do `(some $(← elabExpr ⟨condStx[0]⟩))
      let postStx := stx.raw[5]
      let post ← if postStx.getNumArgs == 0 then `(none) else do `(some $(← elabExpr ⟨postStx[0]⟩))
      `(Solidity.Stmt.for $init $cond $post $(← elabStmt ⟨stx.raw[7]⟩))
    else if stx.raw.isOfKind ``solidityTupleDecl then
      -- ( binders ) = rhs ;
      let binders := stx.raw[1].getSepArgs
      let bs ← binders.mapM fun b => do
        if b.getNumArgs == 0 then `(none) else `(some $(← elabParam ⟨b[0]⟩))
      `(Solidity.Stmt.tupleDecl $(← mkList bs) $(← elabExpr ⟨stx.raw[4]⟩))
    else if stx.raw.isOfKind ``solidityTry then
      -- try call (returns ( params ))? { body } catch+
      let call ← elabExpr ⟨stx.raw[1]⟩
      let retsStx := stx.raw[2]
      let rets ← if retsStx.getNumArgs == 0 then `([])
        else elabParams (retsStx[2].getSepArgs.map (⟨·⟩))
      let body ← elabBlock (stx.raw[4].getArgs.map (⟨·⟩))
      let clauses ← stx.raw[6].getArgs.mapM fun c => elabCatch ⟨c⟩
      `(Solidity.Stmt.tryCatch $call $rets $body $(← mkList clauses))
    else Macro.throwErrorAt stx s!"unsupported statement syntax ({stx.raw.getKind})"

partial def elabCatch (stx : TSyntax `solidityCatch) : MacroM Term := do
  -- catch (ident)? ( ( params ) )? { body }
  let kindStx := stx.raw[1]
  let kind ← if kindStx.getNumArgs == 0 then `(none) else `(some $(strLit (nameStr kindStx[0].getId)))
  let paramsStx := stx.raw[2]
  let params ← if paramsStx.getNumArgs == 0 then `([])
    else elabParams (paramsStx[1].getSepArgs.map (⟨·⟩))
  let body ← elabBlock (stx.raw[4].getArgs.map (⟨·⟩))
  `(Solidity.CatchClause.mk $kind $params $body)

end

/-! ### Items -/

private structure FnAttrs where
  visibility : Option Term := none
  mutability : Option Term := none
  isVirtual : Bool := false
  overrides : Option (Array String) := none
  returns : Option (Array Term) := none
  modifiers : Array Term := #[]

private def visibilityTerm (s : String) : Option (MacroM Term) :=
  match s with
  | "public" => some `(some Solidity.Visibility.pub)
  | "private" => some `(some Solidity.Visibility.priv)
  | "internal" => some `(some Solidity.Visibility.internal)
  | "external" => some `(some Solidity.Visibility.external)
  | _ => none

private def mutabilityTerm (s : String) : Option (MacroM Term) :=
  match s with
  | "payable" => some `(Solidity.Mutability.payable)
  | "view" => some `(Solidity.Mutability.view)
  | "pure" => some `(Solidity.Mutability.pure)
  | _ => none

/-- Fold one `solidityFnAttr` node into the accumulator.  Keyword alternatives arrive as
    `token.<kw>` nodes or atoms; `override(…)`, `returns(…)` and modifier invocations as groups. -/
private def foldFnAttr (acc : FnAttrs) (attr : Syntax) : MacroM FnAttrs := do
  let node := attr[0]
  let isGroup := node.getKind == `group
  let headStr := if isGroup then kwText node[0] else kwText node
  if let some v := visibilityTerm headStr then return { acc with visibility := some (← v) }
  if let some m := mutabilityTerm headStr then return { acc with mutability := some (← m) }
  if headStr == "virtual" then return { acc with isVirtual := true }
  if headStr == "override" then
    let names := if !isGroup || node[1].getNumArgs == 0 then #[]
      else node[1][1].getSepArgs.map fun x => nameStr x.getId
    return { acc with overrides := some names }
  if headStr == "returns" then
    if !isGroup then Macro.throwError "`returns` needs a parameter list"
    let ps := node[2].getSepArgs.map (⟨·⟩ : Syntax → TSyntax `solidityParam)
    return { acc with returns := some (← ps.mapM elabParam) }
  if headStr.isEmpty then Macro.throwErrorAt attr "unsupported function attribute"
  let args ← if !isGroup || node[1].getNumArgs == 0 then `(none)
    else do
      let es ← node[1][1].getSepArgs.mapM fun e => elabExpr ⟨e⟩
      `(some (Solidity.Args.positional $(← mkList es)))
  let mi ← `({ name := $(strLit headStr), args := $args : Solidity.ModifierInvocation })
  return { acc with modifiers := acc.modifiers.push mi }

private def foldFnAttrs (attrs : Array Syntax) : MacroM FnAttrs :=
  attrs.foldlM foldFnAttr {}

private def overridesTerm (o : Option (Array String)) : MacroM Term :=
  match o with
  | none => `(none)
  | some names => do `(some $(← mkList (names.map strLit)))

private def boolTerm (b : Bool) : Term := if b then mkIdent ``true else mkIdent ``false

private def fnDeclTerm (kind : Term) (name : String) (params : Term) (attrs : FnAttrs)
    (body : Option Term) : MacroM Term := do
  let vis ← match attrs.visibility with | some v => pure v | none => `(none)
  let mut_ ← match attrs.mutability with | some m => pure m | none => `(Solidity.Mutability.nonpayable)
  let rets ← match attrs.returns with | some rs => mkList rs | none => `([])
  let body ← optTerm body
  `({ kind := $kind, name := $(strLit name), params := $params, returns := $rets,
      visibility := $vis, mutability := $mut_, modifiers := $(← mkList attrs.modifiers),
      isVirtual := $(boolTerm attrs.isVirtual), overrides := $(← overridesTerm attrs.overrides),
      body := $body : Solidity.FnDecl })

/-- `solidityBody` node: `{ stmts }` group or `;`. -/
private def elabBody (stx : Syntax) : MacroM (Option Term) := do
  let node := stx[0]
  if node.isAtom then return none
  return some (← elabBlock (node[1].getArgs.map (⟨·⟩)))

private def elabStructMembers (ms : Array Syntax) : MacroM Term := do
  mkList (← ms.mapM fun m => do `(($(← elabTy ⟨m[0]⟩), $(strLit (nameStr m[1].getId)))))

private def elabEventDecl (name : Syntax) (params : Array Syntax) (anon : Syntax) : MacroM Term := do
  let ps ← mkList (← params.mapM fun p => elabEventParam ⟨p⟩)
  `({ name := $(strLit (nameStr name.getId)), params := $ps,
      anonymous := $(boolTerm (anon.getNumArgs != 0)) : Solidity.EventDecl })

private def elabErrorDecl (name : Syntax) (params : Array Syntax) : MacroM Term := do
  `({ name := $(strLit (nameStr name.getId)),
      params := $(← elabParams (params.map (⟨·⟩))) : Solidity.ErrorDecl })

private def elabStructDecl (name : Syntax) (members : Array Syntax) : MacroM Term := do
  `({ name := $(strLit (nameStr name.getId)), fields := $(← elabStructMembers members) : Solidity.StructDecl })

private def elabEnumDecl (name : Syntax) (members : Array Syntax) : MacroM Term := do
  `({ name := $(strLit (nameStr name.getId)),
      members := $(← mkList (members.map fun m => strLit (nameStr m.getId))) : Solidity.EnumDecl })

private def elabVarAttrs (attrs : Array Syntax) : MacroM (Term × Term × Term) := do
  let mut vis ← `(Solidity.Visibility.internal)
  let mut mutab ← `(Solidity.VarMutability.mutable)
  let mut ov ← `(none)
  for attr in attrs do
    let node := attr[0]
    let isGroup := node.getKind == `group
    let s := if isGroup then kwText node[0] else kwText node
    match s with
    | "public" => vis ← `(Solidity.Visibility.pub)
    | "private" => vis ← `(Solidity.Visibility.priv)
    | "internal" => vis ← `(Solidity.Visibility.internal)
    | "constant" => mutab ← `(Solidity.VarMutability.constant)
    | "immutable" => mutab ← `(Solidity.VarMutability.immutable)
    | "override" =>
      let names := if !isGroup || node[1].getNumArgs == 0 then #[]
        else node[1][1].getSepArgs.map fun x => strLit (nameStr x.getId)
      ov ← `(some $(← mkList names))
    | other => Macro.throwError s!"unknown state variable attribute `{other}`"
  return (vis, mutab, ov)

def elabItem (stx : TSyntax `solidityItem) : MacroM Term := do
  let raw := stx.raw
  if raw.isOfKind ``solidityStateVar then
    -- ty attrs* ident (= init)? ;
    let ty ← elabTy ⟨raw[0]⟩
    let (vis, mutab, ov) ← elabVarAttrs raw[1].getArgs
    let name := nameStr raw[2].getId
    let init ← if raw[3].getNumArgs == 0 then `(none) else do `(some $(← elabExpr ⟨raw[3][1]⟩))
    `(Solidity.ContractItem.stateVar
      { name := $(strLit name), ty := $ty, visibility := $vis, mutability := $mutab,
        overrides := $ov, init := $init : Solidity.StateVarDecl })
  else if raw.isOfKind ``solidityFunction then
    -- function ident ( params ) attrs* body
    let name := nameStr raw[1].getId
    let params ← elabParams (raw[3].getSepArgs.map (⟨·⟩))
    let attrs ← foldFnAttrs raw[5].getArgs
    let body ← elabBody raw[6]
    `(Solidity.ContractItem.fn $(← fnDeclTerm (← `(Solidity.FnKind.function)) name params attrs body))
  else if raw.isOfKind ``solidityCtor then
    -- constructor ( params ) attrs* { stmts }
    let params ← elabParams (raw[2].getSepArgs.map (⟨·⟩))
    let attrs ← foldFnAttrs raw[4].getArgs
    let body ← elabBlock (raw[6].getArgs.map (⟨·⟩))
    `(Solidity.ContractItem.fn $(← fnDeclTerm (← `(Solidity.FnKind.ctor)) "" params attrs (some body)))
  else if raw.isOfKind ``solidityReceive then
    -- receive ( ) attrs* { stmts }
    let attrs ← foldFnAttrs raw[3].getArgs
    let body ← elabBlock (raw[5].getArgs.map (⟨·⟩))
    `(Solidity.ContractItem.fn $(← fnDeclTerm (← `(Solidity.FnKind.receive)) "" (← `([])) attrs (some body)))
  else if raw.isOfKind ``solidityFallback then
    -- fallback ( params ) attrs* { stmts }
    let params ← elabParams (raw[2].getSepArgs.map (⟨·⟩))
    let attrs ← foldFnAttrs raw[4].getArgs
    let body ← elabBlock (raw[6].getArgs.map (⟨·⟩))
    `(Solidity.ContractItem.fn $(← fnDeclTerm (← `(Solidity.FnKind.fallback)) "" params attrs (some body)))
  else if raw.isOfKind ``solidityModifier then
    -- modifier ident ( ( params ) )? attrs* body
    let name := nameStr raw[1].getId
    let params ← if raw[2].getNumArgs == 0 then `([]) else elabParams (raw[2][1].getSepArgs.map (⟨·⟩))
    let attrs ← foldFnAttrs raw[3].getArgs
    let body ← optTerm (← elabBody raw[4])
    `(Solidity.ContractItem.modifier
      { name := $(strLit name), params := $params, isVirtual := $(boolTerm attrs.isVirtual),
        overrides := $(← overridesTerm attrs.overrides), body := $body : Solidity.ModifierDecl })
  else if raw.isOfKind ``solidityEventItem then
    `(Solidity.ContractItem.event $(← elabEventDecl raw[1] raw[3].getSepArgs raw[5]))
  else if raw.isOfKind ``solidityErrorItem then
    `(Solidity.ContractItem.error $(← elabErrorDecl raw[1] raw[3].getSepArgs))
  else if raw.isOfKind ``solidityStructItem then
    `(Solidity.ContractItem.struct $(← elabStructDecl raw[1] raw[3].getArgs))
  else if raw.isOfKind ``solidityEnumItem then
    `(Solidity.ContractItem.enum $(← elabEnumDecl raw[1] raw[3].getSepArgs))
  else if raw.isOfKind ``solidityUsing then
    -- using (ident | { idents }) for (ty | *) ;
    let targetStx := raw[1]
    let target ← if targetStx.isIdent then `(Solidity.UsingTarget.library $(strLit (nameStr targetStx.getId)))
      else do
        let fs := targetStx[1].getSepArgs.map fun x => strLit (nameStr x.getId)
        `(Solidity.UsingTarget.functions $(← mkList fs))
    let tyStx := raw[3]
    let ty ← if tyStx.isAtom then `(none) else do `(some $(← elabTy ⟨tyStx⟩))
    `(Solidity.ContractItem.usingFor { target := $target, ty := $ty : Solidity.UsingFor })
  else
    match stx with
    | `(solidityItem| $e:solidityEsc) =>
      match e with
      | `(solidityEsc| ${ $t }) => `(($t : Solidity.ContractItem))
      | _ => Macro.throwError "only `${…}` escapes are allowed in item position"
    | _ => Macro.throwErrorAt stx s!"unsupported item syntax ({stx.raw.getKind})"

private def elabBases (stx : Syntax) : MacroM Term := do
  -- optional `is base,+`
  if stx.getNumArgs == 0 then return ← `([])
  let bases ← stx[1].getSepArgs.mapM fun b => do
    let name := strLit (nameStr b[0].getId)
    let args ← if b[1].getNumArgs == 0 then `(none)
      else do
        let es ← b[1][1].getSepArgs.mapM fun e => elabExpr ⟨e⟩
        `(some (Solidity.Args.positional $(← mkList es)))
    `({ name := $name, args := $args : Solidity.BaseSpec })
  mkList bases

private def contractTerm (kind : Term) (name : Syntax) (bases : Syntax) (items : Array Syntax) :
    MacroM Term := do
  let items ← mkList (← items.mapM fun i => elabItem ⟨i⟩)
  `(Solidity.SourceUnit.contract
    { kind := $kind, name := $(strLit (nameStr name.getId)), bases := $(← elabBases bases),
      items := $items : Solidity.ContractDecl })

def elabUnit (stx : TSyntax `solidityUnit) : MacroM Term := do
  let raw := stx.raw
  if raw.isOfKind ``solidityContract then
    contractTerm (← `(Solidity.ContractKind.contract)) raw[1] raw[2] raw[4].getArgs
  else if raw.isOfKind ``solidityAbstract then
    contractTerm (← `(Solidity.ContractKind.abstractContract)) raw[2] raw[3] raw[5].getArgs
  else if raw.isOfKind ``solidityInterface then
    contractTerm (← `(Solidity.ContractKind.interface)) raw[1] raw[2] raw[4].getArgs
  else if raw.isOfKind ``solidityLibrary then
    contractTerm (← `(Solidity.ContractKind.library)) raw[1] (mkNullNode) raw[3].getArgs
  else if raw.isOfKind ``solidityStructUnit then
    `(Solidity.SourceUnit.struct $(← elabStructDecl raw[1] raw[3].getArgs))
  else if raw.isOfKind ``solidityEnumUnit then
    `(Solidity.SourceUnit.enum $(← elabEnumDecl raw[1] raw[3].getSepArgs))
  else if raw.isOfKind ``solidityErrorUnit then
    `(Solidity.SourceUnit.error $(← elabErrorDecl raw[1] raw[3].getSepArgs))
  else if raw.isOfKind ``solidityEventUnit then
    `(Solidity.SourceUnit.event $(← elabEventDecl raw[1] raw[3].getSepArgs raw[5]))
  else if raw.isOfKind ``solidityConstUnit then
    -- ty constant ident = e ;
    `(Solidity.SourceUnit.constant
      { name := $(strLit (nameStr raw[2].getId)), ty := $(← elabTy ⟨raw[0]⟩),
        visibility := Solidity.Visibility.internal, mutability := Solidity.VarMutability.constant,
        overrides := none, init := some $(← elabExpr ⟨raw[4]⟩) : Solidity.StateVarDecl })
  else Macro.throwErrorAt stx s!"unsupported unit syntax ({stx.raw.getKind})"

macro_rules
  | `(sol% $u:solidityUnit) => elabUnit u

end Solidity.Notation
