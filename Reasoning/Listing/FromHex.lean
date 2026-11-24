import Reasoning.Listing.Tree
import Reasoning.Listing.Code
import Reasoning.Listing.Tail
import Reasoning.Listing.JumpTable
import Reasoning.Listing.Sha256
import Reasoning.JumpDest
import Lean

/-!
# Listing — from a hex file, at elaboration time

`listing_from_hex` writes a contract's listing (the declarations `scripts/gen_listing.py` used
to write out as text) from the contract's hex file, when the Lean file is elaborated:

```
namespace Foo.Listing
listing_from_hex "runtime.hex" sha256 "<64 hex digits>"
  bytecode Foo.fooBytecode
  [creation] [followed_by tail] [layout Foo.immutableLayout [names ["A", "B"]] blocks fooBlocks]
  [valid_jumps Foo.validJumps]
end Foo.Listing
```

* The file is read relative to the directory of the Lean file (as `include_str` does), and its
  SHA-256 must be the one written in the source: Lake does not know the hex file is an input,
  so the hash pins its content in the reviewed source, and changing the file means changing the
  source, which rebuilds the module.  On a mismatch the error prints the actual hash.
  (`scripts/check_listing_hashes.py` checks every listing's hash without Lean, as CI does: an
  edited hex file with up-to-date `.olean`s is otherwise only noticed by a clean build.)
* `bytes` (the code, immutable sites zeroed) and `table` (`cut 0` of `scan 0 bytes`, the pushes
  at immutable sites replaced by `.immutable i`) are computed by running `Reasoning.Listing.scan`
  and `cut` at elaboration time and are added as closed literal terms, built as `Expr`s: the
  same constants (`Instr.op`, the `Operation` abbreviations such as `Operation.JUMPDEST`, `OfNat`
  numerals) as the elaborated text of a generated listing, without its `let`s.  `bytes` is
  compiled (the bytecode constant runs in the differential tests); `table` is not (only the
  kernel reduces it; its compiled code was most of a large listing's `.olean`).
* Every other declaration is elaborated from the same Lean text `gen_listing.py` writes
  (`sections_eq … := by decide +kernel`, `listing_tree tree from table`, `code_check`,
  `decodes_code`, …), so names, statements and proofs are those of a generated listing.
  Nothing computed here is trusted: the kernel checks `sections bytes = table.erase`.

Options:

* `bytecode C`: the full name of the bytecode constant, defined as `⟨bytes.toArray⟩`.
* `creation`: only the doc strings change ("creation bytecode").
* `followed_by x`: the code runs followed by arbitrary data (creation code and its constructor
  arguments, a Vyper runtime and its immutables' data section); the theorems are stated over
  `C ++ x` for any `x`, with `lim` and, when the code ends in a push cut short, `decodes_last`
  (`Reasoning/Listing/Tail.lean`).  No immutables.
* `layout L … blocks B`: solc immutables.  The sites are those of the layout term `L : Layout`,
  read by evaluating `L.sites` (each `(offset, 32, key)`, `offset` the first data byte of a
  `PUSH32`).  Immutable `i` of the table is the `i`-th key in order of first appearance among the
  sites, or the `i`-th of `names [...]`.  The layout facts (`immutableTemplate_size`,
  `immutableLayout_sites`, `immutableLayout_inBounds`, `immutableTemplate_size64`,
  `immutableRuntime_size`) are added in namespace `B` (a full name, from the root).  The site
  bytes of the file are zeroed.
* `valid_jumps N`: the `@[valid_jumps]` theorem `N` (`Reasoning/Listing/JumpTable.lean`).

`#print_listing T` prints a table constant `T` one instruction per line with its offset, as the
generated text showed it, read from the constant's term.
-/

open Lean Elab Command Meta Ethereum Ethereum.EVM

set_option autoImplicit false

deriving instance ToExpr for Ethereum.Operation.SAOp
deriving instance ToExpr for Ethereum.Operation.CBLOp
deriving instance ToExpr for Ethereum.Operation.KOp
deriving instance ToExpr for Ethereum.Operation.EOp
deriving instance ToExpr for Ethereum.Operation.BOp
deriving instance ToExpr for Ethereum.Operation.SMSFOp
deriving instance ToExpr for Ethereum.Operation.POp
deriving instance ToExpr for Ethereum.Operation.DOp
deriving instance ToExpr for Ethereum.Operation.ExOp
deriving instance ToExpr for Ethereum.Operation.LOp
deriving instance ToExpr for Ethereum.Operation.SOp
deriving instance ToExpr for Ethereum.Operation

namespace Reasoning.Listing.FromHex

/-! ## Terms -/

/-- The term of an operation as a listing's text elaborates it: the abbreviation
`Ethereum.Operation.<NAME>` (`.JUMPDEST`), whose value is the constructor term. -/
def opExpr (env : Environment) (o : Operation) : Except String (Name × Expr) := do
  let rawE := toExpr o
  let args := rawE.getAppArgs
  if h : args.size = 1 then
    if let .const sub _ := args[0] then
      let short := sub.getString!
      let abbr := `Ethereum.Operation ++ Name.mkSimple short
      if let some (.defnInfo d) := env.find? abbr then
        if d.value == rawE then return (Name.mkSimple short, mkConst abbr)
  throw s!"no `Ethereum.Operation` abbreviation for {rawE}"

/-- The term of an instruction. -/
def instrExpr (env : Environment) : Instr → Except String Expr
  | .op o => return mkApp (mkConst ``Instr.op) (← opExpr env o).2
  | .push o v => return mkApp2 (mkConst ``Instr.push) (← opExpr env o).2 (mkNatLit v)
  | .immutable i => return mkApp (mkConst ``Instr.immutable) (mkNatLit i)

/-- The elements `xs[lo:hi]` consed onto `tail`.  Runs of 64 or more are split in two and
the second half bound by a `let`, as Lean's own list literal notation does for long lists, so
that the term is shallow (a 16 K element `List.cons` chain is too deep for the code generator).
`tail` occurs only in the value of the outermost `let`, never under a binder. -/
partial def chunked (ty : Expr) (xs : Array Expr) (lo hi : Nat) (tail : Expr) : Expr :=
  if hi - lo < 64 then
    (List.range' lo (hi - lo)).foldr
      (fun k acc => mkApp3 (mkConst ``List.cons [levelZero]) ty xs[k]! acc) tail
  else
    let mid := (lo + hi) / 2
    .letE `y (mkApp (mkConst ``List [levelZero]) ty) (chunked ty xs mid hi tail)
      (chunked ty xs lo mid (.bvar 0)) true

/-- A list literal `[x₀, …]` of element type `ty` (`nilTy` for its `List.nil`). -/
def listExpr (ty : Expr) (xs : Array Expr) (nilTy : Expr := ty) : Expr :=
  chunked ty xs 0 xs.size (mkApp (mkConst ``List.nil [levelZero]) nilTy)

def bytesExpr (bs : Array UInt8) : Expr :=
  listExpr (mkConst ``UInt8) (bs.map toExpr)

def tableExpr (env : Environment) (t : Table) : Except String Expr := do
  -- type arguments: `Nat × Section` for the elements, `Nat × List Instr` for the final
  -- `List.nil`, as mostly in the elaborated text (which mixes the two; `Section` is an `abbrev`)
  let instrTy := mkConst ``Instr
  let secTy := mkConst ``Section
  let pair (s : Expr) := mkApp2 (mkConst ``Prod [levelZero, levelZero]) (mkConst ``Nat) s
  let mut out : Array Expr := Array.mkEmpty t.length
  for (pc, s) in t do
    let mut is : Array Expr := Array.mkEmpty s.length
    for i in s do is := is.push (← instrExpr env i)
    out := out.push (mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) (mkConst ``Nat) secTy
      (mkNatLit pc) (listExpr instrTy is))
  return listExpr (pair secTy) out (pair (mkApp (mkConst ``List [levelZero]) instrTy))

/-! ## The listing -/

/-- The bytes of a hex file: whitespace around it and a `0x` prefix are allowed. -/
def parseHex (s : String) : Except String (Array UInt8) := do
  let s := s.trimAscii.toString
  let s := if s.startsWith "0x" then (s.drop 2).toString else s
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw s!"not a hex digit: {repr c}"
  let cs := s.toList.toArray
  unless cs.size % 2 = 0 do throw "odd number of hex digits"
  let mut out : Array UInt8 := Array.mkEmpty (cs.size / 2)
  for k in [0:cs.size / 2] do
    out := out.push (16 * (← digit cs[2 * k]!) + (← digit cs[2 * k + 1]!)).toUInt8
  return out

/-- The listing of `code` whose immutable sites are `sites` (data offset, immutable number):
the code with the site bytes zeroed, and its table, from `scan` and `cut`. -/
def listing (code : Array UInt8) (sites : List (Nat × Nat)) :
    Except String (Array UInt8 × Table) := do
  let mut bs := code
  for (off, _) in sites do
    unless 1 ≤ off ∧ off + 32 ≤ bs.size do throw s!"immutable site {off}: outside the code"
    for k in [off:off + 32] do bs := bs.set! k 0
  let mut out : Array Instr := #[]
  let mut pc := 0
  let mut used : List Nat := []
  for i in scan 0 bs.toList do
    match sites.lookup (pc + 1) with
    | some n =>
      unless i.opn = .PUSH32 ∧ pc + 33 ≤ bs.size do
        throw s!"immutable site {pc + 1}: not the data of a full PUSH32"
      out := out.push (.immutable n)
      used := (pc + 1) :: used
    | none => out := out.push i
    pc := pc + i.width
  for (off, _) in sites do
    unless used.contains off do throw s!"immutable site {off}: not at an instruction's data"
  return (bs, cut 0 out.toList)

private unsafe def evalSitesUnsafe (e : Expr) : TermElabM (List (Nat × Nat × String)) :=
  Meta.evalExpr (List (Nat × Nat × String)) (toTypeExpr (List (Nat × Nat × String))) e

/-- The value of a closed term of type `List (Nat × Nat × String)`, by evaluation (only to
find the sites; the kernel checks the layout against the table in `code_check`). -/
@[implemented_by evalSitesUnsafe]
private opaque evalSites (e : Expr) : TermElabM (List (Nat × Nat × String))

/-! ## The text of the other declarations -/

/-- A Lean string literal. -/
def strLit (s : String) : String := (toString (repr s))

/-- The declarations after `table`, as `gen_listing.py` writes them. -/
def declTexts (qual : String) (creation : Bool) (tail : Option String) (names : List String)
    (layout blocks : String) (sites : List (Nat × Nat × String)) (validJumps : Option String)
    (size : Nat) (table : Table) : List String := Id.run do
  let what := if creation then "creation bytecode" else "runtime bytecode"
  let constDoc := if names.isEmpty then
      s!"/-- The {what}, as the byte array the block summaries and the proofs name. -/"
    else
      s!"/-- The {what}, as the byte array the block summaries and the proofs name (for a contract with\nimmutables: the template, zeros at the immutable sites). -/"
  let mut out : List String := [
    s!"{constDoc}\ndef _root_.{qual} : ByteArray := ⟨bytes.toArray⟩",
    "/-- The per-contract check: the bytes decode to the table, immutables erased. -/\ntheorem sections_eq : sections bytes = table.erase := by decide +kernel",
    "/-- Side check: every immutable is a full `PUSH32`. -/\ntheorem fits_eq : fits (join table) bytes.length = true := by decide +kernel",
    "/-- Side check: offsets are words. -/\ntheorem small : bytes.length < 2 ^ 256 := by decide +kernel",
    "theorem check : Checked bytes table := ⟨sections_eq, fits_eq, small⟩",
    "listing_tree tree from table",
    "theorem tree_get (t : Nat) : tree.get? t = table.lookup t :=\n  Tree.get?_eq_lookup tree_flat check.ascending t"]
  if let some vj := validJumps then
    out := out ++ [s!"/-- Membership in the bytecode's `JUMPDEST` set is a lookup in `tree`: the rewrite the
`jump_dest` tactic (`Reasoning/JumpDest.lean`) uses. -/
@[valid_jumps] theorem _root_.{vj} (t : UInt256) :
    (D_J {qual} 0).contains t = ((tree.get? t.toNat).map startsJD).getD false :=
  check.contains_eq tree_get t"]
  let zero := "(fun _ => ⟨0⟩)"
  match tail with
  | some x =>
    let lim := (table.find? fun (off, s) => off + sectionWidth s > size).map (·.1) |>.getD (size + 1)
    let last := (table.lookup lim).map (·.length - 1)
    out := out ++ [
      s!"/-- The bytecode is the listing's bytes, and the table has no immutable. -/
theorem code_check :
    plainCheck {qual}.data.toList bytes table = true := by
  decide +kernel",
      s!"theorem code_eq :
    {qual} = filled bytes {zero} table :=
  eq_filled code_check _",
      s!"/-- Sections before this offset end inside the code (a final push cut short by the end of
the code would read the appended bytes; its section is left out). -/
def lim : Nat := {lim}",
      "theorem inside : insideCheck table bytes.length lim = true := by decide +kernel",
      "theorem small64 : bytes.length < 2 ^ 64 := by decide +kernel",
      s!"/-- A section the tree returns decodes, at its offset, on the code followed by any `{x}`. -/
theorem decodes_code ({x} : ByteArray) \{t : Nat} \{s : Section} (h : tree.get? t = some s)
    (ht : t < lim := by decide) :
    Decodes ({qual} ++ {x}) {zero} t s :=
  code_eq ▸ check.decodes_append {zero} {x} inside small64 (tree_get t ▸ h) ht",
      s!"/-- An offset where the tree has a section that begins with `JUMPDEST` is a valid jump
destination of the code followed by any `{x}`. -/
theorem jumpdest_code ({x} : ByteArray) \{t : Nat} \{s : Section} (h : tree.get? t = some s)
    (hjd : startsJD s = true) (ht : t < 2 ^ 256 := by decide) :
    (D_J ({qual} ++ {x}) 0).contains (UInt256.ofNat t) = true :=
  code_eq ▸ check.jumpdest_append {zero} {x} ht (mem_of_lookup (tree_get t ▸ h)) hjd"]
    if let some last := last then
      let sec := "((tree.get? lim).getD [])"
      out := out ++ [
        s!"/-- The section at `lim`, whose last push is cut short by the end of the code. -/
theorem last_section : tree.get? lim = some {sec} := by decide +kernel",
        s!"theorem bytes_length : bytes.length = {size} := by decide +kernel",
        s!"/-- Its {last} whole instructions decode on the code followed by any `{x}`. -/
theorem decodes_last ({x} : ByteArray) :
    Decodes ({qual} ++ {x}) {zero} lim ({sec}.take {last}) :=
  code_eq ▸ check.decodes_append_take {zero} {x} small64 (tree_get lim ▸ last_section)
    {last} bytes_length (by decide +kernel)"]
  | none =>
    let (binder, code, sigma, arg) :=
      if names.isEmpty then ("", qual, zero, "")
      else ("(immWords : String → UInt256) ", s!"({layout}.runtime {qual} immWords)",
        "(immσ names immWords)", " immWords")
    if names.isEmpty then
      out := out ++ [
        s!"/-- The bytecode is the listing's bytes, and the table has no immutable. -/
theorem code_check :
    plainCheck {qual}.data.toList bytes table = true := by
  decide +kernel",
        s!"/-- The code of the block summaries is the listing's filled code. -/
theorem code_eq :
    {code} = filled bytes {sigma} table :=
  eq_filled code_check _"]
    else
      let nameList := "[" ++ ", ".intercalate (names.map strLit) ++ "]"
      out := out ++ [
        s!"/-- The layout key of each immutable, by its number in the table. -/
def names : List String := {nameList}",
        s!"/-- The template and the layout's sites agree with the listing. -/
theorem code_check :
    codeCheck {layout}.sites {qual}.data.toList bytes table
      {nameList} = true := by
  decide +kernel",
        s!"/-- The code of the block summaries is the listing's filled code. -/
theorem code_eq {binder}:
    {code} = filled bytes {sigma} table :=
  runtime_eq_filled code_check immWords"]
    out := out ++ [
      s!"/-- A section the tree returns decodes, at its offset, on the code of the block summaries. -/
theorem decodes_code {binder}\{t : Nat} \{s : Section} (h : tree.get? t = some s) :
    Decodes {code} {sigma} t s :=
  code_eq{arg} ▸ check.decodes_lookup {sigma} (tree_get t ▸ h)",
      s!"/-- An offset where the tree has a section that begins with `JUMPDEST` is a valid jump
destination of the code of the block summaries. -/
theorem jumpdest_code {binder}\{t : Nat} \{s : Section} (h : tree.get? t = some s)
    (hjd : startsJD s = true) (ht : t < 2 ^ 256 := by decide) :
    (D_J {code} 0).contains (UInt256.ofNat t) = true :=
  code_eq{arg} ▸ (check.jumpdest_iff_nat {sigma} ht).mpr ⟨s, mem_of_lookup (tree_get t ▸ h), hjd⟩"]
    unless names.isEmpty do
      let siteList := "[" ++ ", ".intercalate (sites.map fun (o, l, k) => s!"({o}, {l}, {strLit k})") ++ "]"
      let b := s!"_root_.{blocks}"
      out := out ++ [
        s!"/-- The template's size. -/
theorem {b}.immutableTemplate_size : {qual}.size = {size} := by
  show {qual}.data.toList.length = {size}
  decide +kernel",
        s!"theorem {b}.immutableLayout_sites :
    {layout}.sites = {siteList} := by decide",
        s!"theorem {b}.immutableLayout_inBounds :
    {layout}.inBounds {qual} = true := by
  simp only [Layout.inBounds, {b}.immutableTemplate_size, {b}.immutableLayout_sites]
  decide",
        s!"theorem {b}.immutableTemplate_size64 :
    {qual}.size < 2 ^ 64 := by
  rw [{b}.immutableTemplate_size]; decide",
        s!"theorem {b}.immutableRuntime_size (immWords : String → Ethereum.UInt256) :
    ({layout}.runtime {qual} immWords).size = {qual}.size := by
  exact Layout.runtime_size_of_bounds {b}.immutableLayout_inBounds"]
  return out

/-- Every position of `stx` replaced by `info` (the command's, marked synthetic), so that
messages and go-to-definition point at the command, not into the generated text. -/
partial def setInfo (info : SourceInfo) : Syntax → Syntax
  | .node _ k args => .node info k (args.map (setInfo info))
  | .atom _ v => .atom info v
  | .ident _ rawE n pre => .ident info rawE n pre
  | .missing => .missing

/-- Elaborate one command given as text, in the scope of the opens the text assumes. -/
def elabText (ref : Syntax) (text : String) : CommandElabM Unit := do
  let full := "open Ethereum Ethereum.EVM Reasoning.Listing Reasoning.Immutables in\n" ++ text
  match Parser.runParserCategory (← getEnv) `command full "<listing_from_hex>" with
  | .error e => throwErrorAt ref "listing_from_hex: internal error, generated text does not parse: {e}\n{full}"
  | .ok stx =>
    let stx := setInfo (SourceInfo.fromRef ref (canonical := false)) stx
    elabCommand stx

/-- Add a closed definition with a doc string; with `compile`, compiled like a `def`. -/
def addLiteral (ref : Syntax) (name : Name) (type value : Expr) (doc : String)
    (compile : Bool) : CommandElabM Unit :=
  withScope (fun sc => { sc with opts := maxRecDepth.set sc.opts 100000 }) <| liftTermElabM do
    let env ← getEnv
    let decl := Declaration.defnDecl <| mkDefinitionValEx name [] type value
      (.regular (getMaxHeight env value + 1)) .safe [name]
    addDecl decl
    -- the code generator recurses along the term's `let`s: `maxRecDepth` is raised for it
    -- (above), as a generated listing's text did with `set_option`
    if compile then compileDecl decl
    addDocStringCore name doc
    addDeclarationRangesFromSyntax name ref

syntax (name := listingFromHex) "listing_from_hex " str &" sha256 " str
  &" bytecode " ident (&" creation")? (&" followed_by " ident)?
  (&" layout " ident (&" names " "[" str,* "]")? &" blocks " ident)?
  (&" valid_jumps " ident)? : command

@[command_elab listingFromHex] def elabListingFromHex : CommandElab := fun stx => do
  let `(listing_from_hex $file:str sha256 $hash:str bytecode $qual:ident $[creation%$cr]?
      $[followed_by $tail?:ident]? $[layout $layout?:ident $[names [$names?,*]]? blocks $blocks?:ident]?
      $[valid_jumps $vj?:ident]?) := stx | throwUnsupportedSyntax
  -- the file, pinned by its hash
  let srcPath := System.FilePath.mk (← getFileName)
  let some srcDir := srcPath.parent | throwError "cannot compute the parent directory of `{srcPath}`"
  let path := srcDir / file.getString
  let rawE ← try IO.FS.readBinFile path catch e => throwErrorAt file "listing_from_hex: cannot read `{path}`: {e.toMessageData}"
  let actual := sha256Hex rawE
  unless actual == hash.getString.trimAscii.toString.toLower do
    throwErrorAt hash "listing_from_hex: the SHA-256 of `{path}` is\n  {actual}\nnot the one written here; if the new content is intended, write that hash"
  let some text := String.fromUTF8? rawE | throwErrorAt file "listing_from_hex: `{path}` is not UTF-8"
  let code ← match parseHex text with
    | .ok c => pure c
    | .error e => throwErrorAt file "listing_from_hex: `{path}`: {e}"
  -- the immutables: the layout's sites, by evaluation
  let mut sites : List (Nat × Nat × String) := []
  let mut names : List String := []
  let mut layoutStr := ""
  let mut blocksStr := ""
  if let some l := layout? then
    if tail?.isSome then throwErrorAt l "listing_from_hex: `layout` and `followed_by` do not combine"
    let lname ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
    layoutStr := toString lname
    blocksStr := toString (blocks?.get!.getId)
    sites ← liftTermElabM <| evalSites (mkApp (mkConst ``Reasoning.Immutables.Layout.sites) (mkConst lname))
    for (_, len, key) in sites do
      unless len = 32 do throwErrorAt l "listing_from_hex: site of `{key}` of length {len}, not 32"
      unless names.contains key do names := names ++ [key]
    if let some ns := names?.join then
      let given := ns.getElems.toList.map (·.getString)
      for k in names do
        unless given.contains k do throwErrorAt l "listing_from_hex: `names` lacks the layout key {k}"
      names := given
    if sites.isEmpty then throwErrorAt l "listing_from_hex: the layout has no sites"
  let numbered := sites.map fun (off, _, key) => (off, names.idxOf key)
  let (bytes, table) ← match listing code numbered with
    | .ok r => pure r
    | .error e => throwErrorAt file "listing_from_hex: {e}"
  -- `bytes` and `table`, as literal terms
  let ns ← getCurrNamespace
  let env ← getEnv
  -- `bytes` is compiled: the bytecode constant `⟨bytes.toArray⟩` runs (the differential tests).
  -- `table` is not: only the kernel reduces it, and `#print_listing` reads its term.
  addLiteral stx (ns ++ `bytes) (mkApp (mkConst ``List [levelZero]) (mkConst ``UInt8))
    (bytesExpr bytes) "The bytecode (for solc immutables the template: immutable sites hold zeros). "
    (compile := true)
  let tableE ← match tableExpr env table with
    | .ok e => pure e
    | .error e => throwError "listing_from_hex: {e}"
  addLiteral stx (ns ++ `table) (mkConst ``Table) tableE "The sections, by offset. "
    (compile := false)
  -- everything else, from the text a generated listing has
  let texts := declTexts (toString qual.getId) cr.isSome (tail?.map (toString ·.getId)) names
    layoutStr blocksStr sites (vj?.map (toString ·.getId)) bytes.size table
  for t in texts do elabText stx t

/-! ## Seeing a listing -/

/-- A natural number literal, raw or as an `OfNat` numeral. -/
def natLit? (e : Expr) : Option Nat :=
  let lit (e : Expr) : Option Nat := match e.consumeMData with
    | .lit (.natVal n) => some n
    | _ => none
  let e := e.consumeMData
  if e.isAppOfArity ``OfNat.ofNat 3 then lit (e.getArg! 1) else lit e

/-- One line of an instruction term of a table (`Instr.op`, `Instr.push`, `Instr.immutable`
applied to an `Ethereum.Operation` abbreviation and literals), and its width in bytes. -/
def renderInstr (e : Expr) : String × Nat :=
  let e := e.consumeMData
  let opName (o : Expr) : String :=
    match o.consumeMData with
    | .const n _ => n.lastComponentAsString
    | _ => "?"
  let pushWidth (s : String) : Nat :=
    if s.startsWith "PUSH" then ((s.drop 4).toString.toNat?.getD 0) else 0
  if e.isAppOfArity ``Instr.op 1 then
    let s := opName e.appArg!
    (s, 1 + pushWidth s)
  else if e.isAppOfArity ``Instr.push 2 then
    let s := opName e.appFn!.appArg!
    let v := match natLit? e.appArg! with
      | some v => s!"0x{String.ofList (Nat.toDigits 16 v)}"
      | none => "?"
    (s!"{s} {v}", 1 + pushWidth s)
  else if e.isAppOfArity ``Instr.immutable 1 then
    (s!"PUSH32 <immutable {(natLit? e.appArg!).getD 0}>", 33)
  else ("?", 1)

/-- `#print_listing T`: the table constant `T` (a listing's `table`), one instruction per line
(offset, operation, immediate), sections separated by a blank line.  The table is read from
its term (it has no compiled code). -/
syntax (name := printListing) "#print_listing " ident : command

@[command_elab printListing] def elabPrintListing : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some c := (← getEnv).find? n | throwError "#print_listing: unknown constant {n}"
  let some v := c.value? | throwError "#print_listing: {n} has no value"
  let out ← liftTermElabM do
    let mut out := ""
    for p in ← Reasoning.Listing.listElems v #[] do
      let p := p.consumeMData
      unless p.isAppOfArity ``Prod.mk 4 do throwError "#print_listing: not a table entry: {p}"
      let some off := natLit? (p.getArg! 2) | throwError "#print_listing: not an offset: {p.getArg! 2}"
      let mut pc := off
      for i in ← Reasoning.Listing.listElems (p.getArg! 3) #[] do
        let (line, w) := renderInstr i
        out := out ++ s!"{pc}\t{line}\n"
        pc := pc + w
      out := out ++ "\n"
    return out
  logInfo out

end Reasoning.Listing.FromHex
