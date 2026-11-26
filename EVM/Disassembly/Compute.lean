import EVM.Disassembly.Tree
import Lean.ToExpr
import Lean.Elab.Deriving.ToExpr

/-!
# Computing the sections

A bytecode file computes its sections when it is elaborated, with Mathlib's `eval%`:

```
noncomputable def tree : Tree := eval% Tree.ofSections (sectionsOf fooBytecode [])
```

`sectionsOf` returns the same sections as `disassemble` but is written to run fast in the
interpreter, and `Tree.ofSections` builds a balanced tree from them. The `ToExpr` instances are
what `eval%` needs to turn the result into a term.

None of this is trusted: the bytecode file checks the result against `disassemble` in the kernel.
-/

open Ethereum Ethereum.EVM Lean

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

/-- Uses the abbreviations of `Ethereum.Operation`, e.g. `Operation.JUMPDEST` rather than
`.StackMemFlow .JUMPDEST`. -/
instance : ToExpr Ethereum.Operation where
  toExpr o :=
    let abbr (e : Expr) : Expr := mkConst (`Ethereum.Operation ++ Name.mkSimple e.constName!.getString!)
    match o with
    | .StopArith x => abbr (toExpr x)
    | .CompBit x => abbr (toExpr x)
    | .Keccak x => abbr (toExpr x)
    | .Env x => abbr (toExpr x)
    | .Block x => abbr (toExpr x)
    | .StackMemFlow x => abbr (toExpr x)
    | .Push x => abbr (toExpr x)
    | .Dup x => abbr (toExpr x)
    | .Exchange x => abbr (toExpr x)
    | .Log x => abbr (toExpr x)
    | .System x => abbr (toExpr x)
  toTypeExpr := mkConst ``Ethereum.Operation

namespace EVM.Disassembly

deriving instance ToExpr for Instr
deriving instance ToExpr for Tree

/-- Decodes `code` from offset `pc` on, appending to `acc`. A `PUSH32` whose immediate starts at one
of the `sites` becomes an immutable. -/
partial def instrsFrom (code : Array UInt8) (sites : List (Nat × Nat)) (pc : Nat)
    (acc : Array (Nat × Instr)) : Array (Nat × Instr) :=
  if h : pc < code.size then
    let o := (parseInstr code[pc]).getD .INVALID
    let w := argOnNBytesOfInstr o
    let i : Instr :=
      if w = 0 then .op o
      else match sites.lookup (pc + 1) with
        | some n => .immutable n
        | none => .push o (fromBytesBigEndian (immediate w (code.extract (pc + 1) (pc + 1 + w)).toList))
    instrsFrom code sites (pc + 1 + w) (acc.push (pc, i))
  else acc

/-- The sections of `code`, with the pushes at `sites` as immutables. -/
def sectionsOf (code : ByteArray) (sites : List (Nat × Nat)) :
    List (Nat × List Instr) := Id.run do
  let mut out : Array (Nat × List Instr) := #[]
  let mut cur : Option (Nat × Array Instr) := none
  for (pc, i) in instrsFrom code.data sites 0 #[] do
    match cur with
    | some (o, is) =>
      if i.isJumpdest then
        out := out.push (o, is.toList)
        cur := some (pc, #[i])
      else cur := some (o, is.push i)
    | none => cur := some (pc, #[i])
  if let some (o, is) := cur then out := out.push (o, is.toList)
  return out.toList

/-- A balanced tree of `xs[lo:hi]`. -/
def Tree.ofArray (xs : Array (Nat × List Instr)) (lo hi : Nat) : Tree :=
  if lo < hi then
    .node (Tree.ofArray xs lo ((lo + hi) / 2)) xs[(lo + hi) / 2]!
      (Tree.ofArray xs ((lo + hi) / 2 + 1) hi)
  else .empty
termination_by hi - lo

/-- A balanced tree of the sections. -/
def Tree.ofSections (t : List (Nat × List Instr)) : Tree :=
  let xs := t.toArray
  Tree.ofArray xs 0 xs.size

end EVM.Disassembly
