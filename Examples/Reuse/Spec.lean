import Solm.Semantics
import Solm.SolidityLayout

/-!
# Reuse — Solm spec for `C.sol`

Scenario: a `public` function `f` that is **also** called internally by `g`.  `lookupCallable?`
searches `functions` then `transitions`, so modelling `f` as a `TransitionDecl` (its external ABI
entry) lets `g`'s `internalCall "f"` resolve it — matching the bytecode, where solc emits `f`'s body
once as a shared routine reached from both the external dispatcher and `g`'s internal `JUMP`.

This is spec-level data only (the bytecode and proof live in `Bytecode.lean` / `Correct.lean`).

`f` returns `v * 2 + 1`, which solc compiles with *checked* `mul`/`add` (reverts on overflow).
Solm's arithmetic is unbounded `Int`, so the return expression is range-checked back into
`uint256` to model Solidity's checked-arithmetic revert.
-/

open Solm ABI

namespace Reuse

/-- The Solm/ABI `uint256` element and type. -/
def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)

/-- Storage location of the single scalar slot `s` (slot 0, full word). -/
def sLoc : StorageLoc :=
  { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

/-- `s` storage reference. -/
def sRef : StorageRef := { base := "s" }

/-- `f(uint256 v) → uint256`, returning `v * 2 + 1`.  External ABI entry *and* internal call target. -/
def fTransition : TransitionDecl :=
  { name := "f"
    params := [{ name := "v", ty := uint256 }]
    returnType := [uint256]
    body :=
      [ -- non-payable guard (mirrors solc's global `CALLVALUE; ISZERO; …` prologue)
        .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.inRange uint256Int
          (.binary .add (.binary .mul (.var "v") (.intLit 2)) (.intLit 1)))] ] }

/-- `g(uint256 v) external { s = f(v); }` — invokes `f` as an **internal call**, then stores. -/
def gTransition : TransitionDecl :=
  { name := "g"
    params := [{ name := "v", ty := uint256 }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .internalCall "f" [.var "v"] "r",
        .assign .storage sRef (.var "r") ] }

/-- The `C` contract: one scalar storage word, no constructor body, two transitions (`f`, `g`). -/
def cContract : ContractDecl :=
  { name := "C"
    storage := [{ name := "s", ty := .elem (.int uint256Int) }]
    ctor := { params := [], body := [] }
    transitions := [fTransition, gTransition] }

end Reuse

/-- Verification config: `s` at slot 0, default external-call ABI. -/
def cConfig : Config :=
  { storage :=
      { layout := fun ref =>
          match ref.base, ref.steps with
          | "s", [] => fun _ => some Reuse.sLoc
          | _, _ => fun _ => none }
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment Reuse.cContract.ctor.params }
