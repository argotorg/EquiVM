import Solm

/-!
# TinyImmutable immutable values, offset table, and `runtimeCodeOf`

This is the smallest UniswapV3-style immutable example in `Examples`: solc emits the deployed
runtime as a template with 32 zero bytes at every immutable reference, and the constructor patches
those words before returning the runtime.

The offsets below are from solc `0.8.35` standard JSON
`evm.deployedBytecode.immutableReferences` for `TinyImmutable.sol`, optimizer enabled with
800 runs, EVM version Shanghai, and `metadata.bytecodeHash: none`.
-/

open Solm ABI

namespace TinyImmutable.Immutables

/-- Constructor-set immutable values for the tiny example. -/
structure TinyImmutables where
  owner : EVM.Address
  scale : EVM.Word

/-- An address value as an `Expr` literal. -/
def addrLit (a : EVM.Address) : Expr :=
  .cast (.intLit (Int.ofNat a.toNat)) (.elem .address)

variable (v : TinyImmutables)

def owner : Expr := addrLit v.owner
def scale : Expr := .intLit (Int.ofNat v.scale.toNat)

/-- solc `immutableReferences` offsets, keyed by the constructor locals `imm_<name>`. -/
def offsets : List (Ident × List Nat) :=
  [ ("imm_scale", [186, 361]),
    ("imm_owner", [72, 245]) ]

/-- The immutable values as Solm `Value`s under the `imm_<name>` keys. -/
def immValues (v : TinyImmutables) : List (Ident × Value) :=
  [ ("imm_owner", .address v.owner),
    ("imm_scale", .int (Int.ofNat v.scale.toNat)) ]

/-- A `Value`'s 32-byte word (big-endian), as `valueToWord` computes it. -/
def wordBytes? (v : Value) : Option ByteArray :=
  (valueToWord v).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

/-- Build the `(offset, 32-byte word)` patch list by looking each `imm_<name>` up via `get`. -/
def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let v ← get p.1
    let bytes ← wordBytes? v
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

/-- The patch list for a concrete immutable assignment. -/
def patches (v : TinyImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

/-- `runtimeCodeOf` for the parameterized constructor relation. -/
def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end TinyImmutable.Immutables
