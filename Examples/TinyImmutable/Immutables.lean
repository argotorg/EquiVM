import Solm
import Reasoning.PatchRuntime

/-!
# TinyImmutable immutable values and offset table

This is the smallest UniswapV3-style immutable example in `Examples`: solc emits the deployed
runtime as a template with 32 zero bytes at every immutable reference, and the constructor patches
those words before returning the runtime.

The offsets below are from solc `0.8.35` standard JSON
`evm.deployedBytecode.immutableReferences` for `TinyImmutable.sol`, optimizer enabled with
800 runs, EVM version Shanghai, and `metadata.bytecodeHash: none`.
-/

open Solm ABI

namespace TinyImmutable.Immutables

/-- A valuation of the tiny example's immutables (as the EVM-side proofs consume them). -/
structure TinyImmutables where
  owner : EVM.Address
  scale : EVM.Word

/-- One source for each immutable's name, summary key, and solc patch offsets. -/
def immutableReferences : List (Ident × String × List Nat) :=
  [ ("scale", "scale", [186, 361]),
    ("owner", "owner", [72, 245]) ]

/-- solc `immutableReferences` offsets, keyed by immutable name. -/
def offsets : List (Ident × List Nat) :=
  immutableReferences.map (fun (name, _, sites) => (name, sites))

/-- The immutable values as Solm `Value`s under their names. -/
def immValues (v : TinyImmutables) : List (Ident × Value) :=
  [ ("owner", .address v.owner),
    ("scale", .int (Int.ofNat v.scale.toNat)) ]

/-- A `Value`'s 32-byte word (big-endian), as `valueToWord` computes it. -/
def wordBytes? (v : Value) : Option ByteArray :=
  (valueToWord v).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

/-- Build the `(offset, 32-byte word)` patch list by looking each immutable up via `get`. -/
def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let v ← get p.1
    let bytes ← wordBytes? v
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

/-- The patch list for a concrete immutable assignment. -/
def patches (v : TinyImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

end TinyImmutable.Immutables
