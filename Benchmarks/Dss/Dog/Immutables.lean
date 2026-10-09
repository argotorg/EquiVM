import Solm
import Reasoning.SolmBody
import Reasoning.BytecodePatching
import Reasoning.Immutables

/-!
# MakerDAO/Sky DSS Dog immutable values and offset table

`runtime.hex` is solc's optimized, metadata-free runtime template for `dss/src/dog.sol`.
The constructor patches the immutable `vat` address at the offsets below, re-derived from
standard-JSON `evm.deployedBytecode.immutableReferences` for solc `0.6.12`, optimizer runs 200,
and `metadata.bytecodeHash = "none"`.
-/

open Solm ABI

namespace Benchmarks.Dss.Dog.Immutables

structure DogImmutables where
  vat : EVM.Address

variable (v : DogImmutables)

/-- The immutable `vat`, read from the deployed contract's immutables. -/
def vatExpr : Expr := .immutable "vat"

/-- The immutables a contract deployed with `v` runs with. -/
def immStore (v : DogImmutables) : Store :=
  (∅ : Store).insert "vat" (.address v.vat)

def offsets : List (Ident × List Nat) :=
  [("vat", [1405, 2890, 3170, 3965])]

/-- The constructor's immutable offsets as a layout for generated runtime summaries. -/
def immutableLayout : Reasoning.Immutables.Layout :=
  ⟨offsets.flatMap fun (key, sites) => sites.map fun off => (off, 32, key)⟩

def immValues (v : DogImmutables) : List (Ident × Value) :=
  [("vat", .address v.vat)]

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← Reasoning.Theory.wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : DogImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

end Benchmarks.Dss.Dog.Immutables
