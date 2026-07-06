import Solm

/-!
# MakerDAO/Sky DSS Dog immutable values, offset table, and `runtimeCodeOf`

`runtime.hex` is solc's optimized, metadata-free runtime template for `dss/src/dog.sol`.
The constructor patches the immutable `vat` address at the offsets below, re-derived from
standard-JSON `evm.deployedBytecode.immutableReferences` for solc `0.6.12`, optimizer runs 200,
and `metadata.bytecodeHash = "none"`.

Convention: the Solm constructor binds `vat_` as local `imm_vat`; `runtimeCodeOf` reads that local,
converts it to a 32-byte word, and patches the runtime template.
-/

open Solm ABI

namespace Benchmarks.Dss.Dog.Immutables

structure DogImmutables where
  vat : EVM.Address

def addrLit (a : EVM.Address) : Expr :=
  .cast (.intLit (Int.ofNat a.toNat)) (.elem .address)

variable (v : DogImmutables)

def vatExpr : Expr := addrLit v.vat

def offsets : List (Ident × List Nat) :=
  [("imm_vat", [1405, 2890, 3170, 3965])]

def immValues (v : DogImmutables) : List (Ident × Value) :=
  [("imm_vat", .address v.vat)]

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : DogImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.Dss.Dog.Immutables
