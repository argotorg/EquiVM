import Solm

/-!
# MakerDAO/Sky DSS Clipper immutable values, offset table, and `runtimeCodeOf`

`runtime.hex` is solc's optimized, metadata-free runtime template for `dss/src/clip.sol`.
The constructor patches immutable `ilk` and `vat` values at the offsets below, re-derived from
standard-JSON `evm.deployedBytecode.immutableReferences` for solc `0.6.12`, optimizer runs 200,
and `metadata.bytecodeHash = "none"`.
-/

open Solm ABI

namespace Benchmarks.Dss.Clipper.Immutables

structure ClipperImmutables where
  ilk : Value
  vat : EVM.Address

def addrLit (a : EVM.Address) : Expr :=
  .cast (.intLit (Int.ofNat a.toNat)) (.elem .address)

variable (v : ClipperImmutables)

def ilkExpr : Expr :=
  match v.ilk with
  | .fixedBytes n bs => .fixedBytesLit n bs
  | _ => .fixedBytesLit ⟨31, by decide⟩ (List.replicate 32 0)

def vatExpr : Expr := addrLit v.vat

def offsets : List (Ident × List Nat) :=
  [ ("imm_ilk", [1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747]),
    ("imm_vat", [1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936]) ]

def immValues (v : ClipperImmutables) : List (Ident × Value) :=
  [("imm_ilk", v.ilk), ("imm_vat", .address v.vat)]

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : ClipperImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.Dss.Clipper.Immutables
