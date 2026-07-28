import Solm

/-!
# EAS Attester immutable values, offset table, and `runtimeCodeOf`

`runtime.hex` is solc's optimized `--bin-runtime` template for `Attester`: the immutable `_eas`
address is zeroed in the emitted runtime. The constructor patches `_eas` at the offsets below,
re-derived from standard-JSON `evm.deployedBytecode.immutableReferences` for solc `0.8.26`.

Convention: the Solm constructor binds `_eas` as local `imm_eas`; `runtimeCodeOf` reads that local,
converts it to a 32-byte word, and patches the runtime template.
-/

open Solm ABI

namespace Benchmarks.EAS.Attester.Immutables

/-- Attester's constructor-set immutable EAS address. -/
structure AttesterImmutables where
  eas : EVM.Address

/-- An address value as an `Expr` literal. -/
def addrLit (a : EVM.Address) : Expr :=
  .cast (.intLit (Int.ofNat a.toNat)) (.elem .address)

variable (v : AttesterImmutables)

def easExpr : Expr := addrLit v.eas

/-- solc `immutableReferences` offsets, keyed by `imm_eas` (AST id 516 = `_eas`). -/
def offsets : List (Ident × List Nat) :=
  [("imm_eas", [722, 1465, 1598, 1939])]

/-- The immutable value as a `Value` under its constructor-local `imm_eas` key. -/
def immValues (v : AttesterImmutables) : List (Ident × Value) :=
  [("imm_eas", .address v.eas)]

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : AttesterImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

/-- `runtimeCodeOf` for the parameterized constructor relation. -/
def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.EAS.Attester.Immutables
