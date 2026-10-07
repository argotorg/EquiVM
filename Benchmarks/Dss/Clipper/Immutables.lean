import Solm
import Reasoning.PatchRuntime
import Reasoning.Immutables

/-!
# MakerDAO/Sky DSS Clipper immutable values and offset table

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
  ilk_wf : ∃ bs, ilk = .fixedBytes ⟨31, by decide⟩ bs ∧ bs.length = 32

/-- The immutable `ilk`, read from the deployed contract's immutables. -/
def ilkExpr : Expr := .immutable "ilk"

/-- The immutable `vat`, read from the deployed contract's immutables. -/
def vatExpr : Expr := .immutable "vat"

/-- The immutables a contract deployed with `v` runs with. -/
def immStore (v : ClipperImmutables) : Store :=
  ((∅ : Store).insert "vat" (.address v.vat)).insert "ilk" v.ilk

@[simp] theorem immStore_get_ilk (v : ClipperImmutables) : (immStore v).get? "ilk" = some v.ilk := by
  simp [immStore]

@[simp] theorem immStore_get_vat (v : ClipperImmutables) :
    (immStore v).get? "vat" = some (.address v.vat) := by
  grind [immStore]

@[simp] theorem evalExpr_ilkExpr {v : ClipperImmutables} {cfg : Config} {C : ContractDecl}
    {L : Store} {evm : EVM.State} :
    evalExpr? cfg { contract := C, locals := L, immutables := immStore v } evm ilkExpr =
      .ok v.ilk := by
  simp only [ilkExpr, evalExpr?, immStore_get_ilk, EvalResult.ofOption]

@[simp] theorem evalExpr_vatExpr {v : ClipperImmutables} {cfg : Config} {C : ContractDecl}
    {L : Store} {evm : EVM.State} :
    evalExpr? cfg { contract := C, locals := L, immutables := immStore v } evm vatExpr =
      .ok (.address v.vat) := by
  simp only [vatExpr, evalExpr?, immStore_get_vat, EvalResult.ofOption]

def offsets : List (Ident × List Nat) :=
  -- These groups follow the constructor's actual write order. The windows are disjoint, so the
  -- ordering does not change the deployed bytes, but it keeps the proof's write cascade direct.
  [ ("vat", [1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936]),
    ("ilk", [1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747]) ]

/-- The constructor's immutable offsets as a layout for generated runtime summaries. -/
def immutableLayout : Reasoning.Immutables.Layout :=
  ⟨offsets.flatMap fun (key, sites) => sites.map fun off => (off, 32, key)⟩

def immValues (v : ClipperImmutables) : List (Ident × Value) :=
  [("ilk", v.ilk), ("vat", .address v.vat)]

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : ClipperImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

end Benchmarks.Dss.Clipper.Immutables
