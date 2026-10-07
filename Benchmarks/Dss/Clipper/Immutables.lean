import Reasoning.SolmBody
import Reasoning.BytecodePatching
import Solm
import Reasoning.Immutables

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
  ilk_wf : ∃ bs, ilk = .fixedBytes ⟨31, by decide⟩ bs ∧ bs.length = 32


variable (v : ClipperImmutables)

def ilkExpr : Expr :=
  match v.ilk with
  | .fixedBytes n bs => .fixedBytesLit n bs
  | _ => .fixedBytesLit ⟨31, by decide⟩ (List.replicate 32 0)

def vatExpr : Expr := Reasoning.Theory.addressLiteral v.vat

def offsets : List (Ident × List Nat) :=
  -- These groups follow the constructor's actual write order. The windows are disjoint, so the
  -- ordering does not change the deployed bytes, but it keeps the proof's write cascade direct.
  [ ("imm_vat", [1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936]),
    ("imm_ilk", [1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747]) ]

/-- The constructor's immutable offsets as a layout for generated runtime summaries. -/
def immutableLayout : Reasoning.Immutables.Layout :=
  ⟨offsets.flatMap fun (key, sites) => sites.map fun off => (off, 32, key)⟩

def immValues (v : ClipperImmutables) : List (Ident × Value) :=
  [("imm_ilk", v.ilk), ("imm_vat", .address v.vat)]


def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← Reasoning.Theory.wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : ClipperImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.Dss.Clipper.Immutables
