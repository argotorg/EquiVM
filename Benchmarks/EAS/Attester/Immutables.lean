import Reasoning.SolmBody
import Reasoning.BytecodePatching
import Solm
import Reasoning.PatchRuntime
import Reasoning.Immutables

/-!
# EAS Attester immutable values and offset table

`runtime.hex` is solc's optimized `--bin-runtime` template for `Attester`: the immutable `_eas`
address is zeroed in the emitted runtime. The constructor patches `_eas` at the offsets below,
re-derived from standard-JSON `evm.deployedBytecode.immutableReferences` for solc `0.8.26`.
-/

open Solm ABI

namespace Benchmarks.EAS.Attester.Immutables

def easExpr : Expr := .immutable "_eas"

/-- solc `immutableReferences` offsets, keyed by immutable name (AST id 516 = `_eas`). -/
def offsets : List (Ident × List Nat) :=
  [("_eas", [824, 1719, 1888, 2289])]

/-- The constructor's immutable offsets as a layout for generated runtime summaries. -/
def immutableLayout : Reasoning.Immutables.Layout :=
  ⟨offsets.flatMap fun (key, sites) => sites.map fun off => (off, 32, key)⟩

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← Reasoning.Theory.wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

/-- The runtime code deployed for an immutables store: the template patched with the stored
    values at their `immutableReferences` offsets (the template itself if a value is missing or
    a patch does not fit). -/
def deployedRuntime (template : ByteArray) (imms : Store) : ByteArray :=
  ((patchesFrom (fun n => imms.get? n)).bind (patchRuntime template)).getD template

end Benchmarks.EAS.Attester.Immutables
