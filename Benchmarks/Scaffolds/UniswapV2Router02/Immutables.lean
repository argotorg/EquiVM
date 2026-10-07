import Reasoning.SolmBody
import Reasoning.BytecodePatching
import Solm
import Reasoning.PatchRuntime
import Reasoning.Immutables

/-!
# UniswapV2Router02 immutable values and offset table

`runtime.hex` is solc's `--optimize --optimize-runs 999999 --metadata-hash none` runtime
*template* for the upstream `UniswapV2Router02` contract at Solidity `=0.6.6`: both immutable
address slots are zeroed in the emitted runtime.  The constructor patches `factory` and `WETH` at
the offsets below, re-derived from standard-JSON `evm.deployedBytecode.immutableReferences`.
-/

open Solm ABI

namespace Benchmarks.UniswapV2Router02.Immutables

def factory : Expr := .immutable "factory"
def WETH : Expr := .immutable "WETH"

/-- solc `immutableReferences` offsets, keyed by immutable name (verified against the AST ids). -/
def offsets : List (Ident × List Nat) :=
  [ ("factory",
      [4295, 4549, 4971, 5028, 5455, 6116, 6324, 6817, 8799, 9216, 9641, 10908,
       11743, 12401, 12442, 12490, 12967, 13398, 14381, 14795, 17460, 17527,
       18391, 18872, 20275, 20500, 20628]),
    ("WETH",
      [428, 3677, 3736, 4053, 4760, 5874, 6358, 7710, 8098, 8306, 8569, 9004,
       9153, 9843, 10010, 10223, 10484, 10716, 10845, 12524, 13346, 13432,
       13484, 13613, 14151, 14583, 14732]) ]

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

end Benchmarks.UniswapV2Router02.Immutables
