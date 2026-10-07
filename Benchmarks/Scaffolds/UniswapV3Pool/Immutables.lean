import Solm
import Reasoning.PatchRuntime
import Reasoning.Immutables

/-!
# UniswapV3Pool immutable values and offset table

`runtime.hex` is solc's `--bin-runtime` *template*: every immutable reference is 32 zero bytes.  The
constructor splices the seven immutables in at the offsets solc reports under
`evm.deployedBytecode.immutableReferences` (standard-JSON, solc 0.7.6, `--optimize --optimize-runs
800`, `metadata.bytecodeHash: none`).  Re-derived and verified this session: the emitted template
equals `runtime.hex` byte-for-byte, and the offsets below match solc's output exactly.
-/

open Solm ABI

namespace Benchmarks.UniswapV3Pool.Immutables

/-- solc `immutableReferences` offsets (bytes into the runtime), keyed by immutable name.
    Verified against `evm.deployedBytecode.immutableReferences`. -/
def offsets : List (Ident × List Nat) :=
  [ ("factory",             [8315, 8829, 10457]),
    ("token0",              [2258, 4853, 6740, 7822, 9150, 15650]),
    ("token1",              [4551, 6789, 7924, 9284, 10529, 15979]),
    ("fee",                 [3311, 6603, 6658, 10565]),
    ("tickSpacing",         [3072, 10493, 19402, 19452]),
    ("maxLiquidityPerTick", [8174, 19295, 19350]),
    ("original",            [11259]) ]

/-- The constructor's immutable offsets as a layout for generated runtime summaries. -/
def immutableLayout : Reasoning.Immutables.Layout :=
  ⟨offsets.flatMap fun (key, sites) => sites.map fun off => (off, 32, key)⟩

/-- A `Value`'s 32-byte word (big-endian), as `valueToWord` computes it. -/
def wordBytes? (v : Value) : Option ByteArray :=
  (valueToWord v).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

/-- Build the `(offset, 32-byte word)` patch list by looking each immutable up via `get`. -/
def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let v ← get p.1
    let bytes ← wordBytes? v
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

/-- The runtime code deployed for an immutables store: the template patched with the stored
    values at their `immutableReferences` offsets (the template itself if a value is missing or
    a patch does not fit). -/
def deployedRuntime (template : ByteArray) (imms : Store) : ByteArray :=
  ((patchesFrom (fun n => imms.get? n)).bind (patchRuntime template)).getD template

end Benchmarks.UniswapV3Pool.Immutables
