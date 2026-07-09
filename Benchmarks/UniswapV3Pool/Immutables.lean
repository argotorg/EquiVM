import Solm

/-!
# UniswapV3Pool immutable values, offset table, and `runtimeCodeOf`

`runtime.hex` is solc's `--bin-runtime` *template*: every immutable reference is 32 zero bytes.  The
constructor splices the seven immutables in at the offsets solc reports under
`evm.deployedBytecode.immutableReferences` (standard-JSON, solc 0.7.6, `--optimize --optimize-runs
800`, `metadata.bytecodeHash: none`).  Re-derived and verified this session: the emitted template
equals `runtime.hex` byte-for-byte, and the offsets below match solc's output exactly.

Convention: the spec constructor binds each immutable as a local `imm_<name>`; `runtimeCodeOf` reads
those locals, `valueToWord`s each, and `patchRuntime`s the template with the offset table.
-/

open Solm ABI

namespace Benchmarks.UniswapV3Pool.Immutables

/-- The pool's seven constructor-set immutables. -/
structure PoolImmutables where
  factory : EVM.Address
  token0 : EVM.Address
  token1 : EVM.Address
  fee : Int
  fee_nonneg : 0 ≤ fee
  fee_lt : fee < 2 ^ 24
  tickSpacing : Int
  tickSpacing_ge : -(2 ^ 23) ≤ tickSpacing
  tickSpacing_lt : tickSpacing < 2 ^ 23
  maxLiquidityPerTick : Int
  maxLiquidityPerTick_nonneg : 0 ≤ maxLiquidityPerTick
  maxLiquidityPerTick_lt : maxLiquidityPerTick < 2 ^ 128
  original : EVM.Address

/-- solc `immutableReferences` offsets (bytes into the runtime), keyed by the `imm_<name>` local.
    Verified against `evm.deployedBytecode.immutableReferences`. -/
def offsets : List (Ident × List Nat) :=
  [ ("imm_factory",             [8315, 8829, 10457]),
    ("imm_token0",              [2258, 4853, 6740, 7822, 9150, 15650]),
    ("imm_token1",              [4551, 6789, 7924, 9284, 10529, 15979]),
    ("imm_fee",                 [3311, 6603, 6658, 10565]),
    ("imm_tickSpacing",         [3072, 10493, 19402, 19452]),
    ("imm_maxLiquidityPerTick", [8174, 19295, 19350]),
    ("imm_original",            [11259]) ]

/-- The immutable values as Solm `Value`s under their `imm_<name>` keys. -/
def immValues (v : PoolImmutables) : List (Ident × Value) :=
  [ ("imm_factory",             .address v.factory),
    ("imm_token0",              .address v.token0),
    ("imm_token1",              .address v.token1),
    ("imm_fee",                 .int v.fee),
    ("imm_tickSpacing",         .int v.tickSpacing),
    ("imm_maxLiquidityPerTick", .int v.maxLiquidityPerTick),
    ("imm_original",            .address v.original) ]

/-- A `Value`'s 32-byte word (big-endian), as `valueToWord` computes it. -/
def wordBytes? (v : Value) : Option ByteArray :=
  (valueToWord v).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

/-- Build the `(offset, 32-byte word)` patch list by looking each `imm_<name>` up via `get`. -/
def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let v ← get p.1
    let bytes ← wordBytes? v
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

/-- The patch list for a concrete immutable assignment (used at the per-value theorem site). -/
def patches (v : PoolImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

/-- `runtimeCodeOf` for the parameterized constructor relation: reads the constructor's final
    `imm_<name>` locals, and patches the template.  `none` if a local is missing/ill-typed. -/
def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.UniswapV3Pool.Immutables
