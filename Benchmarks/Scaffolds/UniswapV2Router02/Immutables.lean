import Solm

/-!
# UniswapV2Router02 immutable values, offset table, and `runtimeCodeOf`

`runtime.hex` is solc's `--optimize --optimize-runs 999999 --metadata-hash none` runtime
*template* for the upstream `UniswapV2Router02` contract at Solidity `=0.6.6`: both immutable
address slots are zeroed in the emitted runtime.  The constructor patches `factory` and `WETH` at
the offsets below, re-derived from standard-JSON `evm.deployedBytecode.immutableReferences`.

Convention: the Solm constructor binds each immutable as a local `imm_<name>`; `runtimeCodeOf`
reads those locals, converts them to 32-byte words, and patches the runtime template.
-/

open Solm ABI

namespace Benchmarks.UniswapV2Router02.Immutables

/-- Router02's two constructor-set immutables. -/
structure RouterImmutables where
  factory : EVM.Address
  WETH : EVM.Address

/-- An address value as an `Expr` literal. -/
def addrLit (a : EVM.Address) : Expr :=
  .cast (.intLit (Int.ofNat a.toNat)) (.elem .address)

variable (v : RouterImmutables)

def factory : Expr := addrLit v.factory
def WETH : Expr := addrLit v.WETH

/-- solc `immutableReferences` offsets, keyed by `imm_<name>` (verified against the AST ids). -/
def offsets : List (Ident × List Nat) :=
  [ ("imm_factory",
      [4295, 4549, 4971, 5028, 5455, 6116, 6324, 6817, 8799, 9216, 9641, 10908,
       11743, 12401, 12442, 12490, 12967, 13398, 14381, 14795, 17460, 17527,
       18391, 18872, 20275, 20500, 20628]),
    ("imm_WETH",
      [428, 3677, 3736, 4053, 4760, 5874, 6358, 7710, 8098, 8306, 8569, 9004,
       9153, 9843, 10010, 10223, 10484, 10716, 10845, 12524, 13346, 13432,
       13484, 13613, 14151, 14583, 14732]) ]

/-- The immutable values as `Value`s under their `imm_<name>` keys. -/
def immValues (v : RouterImmutables) : List (Ident × Value) :=
  [ ("imm_factory", .address v.factory),
    ("imm_WETH", .address v.WETH) ]

def wordBytes? (x : Value) : Option ByteArray :=
  (valueToWord x).map (fun w => ByteArray.mk (EVM.Word.toBytesBE w).toArray)

def patchesFrom (get : Ident → Option Value) : Option (List (Nat × ByteArray)) :=
  offsets.foldrM (fun p acc => do
    let x ← get p.1
    let bytes ← wordBytes? x
    pure (p.2.map (fun o => (o, bytes)) ++ acc)) []

def patches (v : RouterImmutables) : List (Nat × ByteArray) :=
  (patchesFrom (fun n => (immValues v).lookup n)).getD []

/-- `runtimeCodeOf` for the parameterized constructor relation. -/
def runtimeCodeOf (template : ByteArray) (locals : Store) : Option ByteArray := do
  let ps ← patchesFrom (fun n => locals.get? n)
  patchRuntime template ps

end Benchmarks.UniswapV2Router02.Immutables
