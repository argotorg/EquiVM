import Reasoning.SolmBody
import Reasoning.BytecodePatching
import Solm

/-!
# TinyImmutable immutable valuation and offset table

This is the smallest UniswapV3-style immutable example in `Examples`: solc emits the deployed
runtime as a template with 32 zero bytes at every immutable reference, and the constructor patches
those words before returning the runtime.

The offsets below are from solc `0.8.35` standard JSON
`evm.deployedBytecode.immutableReferences` for `TinyImmutable.sol`, optimizer enabled with
800 runs, EVM version Shanghai, and `metadata.bytecodeHash: none`.
-/

open Solm ABI

namespace TinyImmutable.Immutables

/-- A valuation of the tiny example's immutables, as the runtime proofs consume them. -/
structure TinyImmutables where
  owner : EVM.Address
  scale : EVM.Word

/-- solc `immutableReferences`: each immutable's Solm name and patch offsets, in the order the
    constructor writes them. -/
def immutableReferences : List (Ident × List Nat) :=
  [ ("scale", [186, 361]),
    ("owner", [72, 245]) ]

end TinyImmutable.Immutables
