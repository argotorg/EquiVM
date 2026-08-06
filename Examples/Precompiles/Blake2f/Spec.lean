import Examples.Precompiles.Blake2f.Bytecode
import Examples.Precompiles.Blake2f.Model
import Reasoning.Bytecode

/-!
# BLAKE2F precompile bytecode-spec experiment

This is the Solm-independent proof target for a deployed BLAKE2F replacement.  The intended theorem
is a `PrecompileSpec`: valid EIP-152 inputs return the pure Lean `compressBytes` output with the
replacement bytecode's exact gas expression; invalid EIP-152 inputs collapse to the common
caller-visible failure result.

The native precompile charges `rounds`; the deployed bytecode will not.  Therefore
`bytecodeGasCost` is deliberately separate from `Model.nativeGasCost`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

/-- Calls in scope for the replacement contract proof.

The Solidity fallback is non-payable, so the precompile-style experiment currently scopes the
bytecode proof to value-free calls. -/
def accepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < UInt256.size

/-- Valid EIP-152 BLAKE2F inputs: exactly 213 bytes and final flag exactly 0 or 1. -/
def valid (ctx : BytecodeContext) : Prop :=
  Model.validInput ctx.executionEnv.calldata

/-- Pure output required from the replacement on valid inputs. -/
def output (ctx : BytecodeContext) : ByteArray :=
  Model.output ctx.executionEnv.calldata

/-- Intended final proof shape for the BLAKE2F experiment.

`gasCost` is bytecode-specific. It is intentionally a parameter here because the native precompile
cost is just `rounds`, while the deployed Solidity replacement has its own instruction-level gas
expression. -/
abbrev bytecodeSpecTarget (gasCost : BytecodeContext → Nat) : Prop :=
  PrecompileSpec runtimeBytecode accepts valid output gasCost

end Blake2f
