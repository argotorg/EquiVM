import Examples.Precompiles.Ripemd160.HashWideTrace

/-!
# RIPEMD-160 bytecode correctness

This is the entry point for the precompile-style proof. `ripemd160BytecodeSpec` is stated directly
using the generic `Reasoning.Reach.BytecodeSpec` interface. It relates the deployed bytecode to the
pure Lean RIPEMD-160 model and gives the exact successful gas charge and OOG threshold. It has no
dependency on the contract's Solm specification or its equivalence proof.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Ripemd160

/-- Calls covered by the bytecode specification. -/
def ripemd160BytecodeAccepts (ctx : BytecodeContext) : Prop :=
  ripemd160Accepts ctx.executionEnv

/-- Caller-visible functional and exact-gas behavior of the RIPEMD-160 bytecode. -/
def ripemd160BytecodeEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx
    (Model.rawOutput ctx.executionEnv.calldata)
    (ripemd160GasCost ctx.executionEnv)
    result

/-- Final precompile-style result: the bytecode implements the pure RIPEMD-160 function and its
exact gas term at the caller-visible `Θ` boundary. -/
theorem ripemd160BytecodeSpec :
    BytecodeSpec ripemd160RuntimeBytecode
      ripemd160BytecodeAccepts ripemd160BytecodeEnsures := by
  simpa [ripemd160BytecodeAccepts, ripemd160BytecodeEnsures]
    using ripemd160BytecodeExactGas

end Ripemd160
